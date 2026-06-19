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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
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
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5;
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1;
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__3_value;
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
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
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
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v___x_429_; lean_object* v_toEnvExtension_430_; lean_object* v_asyncMode_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_merged_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v___x_427_ = lean_st_ref_get(v___y_425_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_env_428_);
lean_dec(v___x_427_);
v___x_429_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_430_ = lean_ctor_get(v___x_429_, 0);
v_asyncMode_431_ = lean_ctor_get(v_toEnvExtension_430_, 2);
v___x_432_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_432_, v___x_429_, v_env_428_, v_asyncMode_431_, v___x_433_);
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
lean_object* v___x_452_; lean_object* v_scopes_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_opts_456_; lean_object* v___x_457_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_scopes_453_ = lean_ctor_get(v___x_452_, 2);
lean_inc(v_scopes_453_);
lean_dec(v___x_452_);
v___x_454_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_455_ = l_List_head_x21___redArg(v___x_454_, v_scopes_453_);
lean_dec(v_scopes_453_);
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
v___x_515_ = lean_st_ref_set(v___x_512_, v___x_514_);
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
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 5, v___x_540_);
lean_ctor_set(v___x_538_, 0, v_env_526_);
v___x_542_ = v___x_538_;
goto v_reusejp_541_;
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
lean_ctor_set(v_reuseFailAlloc_546_, 5, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_messages_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_infoState_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_snapshotTasks_536_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_st_ref_set(v___y_527_, v___x_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
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
lean_object* v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_564_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
lean_ctor_set(v___x_569_, 4, v___x_567_);
lean_ctor_set(v___x_569_, 5, v___x_567_);
lean_ctor_set(v___x_569_, 6, v___x_567_);
lean_ctor_set(v___x_569_, 7, v___x_567_);
lean_ctor_set(v___x_569_, 8, v___x_567_);
lean_ctor_set(v___x_569_, 9, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(32u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_573_ = ((size_t)5ULL);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_unsigned_to_nat(32u);
v___x_576_ = lean_mk_empty_array_with_capacity(v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_578_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_574_);
lean_ctor_set(v___x_578_, 3, v___x_574_);
lean_ctor_set_usize(v___x_578_, 4, v___x_573_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_box(1);
v___x_580_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_581_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
lean_ctor_set(v___x_582_, 2, v___x_579_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v_env_588_; lean_object* v_options_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_587_ = lean_st_ref_get(v___y_585_);
v_env_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_588_);
lean_dec(v___x_587_);
v_options_589_ = lean_ctor_get(v___y_584_, 2);
v___x_590_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_591_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_589_);
v___x_592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_592_, 0, v_env_588_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_ctor_set(v___x_592_, 3, v_options_589_);
v___x_593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_msgData_583_);
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
v_ref_604_ = lean_ctor_get(v___y_601_, 5);
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
lean_object* v_fileName_648_; lean_object* v_fileMap_649_; lean_object* v_options_650_; lean_object* v_currRecDepth_651_; lean_object* v_maxRecDepth_652_; lean_object* v_ref_653_; lean_object* v_currNamespace_654_; lean_object* v_openDecls_655_; lean_object* v_initHeartbeats_656_; lean_object* v_maxHeartbeats_657_; lean_object* v_quotContext_658_; lean_object* v_currMacroScope_659_; uint8_t v_diag_660_; lean_object* v_cancelTk_x3f_661_; uint8_t v_suppressElabErrors_662_; lean_object* v_inheritedTraceOptions_663_; lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_fileName_648_ = lean_ctor_get(v___y_645_, 0);
v_fileMap_649_ = lean_ctor_get(v___y_645_, 1);
v_options_650_ = lean_ctor_get(v___y_645_, 2);
v_currRecDepth_651_ = lean_ctor_get(v___y_645_, 3);
v_maxRecDepth_652_ = lean_ctor_get(v___y_645_, 4);
v_ref_653_ = lean_ctor_get(v___y_645_, 5);
v_currNamespace_654_ = lean_ctor_get(v___y_645_, 6);
v_openDecls_655_ = lean_ctor_get(v___y_645_, 7);
v_initHeartbeats_656_ = lean_ctor_get(v___y_645_, 8);
v_maxHeartbeats_657_ = lean_ctor_get(v___y_645_, 9);
v_quotContext_658_ = lean_ctor_get(v___y_645_, 10);
v_currMacroScope_659_ = lean_ctor_get(v___y_645_, 11);
v_diag_660_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*14);
v_cancelTk_x3f_661_ = lean_ctor_get(v___y_645_, 12);
v_suppressElabErrors_662_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_663_ = lean_ctor_get(v___y_645_, 13);
v_ref_664_ = l_Lean_replaceRef(v_ref_643_, v_ref_653_);
lean_inc_ref(v_inheritedTraceOptions_663_);
lean_inc(v_cancelTk_x3f_661_);
lean_inc(v_currMacroScope_659_);
lean_inc(v_quotContext_658_);
lean_inc(v_maxHeartbeats_657_);
lean_inc(v_initHeartbeats_656_);
lean_inc(v_openDecls_655_);
lean_inc(v_currNamespace_654_);
lean_inc(v_maxRecDepth_652_);
lean_inc(v_currRecDepth_651_);
lean_inc_ref(v_options_650_);
lean_inc_ref(v_fileMap_649_);
lean_inc_ref(v_fileName_648_);
v___x_665_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_665_, 0, v_fileName_648_);
lean_ctor_set(v___x_665_, 1, v_fileMap_649_);
lean_ctor_set(v___x_665_, 2, v_options_650_);
lean_ctor_set(v___x_665_, 3, v_currRecDepth_651_);
lean_ctor_set(v___x_665_, 4, v_maxRecDepth_652_);
lean_ctor_set(v___x_665_, 5, v_ref_664_);
lean_ctor_set(v___x_665_, 6, v_currNamespace_654_);
lean_ctor_set(v___x_665_, 7, v_openDecls_655_);
lean_ctor_set(v___x_665_, 8, v_initHeartbeats_656_);
lean_ctor_set(v___x_665_, 9, v_maxHeartbeats_657_);
lean_ctor_set(v___x_665_, 10, v_quotContext_658_);
lean_ctor_set(v___x_665_, 11, v_currMacroScope_659_);
lean_ctor_set(v___x_665_, 12, v_cancelTk_x3f_661_);
lean_ctor_set(v___x_665_, 13, v_inheritedTraceOptions_663_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*14, v_diag_660_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*14 + 1, v_suppressElabErrors_662_);
v___x_666_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_644_, v___x_665_, v___y_646_);
lean_dec_ref_known(v___x_665_, 14);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_ref_667_, lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_667_, v_msg_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_ref_667_);
return v_res_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(lean_object* v_msg_694_, lean_object* v_declHint_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v_env_699_; uint8_t v___x_700_; 
v___x_698_ = lean_st_ref_get(v___y_696_);
v_env_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_env_699_);
lean_dec(v___x_698_);
v___x_700_ = l_Lean_Name_isAnonymous(v_declHint_695_);
if (v___x_700_ == 0)
{
uint8_t v_isExporting_701_; 
v_isExporting_701_ = lean_ctor_get_uint8(v_env_699_, sizeof(void*)*8);
if (v_isExporting_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec_ref(v_env_699_);
lean_dec(v_declHint_695_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v_msg_694_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
lean_inc_ref(v_env_699_);
v___x_703_ = l_Lean_Environment_setExporting(v_env_699_, v___x_700_);
lean_inc(v_declHint_695_);
lean_inc_ref(v___x_703_);
v___x_704_ = l_Lean_Environment_contains(v___x_703_, v_declHint_695_, v_isExporting_701_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v___x_703_);
lean_dec_ref(v_env_699_);
lean_dec(v_declHint_695_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_msg_694_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_c_711_; lean_object* v___x_712_; 
v___x_706_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_707_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_708_ = l_Lean_Options_empty;
v___x_709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_709_, 0, v___x_703_);
lean_ctor_set(v___x_709_, 1, v___x_706_);
lean_ctor_set(v___x_709_, 2, v___x_707_);
lean_ctor_set(v___x_709_, 3, v___x_708_);
lean_inc(v_declHint_695_);
v___x_710_ = l_Lean_MessageData_ofConstName(v_declHint_695_, v___x_700_);
v_c_711_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_711_, 0, v___x_709_);
lean_ctor_set(v_c_711_, 1, v___x_710_);
v___x_712_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_699_, v_declHint_695_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_env_699_);
lean_dec(v_declHint_695_);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_c_711_);
v___x_715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_MessageData_note(v___x_716_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v_msg_694_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_755_; 
v_val_720_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_755_ == 0)
{
v___x_722_ = v___x_712_;
v_isShared_723_ = v_isSharedCheck_755_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v___x_712_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_755_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_mod_727_; uint8_t v___x_728_; 
v___x_724_ = lean_box(0);
v___x_725_ = l_Lean_Environment_header(v_env_699_);
lean_dec_ref(v_env_699_);
v___x_726_ = l_Lean_EnvironmentHeader_moduleNames(v___x_725_);
v_mod_727_ = lean_array_get(v___x_724_, v___x_726_, v_val_720_);
lean_dec(v_val_720_);
lean_dec_ref(v___x_726_);
v___x_728_ = l_Lean_isPrivateName(v_declHint_695_);
lean_dec(v_declHint_695_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_c_711_);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = l_Lean_MessageData_ofName(v_mod_727_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_MessageData_note(v___x_736_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v_msg_694_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v___x_738_);
v___x_740_ = v___x_722_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_c_711_);
v___x_744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_MessageData_ofName(v_mod_727_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_MessageData_note(v___x_749_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v_msg_694_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v___x_751_);
v___x_753_ = v___x_722_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_756_; 
lean_dec_ref(v_env_699_);
lean_dec(v_declHint_695_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_msg_694_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_msg_757_, lean_object* v_declHint_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_757_, v_declHint_758_, v___y_759_);
lean_dec(v___y_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(lean_object* v_msg_762_, lean_object* v_declHint_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v___x_767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_762_, v_declHint_763_, v___y_765_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_777_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = l_Lean_unknownIdentifierMessageTag;
v___x_773_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_a_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_msg_778_, lean_object* v_declHint_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_778_, v_declHint_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_ref_784_, lean_object* v_msg_785_, lean_object* v_declHint_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_792_; 
v___x_790_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_785_, v_declHint_786_, v___y_787_, v___y_788_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref(v___x_790_);
v___x_792_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_784_, v_a_791_, v___y_787_, v___y_788_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_ref_793_, lean_object* v_msg_794_, lean_object* v_declHint_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_793_, v_msg_794_, v_declHint_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v_ref_793_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_ref_804_, lean_object* v_constName_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_809_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0);
v___x_810_ = 0;
lean_inc(v_constName_805_);
v___x_811_ = l_Lean_MessageData_ofConstName(v_constName_805_, v___x_810_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_809_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_804_, v___x_814_, v_constName_805_, v___y_806_, v___y_807_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_816_, lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_816_, v_constName_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v_ref_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_ref_826_; lean_object* v___x_827_; 
v_ref_826_ = lean_ctor_get(v___y_823_, 5);
v___x_827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_826_, v_constName_822_, v___y_823_, v___y_824_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_constName_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(lean_object* v_constName_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_837_ = lean_st_ref_get(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = 0;
lean_inc(v_constName_833_);
v___x_840_ = l_Lean_Environment_find_x3f(v_env_838_, v_constName_833_, v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_833_, v___y_834_, v___y_835_);
return v___x_841_;
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_constName_833_);
v_val_842_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 0);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_val_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_constName_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_constName_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(lean_object* v_attrName_864_, lean_object* v_declName_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_869_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_870_ = l_Lean_MessageData_ofName(v_attrName_864_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = 0;
v___x_875_ = l_Lean_MessageData_ofConstName(v_declName_865_, v___x_874_);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_873_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_878_, v___y_866_, v___y_867_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_attrName_880_, lean_object* v_declName_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_880_, v_declName_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_885_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(lean_object* v_name_895_, uint8_t v_kind_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___y_906_; 
v___x_900_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1);
v___x_901_ = l_Lean_MessageData_ofName(v_name_895_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
switch(v_kind_896_)
{
case 0:
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4));
v___y_906_ = v___x_913_;
goto v___jp_905_;
}
case 1:
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5));
v___y_906_ = v___x_914_;
goto v___jp_905_;
}
default: 
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6));
v___y_906_ = v___x_915_;
goto v___jp_905_;
}
}
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc_ref(v___y_906_);
v___x_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_907_, 0, v___y_906_);
v___x_908_ = l_Lean_MessageData_ofFormat(v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_904_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_911_, v___y_897_, v___y_898_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_name_916_, lean_object* v_kind_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
uint8_t v_kind_boxed_921_; lean_object* v_res_922_; 
v_kind_boxed_921_ = lean_unbox(v_kind_917_);
v_res_922_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_916_, v_kind_boxed_921_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_922_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(lean_object* v_keys_923_, lean_object* v_i_924_, lean_object* v_k_925_){
_start:
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_array_get_size(v_keys_923_);
v___x_927_ = lean_nat_dec_lt(v_i_924_, v___x_926_);
if (v___x_927_ == 0)
{
lean_dec(v_i_924_);
return v___x_927_;
}
else
{
lean_object* v_k_x27_928_; uint8_t v___x_929_; 
v_k_x27_928_ = lean_array_fget_borrowed(v_keys_923_, v_i_924_);
v___x_929_ = l_Lean_instBEqExtraModUse_beq(v_k_925_, v_k_x27_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_add(v_i_924_, v___x_930_);
lean_dec(v_i_924_);
v_i_924_ = v___x_931_;
goto _start;
}
else
{
lean_dec(v_i_924_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg___boxed(lean_object* v_keys_933_, lean_object* v_i_934_, lean_object* v_k_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_933_, v_i_934_, v_k_935_);
lean_dec_ref(v_k_935_);
lean_dec_ref(v_keys_933_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; 
v___x_938_ = ((size_t)5ULL);
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_shift_left(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; 
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__0);
v___x_943_ = lean_usize_sub(v___x_942_, v___x_941_);
return v___x_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(lean_object* v_x_944_, size_t v_x_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
lean_object* v_es_947_; lean_object* v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v_j_952_; lean_object* v___x_953_; 
v_es_947_ = lean_ctor_get(v_x_944_, 0);
v___x_948_ = lean_box(2);
v___x_949_ = ((size_t)5ULL);
v___x_950_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___closed__1);
v___x_951_ = lean_usize_land(v_x_945_, v___x_950_);
v_j_952_ = lean_usize_to_nat(v___x_951_);
v___x_953_ = lean_array_get_borrowed(v___x_948_, v_es_947_, v_j_952_);
lean_dec(v_j_952_);
switch(lean_obj_tag(v___x_953_))
{
case 0:
{
lean_object* v_key_954_; uint8_t v___x_955_; 
v_key_954_ = lean_ctor_get(v___x_953_, 0);
v___x_955_ = l_Lean_instBEqExtraModUse_beq(v_x_946_, v_key_954_);
return v___x_955_;
}
case 1:
{
lean_object* v_node_956_; size_t v___x_957_; 
v_node_956_ = lean_ctor_get(v___x_953_, 0);
v___x_957_ = lean_usize_shift_right(v_x_945_, v___x_949_);
v_x_944_ = v_node_956_;
v_x_945_ = v___x_957_;
goto _start;
}
default: 
{
uint8_t v___x_959_; 
v___x_959_ = 0;
return v___x_959_;
}
}
}
else
{
lean_object* v_ks_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_ks_960_ = lean_ctor_get(v_x_944_, 0);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_ks_960_, v___x_961_, v_x_946_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
size_t v_x_9314__boxed_966_; uint8_t v_res_967_; lean_object* v_r_968_; 
v_x_9314__boxed_966_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_967_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_963_, v_x_9314__boxed_966_, v_x_965_);
lean_dec_ref(v_x_965_);
lean_dec_ref(v_x_963_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
uint64_t v___x_971_; size_t v___x_972_; uint8_t v___x_973_; 
v___x_971_ = l_Lean_instHashableExtraModUse_hash(v_x_970_);
v___x_972_ = lean_uint64_to_usize(v___x_971_);
v___x_973_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_969_, v___x_972_, v_x_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_974_, v_x_975_);
lean_dec_ref(v_x_975_);
lean_dec_ref(v_x_974_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_978_; double v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_float_of_nat(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_cls_983_, lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_ref_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1034_; 
v_ref_988_ = lean_ctor_get(v___y_985_, 5);
v___x_989_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_984_, v___y_985_, v___y_986_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1034_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1034_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v_traceState_995_; lean_object* v_env_996_; lean_object* v_nextMacroScope_997_; lean_object* v_ngen_998_; lean_object* v_auxDeclNGen_999_; lean_object* v_cache_1000_; lean_object* v_messages_1001_; lean_object* v_infoState_1002_; lean_object* v_snapshotTasks_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1033_; 
v___x_994_ = lean_st_ref_take(v___y_986_);
v_traceState_995_ = lean_ctor_get(v___x_994_, 4);
v_env_996_ = lean_ctor_get(v___x_994_, 0);
v_nextMacroScope_997_ = lean_ctor_get(v___x_994_, 1);
v_ngen_998_ = lean_ctor_get(v___x_994_, 2);
v_auxDeclNGen_999_ = lean_ctor_get(v___x_994_, 3);
v_cache_1000_ = lean_ctor_get(v___x_994_, 5);
v_messages_1001_ = lean_ctor_get(v___x_994_, 6);
v_infoState_1002_ = lean_ctor_get(v___x_994_, 7);
v_snapshotTasks_1003_ = lean_ctor_get(v___x_994_, 8);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1005_ = v___x_994_;
v_isShared_1006_ = v_isSharedCheck_1033_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_snapshotTasks_1003_);
lean_inc(v_infoState_1002_);
lean_inc(v_messages_1001_);
lean_inc(v_cache_1000_);
lean_inc(v_traceState_995_);
lean_inc(v_auxDeclNGen_999_);
lean_inc(v_ngen_998_);
lean_inc(v_nextMacroScope_997_);
lean_inc(v_env_996_);
lean_dec(v___x_994_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1033_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint64_t v_tid_1007_; lean_object* v_traces_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1032_; 
v_tid_1007_ = lean_ctor_get_uint64(v_traceState_995_, sizeof(void*)*1);
v_traces_1008_ = lean_ctor_get(v_traceState_995_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_traceState_995_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1010_ = v_traceState_995_;
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_traces_1008_);
lean_dec(v_traceState_995_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; double v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0);
v___x_1014_ = 0;
v___x_1015_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1016_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1016_, 0, v_cls_983_);
lean_ctor_set(v___x_1016_, 1, v___x_1012_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set_float(v___x_1016_, sizeof(void*)*3, v___x_1013_);
lean_ctor_set_float(v___x_1016_, sizeof(void*)*3 + 8, v___x_1013_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*3 + 16, v___x_1014_);
v___x_1017_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2));
v___x_1018_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v_a_990_);
lean_ctor_set(v___x_1018_, 2, v___x_1017_);
lean_inc(v_ref_988_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_ref_988_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_PersistentArray_push___redArg(v_traces_1008_, v___x_1019_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1020_);
v___x_1022_ = v___x_1010_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1020_);
lean_ctor_set_uint64(v_reuseFailAlloc_1031_, sizeof(void*)*1, v_tid_1007_);
v___x_1022_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___x_1022_);
v___x_1024_ = v___x_1005_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_env_996_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_nextMacroScope_997_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_ngen_998_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_auxDeclNGen_999_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1030_, 5, v_cache_1000_);
lean_ctor_set(v_reuseFailAlloc_1030_, 6, v_messages_1001_);
lean_ctor_set(v_reuseFailAlloc_1030_, 7, v_infoState_1002_);
lean_ctor_set(v_reuseFailAlloc_1030_, 8, v_snapshotTasks_1003_);
v___x_1024_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1025_ = lean_st_ref_set(v___y_986_, v___x_1024_);
v___x_1026_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1026_);
v___x_1028_ = v___x_992_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_cls_1035_, lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1035_, v_msg_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1));
v___x_1044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0));
v___x_1045_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_cls_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4));
v___x_1061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_1062_ = l_Lean_Name_append(v___x_1061_, v_cls_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_mod_1073_, uint8_t v_isMeta_1074_, lean_object* v_hint_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_env_1080_; uint8_t v_isExporting_1081_; lean_object* v___x_1082_; lean_object* v_env_1083_; lean_object* v___x_1084_; lean_object* v_entry_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___y_1090_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1079_ = lean_st_ref_get(v___y_1077_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1080_);
lean_dec(v___x_1079_);
v_isExporting_1081_ = lean_ctor_get_uint8(v_env_1080_, sizeof(void*)*8);
lean_dec_ref(v_env_1080_);
v___x_1082_ = lean_st_ref_get(v___y_1077_);
v_env_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2);
lean_inc(v_mod_1073_);
v_entry_1085_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1085_, 0, v_mod_1073_);
lean_ctor_set_uint8(v_entry_1085_, sizeof(void*)*1, v_isExporting_1081_);
lean_ctor_set_uint8(v_entry_1085_, sizeof(void*)*1 + 1, v_isMeta_1074_);
v___x_1086_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1087_ = lean_box(1);
v___x_1088_ = lean_box(0);
v___x_1115_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1084_, v___x_1086_, v_env_1083_, v___x_1087_, v___x_1088_);
v___x_1116_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_1115_, v_entry_1085_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v_options_1117_; uint8_t v_hasTrace_1118_; 
v_options_1117_ = lean_ctor_get(v___y_1076_, 2);
v_hasTrace_1118_ = lean_ctor_get_uint8(v_options_1117_, sizeof(void*)*1);
if (v_hasTrace_1118_ == 0)
{
lean_dec(v_hint_1075_);
lean_dec(v_mod_1073_);
v___y_1090_ = v___y_1077_;
goto v___jp_1089_;
}
else
{
lean_object* v_inheritedTraceOptions_1119_; lean_object* v_cls_1120_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_inheritedTraceOptions_1119_ = lean_ctor_get(v___y_1076_, 13);
v_cls_1120_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4));
v___x_1140_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12);
v___x_1141_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1119_, v_options_1117_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_dec(v_hint_1075_);
lean_dec(v_mod_1073_);
v___y_1090_ = v___y_1077_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1142_; lean_object* v___y_1144_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14);
if (v_isExporting_1081_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19));
v___y_1144_ = v___x_1151_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20));
v___y_1144_ = v___x_1152_;
goto v___jp_1143_;
}
v___jp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref(v___y_1144_);
v___x_1145_ = l_Lean_stringToMessageData(v___y_1144_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1142_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
if (v_isMeta_1074_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17));
v___y_1127_ = v___x_1148_;
v___y_1128_ = v___x_1149_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18));
v___y_1127_ = v___x_1148_;
v___y_1128_ = v___x_1150_;
goto v___jp_1126_;
}
}
}
v___jp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___y_1122_);
lean_ctor_set(v___x_1124_, 1, v___y_1123_);
v___x_1125_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1120_, v___x_1124_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec_ref_known(v___x_1125_, 1);
v___y_1090_ = v___y_1077_;
goto v___jp_1089_;
}
else
{
lean_dec_ref_known(v_entry_1085_, 1);
return v___x_1125_;
}
}
v___jp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
lean_inc_ref(v___y_1128_);
v___x_1129_ = l_Lean_stringToMessageData(v___y_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___y_1127_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_MessageData_ofName(v_mod_1073_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_Name_isAnonymous(v_hint_1075_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8);
v___x_1137_ = l_Lean_MessageData_ofName(v_hint_1075_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___y_1122_ = v___x_1134_;
v___y_1123_ = v___x_1138_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_hint_1075_);
v___x_1139_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9);
v___y_1122_ = v___x_1134_;
v___y_1123_ = v___x_1139_;
goto v___jp_1121_;
}
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref_known(v_entry_1085_, 1);
lean_dec(v_hint_1075_);
lean_dec(v_mod_1073_);
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v_toEnvExtension_1092_; lean_object* v_env_1093_; lean_object* v_nextMacroScope_1094_; lean_object* v_ngen_1095_; lean_object* v_auxDeclNGen_1096_; lean_object* v_traceState_1097_; lean_object* v_messages_1098_; lean_object* v_infoState_1099_; lean_object* v_snapshotTasks_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1113_; 
v___x_1091_ = lean_st_ref_take(v___y_1090_);
v_toEnvExtension_1092_ = lean_ctor_get(v___x_1086_, 0);
v_env_1093_ = lean_ctor_get(v___x_1091_, 0);
v_nextMacroScope_1094_ = lean_ctor_get(v___x_1091_, 1);
v_ngen_1095_ = lean_ctor_get(v___x_1091_, 2);
v_auxDeclNGen_1096_ = lean_ctor_get(v___x_1091_, 3);
v_traceState_1097_ = lean_ctor_get(v___x_1091_, 4);
v_messages_1098_ = lean_ctor_get(v___x_1091_, 6);
v_infoState_1099_ = lean_ctor_get(v___x_1091_, 7);
v_snapshotTasks_1100_ = lean_ctor_get(v___x_1091_, 8);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___x_1091_, 5);
lean_dec(v_unused_1114_);
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1113_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snapshotTasks_1100_);
lean_inc(v_infoState_1099_);
lean_inc(v_messages_1098_);
lean_inc(v_traceState_1097_);
lean_inc(v_auxDeclNGen_1096_);
lean_inc(v_ngen_1095_);
lean_inc(v_nextMacroScope_1094_);
lean_inc(v_env_1093_);
lean_dec(v___x_1091_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1113_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_asyncMode_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_asyncMode_1104_ = lean_ctor_get(v_toEnvExtension_1092_, 2);
v___x_1105_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1086_, v_env_1093_, v_entry_1085_, v_asyncMode_1104_, v___x_1088_);
v___x_1106_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 5, v___x_1106_);
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1108_ = v___x_1102_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_nextMacroScope_1094_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_ngen_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_auxDeclNGen_1096_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_traceState_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 5, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1112_, 6, v_messages_1098_);
lean_ctor_set(v_reuseFailAlloc_1112_, 7, v_infoState_1099_);
lean_ctor_set(v_reuseFailAlloc_1112_, 8, v_snapshotTasks_1100_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_st_ref_set(v___y_1090_, v___x_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_mod_1155_, lean_object* v_isMeta_1156_, lean_object* v_hint_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
uint8_t v_isMeta_boxed_1161_; lean_object* v_res_1162_; 
v_isMeta_boxed_1161_ = lean_unbox(v_isMeta_1156_);
v_res_1162_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_mod_1155_, v_isMeta_boxed_1161_, v_hint_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object* v___x_1163_, lean_object* v_declName_1164_, lean_object* v_as_1165_, size_t v_sz_1166_, size_t v_i_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_lt(v_i_1167_, v_sz_1166_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v_declName_1164_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_b_1168_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v_modules_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v_toImport_1179_; lean_object* v_module_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1174_ = l_Lean_Environment_header(v___x_1163_);
v_modules_1175_ = lean_ctor_get(v___x_1174_, 3);
lean_inc_ref(v_modules_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1177_ = lean_array_uget_borrowed(v_as_1165_, v_i_1167_);
v___x_1178_ = lean_array_get(v___x_1176_, v_modules_1175_, v_a_1177_);
lean_dec_ref(v_modules_1175_);
v_toImport_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_ref(v_toImport_1179_);
lean_dec(v___x_1178_);
v_module_1180_ = lean_ctor_get(v_toImport_1179_, 0);
lean_inc(v_module_1180_);
lean_dec_ref(v_toImport_1179_);
v___x_1181_ = 0;
lean_inc(v_declName_1164_);
v___x_1182_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1180_, v___x_1181_, v_declName_1164_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; 
lean_dec_ref_known(v___x_1182_, 1);
v___x_1183_ = lean_box(0);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1167_, v___x_1184_);
v_i_1167_ = v___x_1185_;
v_b_1168_ = v___x_1183_;
goto _start;
}
else
{
lean_dec(v_declName_1164_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v___x_1187_, lean_object* v_declName_1188_, lean_object* v_as_1189_, lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v___x_1187_, v_declName_1188_, v_as_1189_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_as_1189_);
lean_dec_ref(v___x_1187_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object* v_a_1199_, lean_object* v_x_1200_){
_start:
{
if (lean_obj_tag(v_x_1200_) == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_box(0);
return v___x_1201_;
}
else
{
lean_object* v_key_1202_; lean_object* v_value_1203_; lean_object* v_tail_1204_; uint8_t v___x_1205_; 
v_key_1202_ = lean_ctor_get(v_x_1200_, 0);
v_value_1203_ = lean_ctor_get(v_x_1200_, 1);
v_tail_1204_ = lean_ctor_get(v_x_1200_, 2);
v___x_1205_ = lean_name_eq(v_key_1202_, v_a_1199_);
if (v___x_1205_ == 0)
{
v_x_1200_ = v_tail_1204_;
goto _start;
}
else
{
lean_object* v___x_1207_; 
lean_inc(v_value_1203_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_value_1203_);
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec(v_a_1208_);
return v_res_1210_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1211_; uint64_t v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(1723u);
v___x_1212_ = lean_uint64_of_nat(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object* v_m_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_buckets_1215_; lean_object* v___x_1216_; uint64_t v___y_1218_; 
v_buckets_1215_ = lean_ctor_get(v_m_1213_, 1);
v___x_1216_ = lean_array_get_size(v_buckets_1215_);
if (lean_obj_tag(v_a_1214_) == 0)
{
uint64_t v___x_1232_; 
v___x_1232_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___closed__0);
v___y_1218_ = v___x_1232_;
goto v___jp_1217_;
}
else
{
uint64_t v_hash_1233_; 
v_hash_1233_ = lean_ctor_get_uint64(v_a_1214_, sizeof(void*)*2);
v___y_1218_ = v_hash_1233_;
goto v___jp_1217_;
}
v___jp_1217_:
{
uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v_fold_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1219_ = 32ULL;
v___x_1220_ = lean_uint64_shift_right(v___y_1218_, v___x_1219_);
v_fold_1221_ = lean_uint64_xor(v___y_1218_, v___x_1220_);
v___x_1222_ = 16ULL;
v___x_1223_ = lean_uint64_shift_right(v_fold_1221_, v___x_1222_);
v___x_1224_ = lean_uint64_xor(v_fold_1221_, v___x_1223_);
v___x_1225_ = lean_uint64_to_usize(v___x_1224_);
v___x_1226_ = lean_usize_of_nat(v___x_1216_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_sub(v___x_1226_, v___x_1227_);
v___x_1229_ = lean_usize_land(v___x_1225_, v___x_1228_);
v___x_1230_ = lean_array_uget_borrowed(v_buckets_1215_, v___x_1229_);
v___x_1231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1214_, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object* v_m_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_m_1234_);
return v_res_1236_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1));
v___x_1240_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0));
v___x_1241_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1240_, v___x_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(lean_object* v_declName_1244_, uint8_t v_isMeta_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v_env_1253_; lean_object* v___y_1255_; lean_object* v___x_1268_; 
v___x_1249_ = lean_st_ref_get(v___y_1247_);
v_env_1253_ = lean_ctor_get(v___x_1249_, 0);
lean_inc_ref(v_env_1253_);
lean_dec(v___x_1249_);
v___x_1268_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1253_, v_declName_1244_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_dec_ref(v_env_1253_);
lean_dec(v_declName_1244_);
goto v___jp_1250_;
}
else
{
lean_object* v_val_1269_; lean_object* v___x_1270_; lean_object* v_modules_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = l_Lean_Environment_header(v_env_1253_);
v_modules_1271_ = lean_ctor_get(v___x_1270_, 3);
lean_inc_ref(v_modules_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_array_get_size(v_modules_1271_);
v___x_1273_ = lean_nat_dec_lt(v_val_1269_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v_modules_1271_);
lean_dec(v_val_1269_);
lean_dec_ref(v_env_1253_);
lean_dec(v_declName_1244_);
goto v___jp_1250_;
}
else
{
lean_object* v___x_1274_; lean_object* v_env_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___y_1279_; 
v___x_1274_ = lean_st_ref_get(v___y_1247_);
v_env_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc_ref(v_env_1275_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2);
v___x_1277_ = lean_array_fget(v_modules_1271_, v_val_1269_);
lean_dec(v_val_1269_);
lean_dec_ref(v_modules_1271_);
if (v_isMeta_1245_ == 0)
{
lean_dec_ref(v_env_1275_);
v___y_1279_ = v_isMeta_1245_;
goto v___jp_1278_;
}
else
{
uint8_t v___x_1290_; 
lean_inc(v_declName_1244_);
v___x_1290_ = l_Lean_isMarkedMeta(v_env_1275_, v_declName_1244_);
if (v___x_1290_ == 0)
{
v___y_1279_ = v_isMeta_1245_;
goto v___jp_1278_;
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
v___y_1279_ = v___x_1291_;
goto v___jp_1278_;
}
}
v___jp_1278_:
{
lean_object* v_toImport_1280_; lean_object* v_module_1281_; lean_object* v___x_1282_; 
v_toImport_1280_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_toImport_1280_);
lean_dec(v___x_1277_);
v_module_1281_ = lean_ctor_get(v_toImport_1280_, 0);
lean_inc(v_module_1281_);
lean_dec_ref(v_toImport_1280_);
lean_inc(v_declName_1244_);
v___x_1282_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1281_, v___y_1279_, v_declName_1244_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v___x_1282_, 1);
v___x_1283_ = l_Lean_indirectModUseExt;
v___x_1284_ = lean_box(1);
v___x_1285_ = lean_box(0);
lean_inc_ref(v_env_1253_);
v___x_1286_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1276_, v___x_1283_, v_env_1253_, v___x_1284_, v___x_1285_);
v___x_1287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v___x_1286_, v_declName_1244_);
lean_dec(v___x_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__3));
v___y_1255_ = v___x_1288_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1289_; 
v_val_1289_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1287_, 1);
v___y_1255_ = v_val_1289_;
goto v___jp_1254_;
}
}
else
{
lean_dec_ref(v_env_1253_);
lean_dec(v_declName_1244_);
return v___x_1282_;
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; size_t v_sz_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_box(0);
v_sz_1257_ = lean_array_size(v___y_1255_);
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v_env_1253_, v_declName_1244_, v___y_1255_, v_sz_1257_, v___x_1258_, v___x_1256_, v___y_1246_, v___y_1247_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_env_1253_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1259_, 0);
lean_dec(v_unused_1267_);
v___x_1261_ = v___x_1259_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v___x_1259_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1256_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1256_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1292_, lean_object* v_isMeta_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
uint8_t v_isMeta_boxed_1297_; lean_object* v_res_1298_; 
v_isMeta_boxed_1297_ = lean_unbox(v_isMeta_1293_);
v_res_1298_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_declName_1292_, v_isMeta_boxed_1297_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1298_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, uint8_t v_builtin_1316_, lean_object* v___x_1317_, lean_object* v_name_1318_, lean_object* v_declName_1319_, lean_object* v_stx_1320_, uint8_t v_kind_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1459_; lean_object* v___y_1460_; uint8_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = 0;
v___x_1469_ = l_Lean_instBEqAttributeKind_beq(v_kind_1321_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_dec(v_stx_1320_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v___x_1470_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1318_, v_kind_1321_, v___y_1322_, v___y_1323_);
return v___x_1470_;
}
else
{
goto v___jp_1466_;
}
v___jp_1325_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1332_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1331_);
v___x_1333_ = l_Lean_mkConst(v___x_1332_, v___y_1329_);
v___x_1334_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___y_1327_);
v___x_1335_ = l_Lean_mkAppB(v___x_1333_, v___x_1334_, v___y_1330_);
v___x_1336_ = l_Lean_declareBuiltin(v_declName_1319_, v___x_1335_, v___y_1326_, v___y_1328_);
return v___x_1336_;
}
v___jp_1337_:
{
if (v_builtin_1316_ == 0)
{
lean_object* v___x_1343_; lean_object* v_env_1344_; lean_object* v_options_1345_; lean_object* v_ref_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v___x_1343_ = lean_st_ref_get(v___y_1342_);
v_env_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_ref(v_env_1344_);
lean_dec(v___x_1343_);
v_options_1345_ = lean_ctor_get(v___y_1341_, 2);
v_ref_1346_ = lean_ctor_get(v___y_1341_, 5);
lean_inc_ref(v_options_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_env_1344_);
lean_ctor_set(v___x_1347_, 1, v_options_1345_);
lean_inc(v_declName_1319_);
v___x_1348_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_declName_1319_, v___x_1347_);
lean_dec_ref_known(v___x_1347_, 2);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v_toEnvExtension_1351_; lean_object* v_asyncMode_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_1351_ = lean_ctor_get(v___x_1350_, 0);
v_asyncMode_1352_ = lean_ctor_get(v_toEnvExtension_1351_, 2);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___y_1339_);
lean_ctor_set(v___x_1353_, 1, v_a_1349_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_declName_1319_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1350_, v___y_1340_, v___x_1354_, v_asyncMode_1352_, v___x_1317_);
v___x_1356_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v___x_1355_, v___y_1342_);
return v___x_1356_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1359_ = v___x_1348_;
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1348_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1361_ = lean_io_error_to_string(v_a_1357_);
v___x_1362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
v___x_1363_ = l_Lean_MessageData_ofFormat(v___x_1362_);
lean_inc(v_ref_1346_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_ref_1346_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1364_);
v___x_1366_ = v___x_1359_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
lean_dec_ref(v___y_1340_);
lean_dec(v___x_1317_);
v___x_1369_ = l_Lean_ConstantInfo_type(v___y_1338_);
lean_dec_ref(v___y_1338_);
v___x_1370_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1314_);
lean_inc_ref(v___x_1313_);
v___x_1371_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1370_);
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Lean_Expr_const___override(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_expr_eqv(v___x_1369_, v___x_1373_);
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___x_1369_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_inc(v_declName_1319_);
v___x_1375_ = l_Lean_mkConst(v_declName_1319_, v___x_1372_);
v___y_1326_ = v___y_1341_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1342_;
v___y_1329_ = v___x_1372_;
v___y_1330_ = v___x_1375_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1314_);
lean_inc_ref(v___x_1313_);
v___x_1377_ = l_Lean_Name_mkStr5(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1370_, v___x_1376_);
v___x_1378_ = l_Lean_mkConst(v___x_1377_, v___x_1372_);
lean_inc(v_declName_1319_);
v___x_1379_ = l_Lean_mkConst(v_declName_1319_, v___x_1372_);
v___x_1380_ = l_Lean_Expr_app___override(v___x_1378_, v___x_1379_);
v___y_1326_ = v___y_1341_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1342_;
v___y_1329_ = v___x_1372_;
v___y_1330_ = v___x_1380_;
goto v___jp_1325_;
}
}
}
v___jp_1381_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1382_);
v___x_1388_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1389_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1314_);
lean_inc_ref(v___x_1313_);
v___x_1390_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1389_);
v___x_1391_ = l_Lean_MessageData_ofConstName(v___x_1390_, v___y_1386_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1388_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
v___x_1396_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1395_);
v___x_1397_ = l_Lean_MessageData_ofConstName(v___x_1396_, v___y_1386_);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1394_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Lean_MessageData_ofName(v_declName_1319_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l_Lean_ConstantInfo_type(v___y_1383_);
lean_dec_ref(v___y_1383_);
v___x_1406_ = l_Lean_indentExpr(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1404_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_1407_, v___y_1384_, v___y_1387_);
return v___x_1408_;
}
v___jp_1409_:
{
lean_object* v___x_1413_; 
lean_inc(v_declName_1319_);
v___x_1413_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_declName_1319_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1320_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_1416_, v___x_1417_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc_n(v_a_1419_, 2);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = 0;
v___x_1421_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_a_1419_, v___x_1420_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
lean_dec_ref_known(v___x_1421_, 1);
v___x_1422_ = l_Lean_ConstantInfo_levelParams(v_a_1414_);
v___x_1423_ = l_List_isEmpty___redArg(v___x_1422_);
lean_dec(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v___x_1317_);
v___y_1382_ = v_a_1419_;
v___y_1383_ = v_a_1414_;
v___y_1384_ = v___y_1411_;
v___y_1385_ = v___y_1410_;
v___y_1386_ = v___x_1420_;
v___y_1387_ = v___y_1412_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1424_ = l_Lean_ConstantInfo_type(v_a_1414_);
v___x_1425_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1314_);
lean_inc_ref(v___x_1313_);
v___x_1426_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1425_);
v___x_1427_ = lean_box(0);
v___x_1428_ = l_Lean_Expr_const___override(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_expr_eqv(v___x_1424_, v___x_1428_);
lean_dec_ref(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1314_);
lean_inc_ref(v___x_1313_);
v___x_1431_ = l_Lean_Name_mkStr4(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1430_);
v___x_1432_ = l_Lean_Expr_const___override(v___x_1431_, v___x_1427_);
v___x_1433_ = lean_expr_eqv(v___x_1424_, v___x_1432_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1424_);
if (v___x_1433_ == 0)
{
lean_dec(v___x_1317_);
v___y_1382_ = v_a_1419_;
v___y_1383_ = v_a_1414_;
v___y_1384_ = v___y_1411_;
v___y_1385_ = v___y_1410_;
v___y_1386_ = v___x_1420_;
v___y_1387_ = v___y_1412_;
goto v___jp_1381_;
}
else
{
v___y_1338_ = v_a_1414_;
v___y_1339_ = v_a_1419_;
v___y_1340_ = v___y_1410_;
v___y_1341_ = v___y_1411_;
v___y_1342_ = v___y_1412_;
goto v___jp_1337_;
}
}
else
{
lean_dec_ref(v___x_1424_);
v___y_1338_ = v_a_1414_;
v___y_1339_ = v_a_1419_;
v___y_1340_ = v___y_1410_;
v___y_1341_ = v___y_1411_;
v___y_1342_ = v___y_1412_;
goto v___jp_1337_;
}
}
}
else
{
lean_dec(v_a_1419_);
lean_dec(v_a_1414_);
lean_dec_ref(v___y_1410_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
return v___x_1421_;
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1414_);
lean_dec_ref(v___y_1410_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v_a_1434_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1418_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1418_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1414_);
lean_dec_ref(v___y_1410_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v_a_1442_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1415_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1415_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___y_1410_);
lean_dec(v_stx_1320_);
lean_dec(v_declName_1319_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v_a_1450_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1413_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1413_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
v___jp_1458_:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_st_ref_get(v___y_1460_);
if (v_builtin_1316_ == 0)
{
lean_object* v_env_1462_; lean_object* v___x_1463_; 
v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_env_1462_);
lean_dec(v___x_1461_);
v___x_1463_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1462_, v_declName_1319_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec(v_name_1318_);
v___y_1410_ = v_env_1462_;
v___y_1411_ = v___y_1459_;
v___y_1412_ = v___y_1460_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1463_, 1);
lean_dec_ref(v_env_1462_);
lean_dec(v_stx_1320_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
v___x_1464_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_name_1318_, v_declName_1319_, v___y_1459_, v___y_1460_);
return v___x_1464_;
}
}
else
{
lean_object* v_env_1465_; 
lean_dec(v_name_1318_);
v_env_1465_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_env_1465_);
lean_dec(v___x_1461_);
v___y_1410_ = v_env_1465_;
v___y_1411_ = v___y_1459_;
v___y_1412_ = v___y_1460_;
goto v___jp_1409_;
}
}
v___jp_1466_:
{
if (v_builtin_1316_ == 0)
{
lean_object* v___x_1467_; 
lean_inc(v_declName_1319_);
lean_inc(v_name_1318_);
v___x_1467_ = l_Lean_ensureAttrDeclIsMeta(v_name_1318_, v_declName_1319_, v_kind_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v___y_1459_ = v___y_1322_;
v___y_1460_ = v___y_1323_;
goto v___jp_1458_;
}
else
{
lean_dec(v_stx_1320_);
lean_dec(v_declName_1319_);
lean_dec(v_name_1318_);
lean_dec(v___x_1317_);
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1314_);
lean_dec_ref(v___x_1313_);
return v___x_1467_;
}
}
else
{
v___y_1459_ = v___y_1322_;
v___y_1460_ = v___y_1323_;
goto v___jp_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v_builtin_1474_, lean_object* v___x_1475_, lean_object* v_name_1476_, lean_object* v_declName_1477_, lean_object* v_stx_1478_, lean_object* v_kind_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_builtin_boxed_1483_; uint8_t v_kind_boxed_1484_; lean_object* v_res_1485_; 
v_builtin_boxed_1483_ = lean_unbox(v_builtin_1474_);
v_kind_boxed_1484_ = lean_unbox(v_kind_1479_);
v_res_1485_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1471_, v___x_1472_, v___x_1473_, v_builtin_boxed_1483_, v___x_1475_, v_name_1476_, v_declName_1477_, v_stx_1478_, v_kind_boxed_1484_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t v_builtin_1544_, lean_object* v_name_1545_){
_start:
{
lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; 
lean_inc_n(v_name_1545_, 2);
v___f_1547_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1547_, 0, v_name_1545_);
v___x_1548_ = lean_box(0);
v___x_1549_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1550_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1551_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4));
v___x_1552_ = lean_box(v_builtin_1544_);
v___f_1553_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1553_, 0, v___x_1549_);
lean_closure_set(v___f_1553_, 1, v___x_1550_);
lean_closure_set(v___f_1553_, 2, v___x_1551_);
lean_closure_set(v___f_1553_, 3, v___x_1552_);
lean_closure_set(v___f_1553_, 4, v___x_1548_);
lean_closure_set(v___f_1553_, 5, v_name_1545_);
v___x_1554_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
if (v_builtin_1544_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___y_1556_ = v___x_1563_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___y_1556_ = v___x_1564_;
goto v___jp_1555_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___y_1556_);
v___x_1558_ = lean_string_append(v___y_1556_, v___x_1557_);
v___x_1559_ = 1;
v___x_1560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1560_, 0, v___x_1554_);
lean_ctor_set(v___x_1560_, 1, v_name_1545_);
lean_ctor_set(v___x_1560_, 2, v___x_1558_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*3, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___f_1553_);
lean_ctor_set(v___x_1561_, 2, v___f_1547_);
v___x_1562_ = l_Lean_registerBuiltinAttribute(v___x_1561_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_builtin_1565_, lean_object* v_name_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_builtin_boxed_1568_; lean_object* v_res_1569_; 
v_builtin_boxed_1568_ = lean_unbox(v_builtin_1565_);
v_res_1569_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_builtin_boxed_1568_, v_name_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = 1;
v___x_1578_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1579_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1577_, v___x_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref_known(v___x_1579_, 1);
v___x_1580_ = 0;
v___x_1581_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1582_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1580_, v___x_1581_);
return v___x_1582_;
}
else
{
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1585_, lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_1586_, v___y_1587_, v___y_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_msg_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(v_00_u03b1_1591_, v_msg_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1597_, lean_object* v_attrName_1598_, lean_object* v_declName_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_1598_, v_declName_1599_, v___y_1600_, v___y_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1604_, lean_object* v_attrName_1605_, lean_object* v_declName_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(v_00_u03b1_1604_, v_attrName_1605_, v_declName_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1611_, lean_object* v_name_1612_, uint8_t v_kind_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1612_, v_kind_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_name_1619_, lean_object* v_kind_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_kind_boxed_1624_; lean_object* v_res_1625_; 
v_kind_boxed_1624_ = lean_unbox(v_kind_1620_);
v_res_1625_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(v_00_u03b1_1618_, v_name_1619_, v_kind_boxed_1624_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_1626_, lean_object* v_constName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_1627_, v___y_1628_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_constName_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_1632_, v_constName_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(lean_object* v_00_u03b2_1638_, lean_object* v_m_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1639_, v_a_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_m_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(v_00_u03b2_1642_, v_m_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_m_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1646_, lean_object* v_ref_1647_, lean_object* v_constName_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_1647_, v_constName_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_ref_1654_, lean_object* v_constName_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b1_1653_, v_ref_1654_, v_constName_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v_ref_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(v_00_u03b2_1664_, v_x_1665_, v_x_1666_);
lean_dec_ref(v_x_1666_);
lean_dec_ref(v_x_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(lean_object* v_00_u03b2_1669_, lean_object* v_a_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1673_, lean_object* v_a_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(v_00_u03b2_1673_, v_a_1674_, v_x_1675_);
lean_dec(v_x_1675_);
lean_dec(v_a_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1677_, lean_object* v_ref_1678_, lean_object* v_msg_1679_, lean_object* v_declHint_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_1678_, v_msg_1679_, v_declHint_1680_, v___y_1681_, v___y_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_ref_1686_, lean_object* v_msg_1687_, lean_object* v_declHint_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_00_u03b1_1685_, v_ref_1686_, v_msg_1687_, v_declHint_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_ref_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_1693_, lean_object* v_x_1694_, size_t v_x_1695_, lean_object* v_x_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_1694_, v_x_1695_, v_x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
size_t v_x_10592__boxed_1702_; uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_x_10592__boxed_1702_ = lean_unbox_usize(v_x_1700_);
lean_dec(v_x_1700_);
v_res_1703_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(v_00_u03b2_1698_, v_x_1699_, v_x_10592__boxed_1702_, v_x_1701_);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_x_1699_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(lean_object* v_msg_1705_, lean_object* v_declHint_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_1705_, v_declHint_1706_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___boxed(lean_object* v_msg_1711_, lean_object* v_declHint_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(v_msg_1711_, v_declHint_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b1_1717_, lean_object* v_ref_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_1718_, v_msg_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_ref_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(v_00_u03b1_1724_, v_ref_1725_, v_msg_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v_ref_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(lean_object* v_00_u03b2_1731_, lean_object* v_keys_1732_, lean_object* v_vals_1733_, lean_object* v_heq_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_1732_, v_i_1735_, v_k_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1738_, lean_object* v_keys_1739_, lean_object* v_vals_1740_, lean_object* v_heq_1741_, lean_object* v_i_1742_, lean_object* v_k_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(v_00_u03b2_1738_, v_keys_1739_, v_vals_1740_, v_heq_1741_, v_i_1742_, v_k_1743_);
lean_dec_ref(v_k_1743_);
lean_dec_ref(v_vals_1740_);
lean_dec_ref(v_keys_1739_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1746_, lean_object* v_opt_1747_){
_start:
{
lean_object* v_name_1748_; lean_object* v_defValue_1749_; lean_object* v_map_1750_; lean_object* v___x_1751_; 
v_name_1748_ = lean_ctor_get(v_opt_1747_, 0);
v_defValue_1749_ = lean_ctor_get(v_opt_1747_, 1);
v_map_1750_ = lean_ctor_get(v_opts_1746_, 0);
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1750_, v_name_1748_);
if (lean_obj_tag(v___x_1751_) == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_unbox(v_defValue_1749_);
return v___x_1752_;
}
else
{
lean_object* v_val_1753_; 
v_val_1753_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1753_);
lean_dec_ref_known(v___x_1751_, 1);
if (lean_obj_tag(v_val_1753_) == 1)
{
uint8_t v_v_1754_; 
v_v_1754_ = lean_ctor_get_uint8(v_val_1753_, 0);
lean_dec_ref_known(v_val_1753_, 0);
return v_v_1754_;
}
else
{
uint8_t v___x_1755_; 
lean_dec(v_val_1753_);
v___x_1755_ = lean_unbox(v_defValue_1749_);
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1756_, lean_object* v_opt_1757_){
_start:
{
uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_res_1758_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1756_, v_opt_1757_);
lean_dec_ref(v_opt_1757_);
lean_dec_ref(v_opts_1756_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1760_, uint8_t v_suppressElabErrors_1761_, lean_object* v_x_1762_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 1)
{
lean_object* v_pre_1763_; 
v_pre_1763_ = lean_ctor_get(v_x_1762_, 0);
if (lean_obj_tag(v_pre_1763_) == 0)
{
lean_object* v_str_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_str_1764_ = lean_ctor_get(v_x_1762_, 1);
v___x_1765_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10));
v___x_1766_ = lean_string_dec_eq(v_str_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
return v___y_1760_;
}
else
{
return v_suppressElabErrors_1761_;
}
}
else
{
return v___y_1760_;
}
}
else
{
return v___y_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1767_, lean_object* v_suppressElabErrors_1768_, lean_object* v_x_1769_){
_start:
{
uint8_t v___y_2198__boxed_1770_; uint8_t v_suppressElabErrors_boxed_1771_; uint8_t v_res_1772_; lean_object* v_r_1773_; 
v___y_2198__boxed_1770_ = lean_unbox(v___y_1767_);
v_suppressElabErrors_boxed_1771_ = lean_unbox(v_suppressElabErrors_1768_);
v_res_1772_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(v___y_2198__boxed_1770_, v_suppressElabErrors_boxed_1771_, v_x_1769_);
lean_dec(v_x_1769_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v_env_1778_; lean_object* v___x_1779_; lean_object* v_scopes_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_opts_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1777_ = lean_st_ref_get(v___y_1775_);
v_env_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_ref(v_env_1778_);
lean_dec(v___x_1777_);
v___x_1779_ = lean_st_ref_get(v___y_1775_);
v_scopes_1780_ = lean_ctor_get(v___x_1779_, 2);
lean_inc(v_scopes_1780_);
lean_dec(v___x_1779_);
v___x_1781_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1782_ = l_List_head_x21___redArg(v___x_1781_, v_scopes_1780_);
lean_dec(v_scopes_1780_);
v_opts_1783_ = lean_ctor_get(v___x_1782_, 1);
lean_inc_ref(v_opts_1783_);
lean_dec(v___x_1782_);
v___x_1784_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1785_ = lean_unsigned_to_nat(32u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
lean_dec_ref(v___x_1786_);
v___x_1787_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1788_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1788_, 0, v_env_1778_);
lean_ctor_set(v___x_1788_, 1, v___x_1784_);
lean_ctor_set(v___x_1788_, 2, v___x_1787_);
lean_ctor_set(v___x_1788_, 3, v_opts_1783_);
v___x_1789_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v_msgData_1774_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_1791_, v___y_1792_);
lean_dec(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(lean_object* v_ref_1795_, lean_object* v_msgData_1796_, uint8_t v_severity_1797_, uint8_t v_isSilent_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; uint8_t v___y_1809_; lean_object* v___y_1810_; uint8_t v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1868_; uint8_t v___y_1869_; lean_object* v___y_1870_; uint8_t v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1902_; uint8_t v___y_1903_; uint8_t v___y_1904_; uint8_t v___x_1919_; uint8_t v___y_1921_; uint8_t v___y_1922_; uint8_t v___y_1923_; uint8_t v___y_1925_; uint8_t v___x_1937_; 
v___x_1919_ = 2;
v___x_1937_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1797_, v___x_1919_);
if (v___x_1937_ == 0)
{
v___y_1925_ = v___x_1937_;
goto v___jp_1924_;
}
else
{
uint8_t v___x_1938_; 
lean_inc_ref(v_msgData_1796_);
v___x_1938_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1796_);
v___y_1925_ = v___x_1938_;
goto v___jp_1924_;
}
v___jp_1802_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Elab_Command_getScope___redArg(v___y_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = l_Lean_Elab_Command_getScope___redArg(v___y_1810_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1848_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1848_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1848_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v_currNamespace_1819_; lean_object* v_openDecls_1820_; lean_object* v_env_1821_; lean_object* v_messages_1822_; lean_object* v_scopes_1823_; lean_object* v_usedQuotCtxts_1824_; lean_object* v_nextMacroScope_1825_; lean_object* v_maxRecDepth_1826_; lean_object* v_ngen_1827_; lean_object* v_auxDeclNGen_1828_; lean_object* v_infoState_1829_; lean_object* v_traceState_1830_; lean_object* v_snapshotTasks_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1847_; 
v___x_1818_ = lean_st_ref_take(v___y_1810_);
v_currNamespace_1819_ = lean_ctor_get(v_a_1812_, 2);
lean_inc(v_currNamespace_1819_);
lean_dec(v_a_1812_);
v_openDecls_1820_ = lean_ctor_get(v_a_1814_, 3);
lean_inc(v_openDecls_1820_);
lean_dec(v_a_1814_);
v_env_1821_ = lean_ctor_get(v___x_1818_, 0);
v_messages_1822_ = lean_ctor_get(v___x_1818_, 1);
v_scopes_1823_ = lean_ctor_get(v___x_1818_, 2);
v_usedQuotCtxts_1824_ = lean_ctor_get(v___x_1818_, 3);
v_nextMacroScope_1825_ = lean_ctor_get(v___x_1818_, 4);
v_maxRecDepth_1826_ = lean_ctor_get(v___x_1818_, 5);
v_ngen_1827_ = lean_ctor_get(v___x_1818_, 6);
v_auxDeclNGen_1828_ = lean_ctor_get(v___x_1818_, 7);
v_infoState_1829_ = lean_ctor_get(v___x_1818_, 8);
v_traceState_1830_ = lean_ctor_get(v___x_1818_, 9);
v_snapshotTasks_1831_ = lean_ctor_get(v___x_1818_, 10);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1833_ = v___x_1818_;
v_isShared_1834_ = v_isSharedCheck_1847_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snapshotTasks_1831_);
lean_inc(v_traceState_1830_);
lean_inc(v_infoState_1829_);
lean_inc(v_auxDeclNGen_1828_);
lean_inc(v_ngen_1827_);
lean_inc(v_maxRecDepth_1826_);
lean_inc(v_nextMacroScope_1825_);
lean_inc(v_usedQuotCtxts_1824_);
lean_inc(v_scopes_1823_);
lean_inc(v_messages_1822_);
lean_inc(v_env_1821_);
lean_dec(v___x_1818_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1847_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_currNamespace_1819_);
lean_ctor_set(v___x_1835_, 1, v_openDecls_1820_);
v___x_1836_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___y_1803_);
lean_inc_ref(v___y_1807_);
lean_inc_ref(v___y_1806_);
v___x_1837_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1837_, 0, v___y_1806_);
lean_ctor_set(v___x_1837_, 1, v___y_1805_);
lean_ctor_set(v___x_1837_, 2, v___y_1804_);
lean_ctor_set(v___x_1837_, 3, v___y_1807_);
lean_ctor_set(v___x_1837_, 4, v___x_1836_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*5, v___y_1809_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*5 + 1, v___y_1808_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*5 + 2, v_isSilent_1798_);
v___x_1838_ = l_Lean_MessageLog_add(v___x_1837_, v_messages_1822_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1838_);
v___x_1840_ = v___x_1833_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_env_1821_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_scopes_1823_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_usedQuotCtxts_1824_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_nextMacroScope_1825_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_maxRecDepth_1826_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_ngen_1827_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_auxDeclNGen_1828_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_infoState_1829_);
lean_ctor_set(v_reuseFailAlloc_1846_, 9, v_traceState_1830_);
lean_ctor_set(v_reuseFailAlloc_1846_, 10, v_snapshotTasks_1831_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_st_ref_set(v___y_1810_, v___x_1840_);
v___x_1842_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1842_);
v___x_1844_ = v___x_1816_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1812_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
v_a_1849_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1813_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1813_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
v_a_1857_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1811_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1811_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
v___jp_1865_:
{
lean_object* v_fileName_1871_; lean_object* v_fileMap_1872_; uint8_t v_suppressElabErrors_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1892_; 
v_fileName_1871_ = lean_ctor_get(v___y_1799_, 0);
v_fileMap_1872_ = lean_ctor_get(v___y_1799_, 1);
v_suppressElabErrors_1873_ = lean_ctor_get_uint8(v___y_1799_, sizeof(void*)*10);
v___x_1874_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1796_);
v___x_1875_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1874_, v___y_1800_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1892_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1892_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_inc_ref_n(v_fileMap_1872_, 2);
v___x_1880_ = l_Lean_FileMap_toPosition(v_fileMap_1872_, v___y_1867_);
lean_dec(v___y_1867_);
v___x_1881_ = l_Lean_FileMap_toPosition(v_fileMap_1872_, v___y_1870_);
lean_dec(v___y_1870_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
v___x_1883_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
if (v_suppressElabErrors_1873_ == 0)
{
lean_del_object(v___x_1878_);
v___y_1803_ = v_a_1876_;
v___y_1804_ = v___x_1882_;
v___y_1805_ = v___x_1880_;
v___y_1806_ = v_fileName_1871_;
v___y_1807_ = v___x_1883_;
v___y_1808_ = v___y_1869_;
v___y_1809_ = v___y_1868_;
v___y_1810_ = v___y_1800_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; uint8_t v___x_1887_; 
v___x_1884_ = lean_box(v___y_1866_);
v___x_1885_ = lean_box(v_suppressElabErrors_1873_);
v___f_1886_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1886_, 0, v___x_1884_);
lean_closure_set(v___f_1886_, 1, v___x_1885_);
lean_inc(v_a_1876_);
v___x_1887_ = l_Lean_MessageData_hasTag(v___f_1886_, v_a_1876_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_dec_ref_known(v___x_1882_, 1);
lean_dec_ref(v___x_1880_);
lean_dec(v_a_1876_);
v___x_1888_ = lean_box(0);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1888_);
v___x_1890_ = v___x_1878_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_del_object(v___x_1878_);
v___y_1803_ = v_a_1876_;
v___y_1804_ = v___x_1882_;
v___y_1805_ = v___x_1880_;
v___y_1806_ = v_fileName_1871_;
v___y_1807_ = v___x_1883_;
v___y_1808_ = v___y_1869_;
v___y_1809_ = v___y_1868_;
v___y_1810_ = v___y_1800_;
goto v___jp_1802_;
}
}
}
}
v___jp_1893_:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Syntax_getTailPos_x3f(v___y_1895_, v___y_1897_);
lean_dec(v___y_1895_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_inc(v___y_1898_);
v___y_1866_ = v___y_1894_;
v___y_1867_ = v___y_1898_;
v___y_1868_ = v___y_1897_;
v___y_1869_ = v___y_1896_;
v___y_1870_ = v___y_1898_;
goto v___jp_1865_;
}
else
{
lean_object* v_val_1900_; 
v_val_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___y_1866_ = v___y_1894_;
v___y_1867_ = v___y_1898_;
v___y_1868_ = v___y_1897_;
v___y_1869_ = v___y_1896_;
v___y_1870_ = v_val_1900_;
goto v___jp_1865_;
}
}
v___jp_1901_:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Elab_Command_getRef___redArg(v___y_1799_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v_ref_1907_; lean_object* v___x_1908_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v_ref_1907_ = l_Lean_replaceRef(v_ref_1795_, v_a_1906_);
lean_dec(v_a_1906_);
v___x_1908_ = l_Lean_Syntax_getPos_x3f(v_ref_1907_, v___y_1903_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___y_1894_ = v___y_1902_;
v___y_1895_ = v_ref_1907_;
v___y_1896_ = v___y_1904_;
v___y_1897_ = v___y_1903_;
v___y_1898_ = v___x_1909_;
goto v___jp_1893_;
}
else
{
lean_object* v_val_1910_; 
v_val_1910_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v___x_1908_, 1);
v___y_1894_ = v___y_1902_;
v___y_1895_ = v_ref_1907_;
v___y_1896_ = v___y_1904_;
v___y_1897_ = v___y_1903_;
v___y_1898_ = v_val_1910_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_msgData_1796_);
v_a_1911_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1905_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1905_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
v___jp_1920_:
{
if (v___y_1923_ == 0)
{
v___y_1902_ = v___y_1921_;
v___y_1903_ = v___y_1922_;
v___y_1904_ = v_severity_1797_;
goto v___jp_1901_;
}
else
{
v___y_1902_ = v___y_1921_;
v___y_1903_ = v___y_1922_;
v___y_1904_ = v___x_1919_;
goto v___jp_1901_;
}
}
v___jp_1924_:
{
if (v___y_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v_scopes_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v_opts_1930_; uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1926_ = lean_st_ref_get(v___y_1800_);
v_scopes_1927_ = lean_ctor_get(v___x_1926_, 2);
lean_inc(v_scopes_1927_);
lean_dec(v___x_1926_);
v___x_1928_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1929_ = l_List_head_x21___redArg(v___x_1928_, v_scopes_1927_);
lean_dec(v_scopes_1927_);
v_opts_1930_ = lean_ctor_get(v___x_1929_, 1);
lean_inc_ref(v_opts_1930_);
lean_dec(v___x_1929_);
v___x_1931_ = 1;
v___x_1932_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1797_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_dec_ref(v_opts_1930_);
v___y_1921_ = v___y_1925_;
v___y_1922_ = v___y_1925_;
v___y_1923_ = v___x_1932_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_warningAsError;
v___x_1934_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1930_, v___x_1933_);
lean_dec_ref(v_opts_1930_);
v___y_1921_ = v___y_1925_;
v___y_1922_ = v___y_1925_;
v___y_1923_ = v___x_1934_;
goto v___jp_1920_;
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v_msgData_1796_);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1939_, lean_object* v_msgData_1940_, lean_object* v_severity_1941_, lean_object* v_isSilent_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v_severity_boxed_1946_; uint8_t v_isSilent_boxed_1947_; lean_object* v_res_1948_; 
v_severity_boxed_1946_ = lean_unbox(v_severity_1941_);
v_isSilent_boxed_1947_ = lean_unbox(v_isSilent_1942_);
v_res_1948_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1939_, v_msgData_1940_, v_severity_boxed_1946_, v_isSilent_boxed_1947_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_ref_1939_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object* v_ref_1949_, lean_object* v_msgData_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
uint8_t v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = 1;
v___x_1955_ = 0;
v___x_1956_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1949_, v_msgData_1950_, v___x_1954_, v___x_1955_, v___y_1951_, v___y_1952_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object* v_ref_1957_, lean_object* v_msgData_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_ref_1957_, v_msgData_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v_ref_1957_);
return v_res_1962_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(lean_object* v_linterOption_1969_, lean_object* v_stx_1970_, lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_name_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1993_; 
v_name_1975_ = lean_ctor_get(v_linterOption_1969_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_linterOption_1969_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v_linterOption_1969_, 1);
lean_dec(v_unused_1994_);
v___x_1977_ = v_linterOption_1969_;
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_name_1975_);
lean_dec(v_linterOption_1969_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1);
lean_inc(v_name_1975_);
v___x_1980_ = l_Lean_MessageData_ofName(v_name_1975_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_1980_);
lean_ctor_set(v___x_1977_, 0, v___x_1979_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_disable_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1983_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v_disable_1985_ = l_Lean_MessageData_note(v___x_1984_);
v___x_1986_ = l_Lean_Linter_linterMessageTag;
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_msg_1971_);
lean_ctor_set(v___x_1987_, 1, v_disable_1985_);
v___x_1988_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_name_1975_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v_stx_1970_);
v___x_1990_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_stx_1970_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_stx_1970_, v___x_1990_, v___y_1972_, v___y_1973_);
lean_dec(v_stx_1970_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object* v_linterOption_1995_, lean_object* v_stx_1996_, lean_object* v_msg_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v_linterOption_1995_, v_stx_1996_, v_msg_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2001_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lint___closed__1(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lint___closed__0));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object* v_stx_2005_, lean_object* v_msg_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2010_ = l_Lean_Linter_linter_missingDocs;
v___x_2011_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lint___closed__1, &l_Lean_Linter_MissingDocs_lint___closed__1_once, _init_l_Lean_Linter_MissingDocs_lint___closed__1);
v___x_2012_ = l_Lean_stringToMessageData(v_msg_2006_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2010_, v_stx_2005_, v___x_2013_, v_a_2007_, v_a_2008_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object* v_stx_2015_, lean_object* v_msg_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Linter_MissingDocs_lint(v_stx_2015_, v_msg_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2021_, v___y_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(v_msgData_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2030_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintEmpty___closed__0));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty(lean_object* v_stx_2034_, lean_object* v_msg_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2039_ = l_Lean_Linter_linter_missingDocs;
v___x_2040_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lintEmpty___closed__1, &l_Lean_Linter_MissingDocs_lintEmpty___closed__1_once, _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1);
v___x_2041_ = l_Lean_stringToMessageData(v_msg_2035_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2039_, v_stx_2034_, v___x_2042_, v_a_2036_, v_a_2037_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty___boxed(lean_object* v_stx_2044_, lean_object* v_msg_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2044_, v_msg_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object* v_stx_2050_, lean_object* v_msg_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2056_ = lean_string_append(v_msg_2051_, v___x_2055_);
v___x_2057_ = l_Lean_Syntax_getId(v_stx_2050_);
v___x_2058_ = 1;
v___x_2059_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_string_append(v___x_2056_, v___x_2059_);
lean_dec_ref(v___x_2059_);
v___x_2061_ = l_Lean_Linter_MissingDocs_lint(v_stx_2050_, v___x_2060_, v_a_2052_, v_a_2053_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object* v_stx_2062_, lean_object* v_msg_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2062_, v_msg_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed(lean_object* v_stx_2068_, lean_object* v_msg_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2074_ = lean_string_append(v_msg_2069_, v___x_2073_);
v___x_2075_ = l_Lean_Syntax_getId(v_stx_2068_);
v___x_2076_ = 1;
v___x_2077_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_string_append(v___x_2074_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2068_, v___x_2078_, v_a_2070_, v_a_2071_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed___boxed(lean_object* v_stx_2080_, lean_object* v_msg_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2080_, v_msg_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object* v_parent_2087_, lean_object* v_stx_2088_, lean_object* v_msg_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2093_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2094_ = lean_string_append(v_msg_2089_, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_getId(v_parent_2087_);
v___x_2096_ = 1;
v___x_2097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2095_, v___x_2096_);
v___x_2098_ = lean_string_append(v___x_2094_, v___x_2097_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2100_ = lean_string_append(v___x_2098_, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_getId(v_stx_2088_);
v___x_2102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2101_, v___x_2096_);
v___x_2103_ = lean_string_append(v___x_2100_, v___x_2102_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = l_Lean_Linter_MissingDocs_lint(v_stx_2088_, v___x_2103_, v_a_2090_, v_a_2091_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object* v_parent_2105_, lean_object* v_stx_2106_, lean_object* v_msg_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2105_, v_stx_2106_, v_msg_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_parent_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField(lean_object* v_parent_2112_, lean_object* v_stx_2113_, lean_object* v_msg_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2119_ = lean_string_append(v_msg_2114_, v___x_2118_);
v___x_2120_ = l_Lean_Syntax_getId(v_parent_2112_);
v___x_2121_ = 1;
v___x_2122_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_string_append(v___x_2119_, v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
v___x_2126_ = l_Lean_Syntax_getId(v_stx_2113_);
v___x_2127_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2126_, v___x_2121_);
v___x_2128_ = lean_string_append(v___x_2125_, v___x_2127_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2113_, v___x_2128_, v_a_2115_, v_a_2116_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField___boxed(lean_object* v_parent_2130_, lean_object* v_stx_2131_, lean_object* v_msg_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2130_, v_stx_2131_, v_msg_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_parent_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object* v_parent_2137_, lean_object* v_stx_2138_, lean_object* v_msg_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2144_ = lean_string_append(v_msg_2139_, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_getId(v_parent_2137_);
v___x_2146_ = 1;
v___x_2147_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_string_append(v___x_2144_, v___x_2147_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2150_ = lean_string_append(v___x_2148_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_getId(v_stx_2138_);
v___x_2152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2151_, v___x_2146_);
v___x_2153_ = lean_string_append(v___x_2150_, v___x_2152_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l_Lean_Linter_MissingDocs_lint(v_stx_2138_, v___x_2153_, v_a_2140_, v_a_2141_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object* v_parent_2155_, lean_object* v_stx_2156_, lean_object* v_msg_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Linter_MissingDocs_lintStructField(v_parent_2155_, v_stx_2156_, v_msg_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_parent_2155_);
return v_res_2161_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_box(1);
v___x_2163_ = l_Lean_MessageData_ofFormat(v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2));
v___x_2168_ = l_Lean_MessageData_ofFormat(v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 0)
{
return v_x_2169_;
}
else
{
lean_object* v_head_2171_; lean_object* v_tail_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2194_; 
v_head_2171_ = lean_ctor_get(v_x_2170_, 0);
v_tail_2172_ = lean_ctor_get(v_x_2170_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_x_2170_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2174_ = v_x_2170_;
v_isShared_2175_ = v_isSharedCheck_2194_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_tail_2172_);
lean_inc(v_head_2171_);
lean_dec(v_x_2170_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2194_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_before_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2192_; 
v_before_2176_ = lean_ctor_get(v_head_2171_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_head_2171_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v_head_2171_, 1);
lean_dec(v_unused_2193_);
v___x_2178_ = v_head_2171_;
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_before_2176_);
lean_dec(v_head_2171_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2192_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 7);
lean_ctor_set(v___x_2178_, 1, v___x_2180_);
lean_ctor_set(v___x_2178_, 0, v_x_2169_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_x_2169_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 7);
lean_ctor_set(v___x_2174_, 1, v___x_2183_);
lean_ctor_set(v___x_2174_, 0, v___x_2182_);
v___x_2185_ = v___x_2174_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = l_Lean_MessageData_ofSyntax(v_before_2176_);
v___x_2187_ = l_Lean_indentD(v___x_2186_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2185_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v_x_2169_ = v___x_2188_;
v_x_2170_ = v_tail_2172_;
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
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_2200_, lean_object* v_macroStack_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; lean_object* v_scopes_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_opts_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2204_ = lean_st_ref_get(v___y_2202_);
v_scopes_2205_ = lean_ctor_get(v___x_2204_, 2);
lean_inc(v_scopes_2205_);
lean_dec(v___x_2204_);
v___x_2206_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2207_ = l_List_head_x21___redArg(v___x_2206_, v_scopes_2205_);
lean_dec(v_scopes_2205_);
v_opts_2208_ = lean_ctor_get(v___x_2207_, 1);
lean_inc_ref(v_opts_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_Elab_pp_macroStack;
v___x_2210_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_2208_, v___x_2209_);
lean_dec_ref(v_opts_2208_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec(v_macroStack_2201_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_msgData_2200_);
return v___x_2211_;
}
else
{
if (lean_obj_tag(v_macroStack_2201_) == 0)
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v_msgData_2200_);
return v___x_2212_;
}
else
{
lean_object* v_head_2213_; lean_object* v_after_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2229_; 
v_head_2213_ = lean_ctor_get(v_macroStack_2201_, 0);
lean_inc(v_head_2213_);
v_after_2214_ = lean_ctor_get(v_head_2213_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_head_2213_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v_head_2213_, 0);
lean_dec(v_unused_2230_);
v___x_2216_ = v_head_2213_;
v_isShared_2217_ = v_isSharedCheck_2229_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_after_2214_);
lean_dec(v_head_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2229_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 7);
lean_ctor_set(v___x_2216_, 1, v___x_2218_);
lean_ctor_set(v___x_2216_, 0, v_msgData_2200_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_msgData_2200_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_msgData_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2221_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_MessageData_ofSyntax(v_after_2214_);
v___x_2224_ = l_Lean_indentD(v___x_2223_);
v_msgData_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2225_, 0, v___x_2222_);
lean_ctor_set(v_msgData_2225_, 1, v___x_2224_);
v___x_2226_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(v_msgData_2225_, v_macroStack_2201_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2231_, lean_object* v_macroStack_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2231_, v_macroStack_2232_, v___y_2233_);
lean_dec(v___y_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Elab_Command_getRef___redArg(v___y_2237_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_macroStack_2242_; lean_object* v___x_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2255_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v_macroStack_2242_ = lean_ctor_get(v___y_2237_, 4);
v___x_2243_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_2236_, v___y_2238_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Lean_Elab_getBetterRef(v_a_2241_, v_macroStack_2242_);
lean_dec(v_a_2241_);
lean_inc(v_macroStack_2242_);
v___x_2246_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2244_, v_macroStack_2242_, v___y_2238_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2245_);
lean_ctor_set(v___x_2251_, 1, v_a_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 1);
lean_ctor_set(v___x_2249_, 0, v___x_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_msg_2236_);
v_a_2256_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2240_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2240_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(lean_object* v_ref_2269_, lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Elab_Command_getRef___redArg(v___y_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v_fileName_2276_; lean_object* v_fileMap_2277_; lean_object* v_currRecDepth_2278_; lean_object* v_cmdPos_2279_; lean_object* v_macroStack_2280_; lean_object* v_quotContext_x3f_2281_; lean_object* v_currMacroScope_2282_; lean_object* v_snap_x3f_2283_; lean_object* v_cancelTk_x3f_2284_; uint8_t v_suppressElabErrors_2285_; lean_object* v_ref_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v_fileName_2276_ = lean_ctor_get(v___y_2271_, 0);
v_fileMap_2277_ = lean_ctor_get(v___y_2271_, 1);
v_currRecDepth_2278_ = lean_ctor_get(v___y_2271_, 2);
v_cmdPos_2279_ = lean_ctor_get(v___y_2271_, 3);
v_macroStack_2280_ = lean_ctor_get(v___y_2271_, 4);
v_quotContext_x3f_2281_ = lean_ctor_get(v___y_2271_, 5);
v_currMacroScope_2282_ = lean_ctor_get(v___y_2271_, 6);
v_snap_x3f_2283_ = lean_ctor_get(v___y_2271_, 8);
v_cancelTk_x3f_2284_ = lean_ctor_get(v___y_2271_, 9);
v_suppressElabErrors_2285_ = lean_ctor_get_uint8(v___y_2271_, sizeof(void*)*10);
v_ref_2286_ = l_Lean_replaceRef(v_ref_2269_, v_a_2275_);
lean_dec(v_a_2275_);
lean_inc(v_cancelTk_x3f_2284_);
lean_inc(v_snap_x3f_2283_);
lean_inc(v_currMacroScope_2282_);
lean_inc(v_quotContext_x3f_2281_);
lean_inc(v_macroStack_2280_);
lean_inc(v_cmdPos_2279_);
lean_inc(v_currRecDepth_2278_);
lean_inc_ref(v_fileMap_2277_);
lean_inc_ref(v_fileName_2276_);
v___x_2287_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2287_, 0, v_fileName_2276_);
lean_ctor_set(v___x_2287_, 1, v_fileMap_2277_);
lean_ctor_set(v___x_2287_, 2, v_currRecDepth_2278_);
lean_ctor_set(v___x_2287_, 3, v_cmdPos_2279_);
lean_ctor_set(v___x_2287_, 4, v_macroStack_2280_);
lean_ctor_set(v___x_2287_, 5, v_quotContext_x3f_2281_);
lean_ctor_set(v___x_2287_, 6, v_currMacroScope_2282_);
lean_ctor_set(v___x_2287_, 7, v_ref_2286_);
lean_ctor_set(v___x_2287_, 8, v_snap_x3f_2283_);
lean_ctor_set(v___x_2287_, 9, v_cancelTk_x3f_2284_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*10, v_suppressElabErrors_2285_);
v___x_2288_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2270_, v___x_2287_, v___y_2272_);
lean_dec_ref_known(v___x_2287_, 10);
return v___x_2288_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v_msg_2270_);
v_a_2289_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2274_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2274_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ref_2297_, lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2297_, v_msg_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v_ref_2297_);
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object* v_stx_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_val_2320_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = l_Lean_Syntax_getArg(v_stx_2309_, v___x_2327_);
switch(lean_obj_tag(v___x_2328_))
{
case 2:
{
lean_object* v_val_2329_; 
lean_dec(v_stx_2309_);
v_val_2329_ = lean_ctor_get(v___x_2328_, 1);
lean_inc_ref(v_val_2329_);
lean_dec_ref_known(v___x_2328_, 2);
v_val_2320_ = v_val_2329_;
goto v___jp_2319_;
}
case 1:
{
lean_object* v_kind_2330_; 
v_kind_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_kind_2330_);
if (lean_obj_tag(v_kind_2330_) == 1)
{
lean_object* v_pre_2331_; 
v_pre_2331_ = lean_ctor_get(v_kind_2330_, 0);
lean_inc(v_pre_2331_);
if (lean_obj_tag(v_pre_2331_) == 1)
{
lean_object* v_pre_2332_; 
v_pre_2332_ = lean_ctor_get(v_pre_2331_, 0);
lean_inc(v_pre_2332_);
if (lean_obj_tag(v_pre_2332_) == 1)
{
lean_object* v_pre_2333_; 
v_pre_2333_ = lean_ctor_get(v_pre_2332_, 0);
lean_inc(v_pre_2333_);
if (lean_obj_tag(v_pre_2333_) == 1)
{
lean_object* v_pre_2334_; 
v_pre_2334_ = lean_ctor_get(v_pre_2333_, 0);
if (lean_obj_tag(v_pre_2334_) == 0)
{
lean_object* v_str_2335_; lean_object* v_str_2336_; lean_object* v_str_2337_; lean_object* v_str_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_str_2335_ = lean_ctor_get(v_kind_2330_, 1);
lean_inc_ref(v_str_2335_);
lean_dec_ref_known(v_kind_2330_, 2);
v_str_2336_ = lean_ctor_get(v_pre_2331_, 1);
lean_inc_ref(v_str_2336_);
lean_dec_ref_known(v_pre_2331_, 2);
v_str_2337_ = lean_ctor_get(v_pre_2332_, 1);
lean_inc_ref(v_str_2337_);
lean_dec_ref_known(v_pre_2332_, 2);
v_str_2338_ = lean_ctor_get(v_pre_2333_, 1);
lean_inc_ref(v_str_2338_);
lean_dec_ref_known(v_pre_2333_, 2);
v___x_2339_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2340_ = lean_string_dec_eq(v_str_2338_, v___x_2339_);
lean_dec_ref(v_str_2338_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v_str_2337_);
lean_dec_ref(v_str_2336_);
lean_dec_ref(v_str_2335_);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
else
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2342_ = lean_string_dec_eq(v_str_2337_, v___x_2341_);
lean_dec_ref(v_str_2337_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v_str_2336_);
lean_dec_ref(v_str_2335_);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2344_ = lean_string_dec_eq(v_str_2336_, v___x_2343_);
lean_dec_ref(v_str_2336_);
if (v___x_2344_ == 0)
{
lean_dec_ref(v_str_2335_);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
else
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2346_ = lean_string_dec_eq(v_str_2335_, v___x_2345_);
lean_dec_ref(v_str_2335_);
if (v___x_2346_ == 0)
{
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = l_Lean_Syntax_getArg(v___x_2328_, v___x_2347_);
lean_dec_ref_known(v___x_2328_, 3);
if (lean_obj_tag(v___x_2348_) == 2)
{
lean_object* v_val_2349_; 
lean_dec(v_stx_2309_);
v_val_2349_ = lean_ctor_get(v___x_2348_, 1);
lean_inc_ref(v_val_2349_);
lean_dec_ref_known(v___x_2348_, 2);
v_val_2320_ = v_val_2349_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v___x_2348_);
v___x_2350_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2309_);
v___x_2351_ = l_Lean_MessageData_ofSyntax(v_stx_2309_);
v___x_2352_ = l_Lean_indentD(v___x_2351_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2309_, v___x_2353_, v___y_2310_, v___y_2311_);
lean_dec(v_stx_2309_);
return v___x_2354_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2333_, 2);
lean_dec_ref_known(v_pre_2332_, 2);
lean_dec_ref_known(v_pre_2331_, 2);
lean_dec_ref_known(v_kind_2330_, 2);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
}
else
{
lean_dec_ref_known(v_pre_2332_, 2);
lean_dec(v_pre_2333_);
lean_dec_ref_known(v_pre_2331_, 2);
lean_dec_ref_known(v_kind_2330_, 2);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
}
else
{
lean_dec(v_pre_2332_);
lean_dec_ref_known(v_pre_2331_, 2);
lean_dec_ref_known(v_kind_2330_, 2);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
}
else
{
lean_dec_ref_known(v_kind_2330_, 2);
lean_dec(v_pre_2331_);
lean_dec_ref_known(v___x_2328_, 3);
goto v___jp_2313_;
}
}
else
{
lean_dec_ref_known(v___x_2328_, 3);
lean_dec(v_kind_2330_);
goto v___jp_2313_;
}
}
default: 
{
lean_dec(v___x_2328_);
goto v___jp_2313_;
}
}
v___jp_2313_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2314_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2309_);
v___x_2315_ = l_Lean_MessageData_ofSyntax(v_stx_2309_);
v___x_2316_ = l_Lean_indentD(v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2309_, v___x_2317_, v___y_2310_, v___y_2311_);
lean_dec(v_stx_2309_);
return v___x_2318_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_string_utf8_byte_size(v_val_2320_);
v___x_2323_ = lean_unsigned_to_nat(2u);
v___x_2324_ = lean_nat_sub(v___x_2322_, v___x_2323_);
v___x_2325_ = lean_string_utf8_extract(v_val_2320_, v___x_2321_, v___x_2324_);
lean_dec(v___x_2324_);
lean_dec_ref(v_val_2320_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object* v_stx_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_stx_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(lean_object* v_docOpt_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Lean_Syntax_isNone(v_docOpt_2360_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v_docStx_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2365_ = lean_unsigned_to_nat(0u);
v_docStx_2366_ = l_Lean_Syntax_getArg(v_docOpt_2360_, v___x_2365_);
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = l_Lean_Syntax_getArg(v_docStx_2366_, v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 1)
{
lean_object* v_kind_2397_; 
v_kind_2397_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_kind_2397_);
if (lean_obj_tag(v_kind_2397_) == 1)
{
lean_object* v_pre_2398_; 
v_pre_2398_ = lean_ctor_get(v_kind_2397_, 0);
lean_inc(v_pre_2398_);
if (lean_obj_tag(v_pre_2398_) == 1)
{
lean_object* v_pre_2399_; 
v_pre_2399_ = lean_ctor_get(v_pre_2398_, 0);
lean_inc(v_pre_2399_);
if (lean_obj_tag(v_pre_2399_) == 1)
{
lean_object* v_pre_2400_; 
v_pre_2400_ = lean_ctor_get(v_pre_2399_, 0);
lean_inc(v_pre_2400_);
if (lean_obj_tag(v_pre_2400_) == 1)
{
lean_object* v_pre_2401_; 
v_pre_2401_ = lean_ctor_get(v_pre_2400_, 0);
if (lean_obj_tag(v_pre_2401_) == 0)
{
lean_object* v_str_2402_; lean_object* v_str_2403_; lean_object* v_str_2404_; lean_object* v_str_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_str_2402_ = lean_ctor_get(v_kind_2397_, 1);
lean_inc_ref(v_str_2402_);
lean_dec_ref_known(v_kind_2397_, 2);
v_str_2403_ = lean_ctor_get(v_pre_2398_, 1);
lean_inc_ref(v_str_2403_);
lean_dec_ref_known(v_pre_2398_, 2);
v_str_2404_ = lean_ctor_get(v_pre_2399_, 1);
lean_inc_ref(v_str_2404_);
lean_dec_ref_known(v_pre_2399_, 2);
v_str_2405_ = lean_ctor_get(v_pre_2400_, 1);
lean_inc_ref(v_str_2405_);
lean_dec_ref_known(v_pre_2400_, 2);
v___x_2406_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2407_ = lean_string_dec_eq(v_str_2405_, v___x_2406_);
lean_dec_ref(v_str_2405_);
if (v___x_2407_ == 0)
{
lean_dec_ref(v_str_2404_);
lean_dec_ref(v_str_2403_);
lean_dec_ref(v_str_2402_);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2409_ = lean_string_dec_eq(v_str_2404_, v___x_2408_);
lean_dec_ref(v_str_2404_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v_str_2403_);
lean_dec_ref(v_str_2402_);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2411_ = lean_string_dec_eq(v_str_2403_, v___x_2410_);
lean_dec_ref(v_str_2403_);
if (v___x_2411_ == 0)
{
lean_dec_ref(v_str_2402_);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2413_ = lean_string_dec_eq(v_str_2402_, v___x_2412_);
lean_dec_ref(v_str_2402_);
if (v___x_2413_ == 0)
{
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = l_Lean_Syntax_getArg(v___x_2396_, v___x_2365_);
lean_dec_ref_known(v___x_2396_, 3);
v___x_2415_ = l_Lean_Syntax_isAtom(v___x_2414_);
lean_dec(v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec(v_docStx_2366_);
v___x_2416_ = lean_box(v___x_2364_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
else
{
if (v___x_2364_ == 0)
{
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_docStx_2366_);
v___x_2418_ = lean_box(v___x_2364_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2400_, 2);
lean_dec_ref_known(v_pre_2399_, 2);
lean_dec_ref_known(v_pre_2398_, 2);
lean_dec_ref_known(v_kind_2397_, 2);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
}
else
{
lean_dec(v_pre_2400_);
lean_dec_ref_known(v_pre_2399_, 2);
lean_dec_ref_known(v_pre_2398_, 2);
lean_dec_ref_known(v_kind_2397_, 2);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
}
else
{
lean_dec(v_pre_2399_);
lean_dec_ref_known(v_pre_2398_, 2);
lean_dec_ref_known(v_kind_2397_, 2);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
}
else
{
lean_dec_ref_known(v_kind_2397_, 2);
lean_dec(v_pre_2398_);
lean_dec_ref_known(v___x_2396_, 3);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
}
else
{
lean_dec_ref_known(v___x_2396_, 3);
lean_dec(v_kind_2397_);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
}
else
{
lean_dec(v___x_2396_);
v___y_2368_ = v_a_2361_;
v___y_2369_ = v_a_2362_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_docStx_2366_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2386_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_startInclusive_2378_; lean_object* v_endExclusive_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2375_ = lean_string_utf8_byte_size(v_a_2371_);
v___x_2376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2376_, 0, v_a_2371_);
lean_ctor_set(v___x_2376_, 1, v___x_2365_);
lean_ctor_set(v___x_2376_, 2, v___x_2375_);
v___x_2377_ = l_String_Slice_trimAscii(v___x_2376_);
v_startInclusive_2378_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_startInclusive_2378_);
v_endExclusive_2379_ = lean_ctor_get(v___x_2377_, 2);
lean_inc(v_endExclusive_2379_);
lean_dec_ref(v___x_2377_);
v___x_2380_ = lean_nat_sub(v_endExclusive_2379_, v_startInclusive_2378_);
lean_dec(v_startInclusive_2378_);
lean_dec(v_endExclusive_2379_);
v___x_2381_ = lean_nat_dec_eq(v___x_2380_, v___x_2365_);
lean_dec(v___x_2380_);
v___x_2382_ = lean_box(v___x_2381_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2382_);
v___x_2384_ = v___x_2373_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2370_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2370_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
else
{
uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = 0;
v___x_2421_ = lean_box(v___x_2420_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___boxed(lean_object* v_docOpt_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_docOpt_2423_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(lean_object* v_00_u03b1_2428_, lean_object* v_ref_2429_, lean_object* v_msg_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2429_, v_msg_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_ref_2436_, lean_object* v_msg_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(v_00_u03b1_2435_, v_ref_2436_, v_msg_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v_ref_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2442_, lean_object* v_msg_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2443_, v___y_2444_, v___y_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2448_, lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(v_00_u03b1_2448_, v_msg_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2454_, lean_object* v_macroStack_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2454_, v_macroStack_2455_, v___y_2457_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2460_, lean_object* v_macroStack_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(v_msgData_2460_, v_macroStack_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc(lean_object* v_docOpt_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2466_, v_a_2467_, v_a_2468_);
if (lean_obj_tag(v___x_2470_) == 0)
{
uint8_t v___x_2471_; 
v___x_2471_ = l_Lean_Syntax_isNone(v_docOpt_2466_);
if (v___x_2471_ == 0)
{
return v___x_2470_;
}
else
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2479_; 
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2480_);
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2479_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2479_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_box(v___x_2471_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc___boxed(lean_object* v_docOpt_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Linter_MissingDocs_isMissingDoc(v_docOpt_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_docOpt_2481_);
return v_res_2485_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object* v_as_2496_, size_t v_i_2497_, size_t v_stop_2498_){
_start:
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_usize_dec_eq(v_i_2497_, v_stop_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; uint8_t v___x_2501_; uint8_t v___y_2503_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = 1;
v___x_2507_ = lean_array_uget_borrowed(v_as_2496_, v_i_2497_);
v___x_2508_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2500_);
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2));
lean_inc(v___x_2508_);
v___x_2510_ = l_Lean_Syntax_isOfKind(v___x_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_dec(v___x_2508_);
v___y_2503_ = v___x_2510_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2511_);
lean_dec(v___x_2508_);
v___x_2513_ = l_Lean_Syntax_getId(v___x_2512_);
lean_dec(v___x_2512_);
v___x_2514_ = lean_erase_macro_scopes(v___x_2513_);
v___x_2515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4));
v___x_2516_ = lean_name_eq(v___x_2514_, v___x_2515_);
lean_dec(v___x_2514_);
v___y_2503_ = v___x_2516_;
goto v___jp_2502_;
}
v___jp_2502_:
{
if (v___y_2503_ == 0)
{
size_t v___x_2504_; size_t v___x_2505_; 
v___x_2504_ = ((size_t)1ULL);
v___x_2505_ = lean_usize_add(v_i_2497_, v___x_2504_);
v_i_2497_ = v___x_2505_;
goto _start;
}
else
{
return v___x_2501_;
}
}
}
else
{
uint8_t v___x_2517_; 
v___x_2517_ = 0;
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_stop_2520_){
_start:
{
size_t v_i_boxed_2521_; size_t v_stop_boxed_2522_; uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_i_boxed_2521_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_stop_boxed_2522_ = lean_unbox_usize(v_stop_2520_);
lean_dec(v_stop_2520_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v_as_2518_, v_i_boxed_2521_, v_stop_boxed_2522_);
lean_dec_ref(v_as_2518_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object* v_attrs_2525_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2526_ = lean_unsigned_to_nat(0u);
v___x_2527_ = l_Lean_Syntax_getArg(v_attrs_2525_, v___x_2526_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = l_Lean_Syntax_getArg(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = l_Lean_Syntax_getSepArgs(v___x_2529_);
lean_dec(v___x_2529_);
v___x_2531_ = lean_array_get_size(v___x_2530_);
v___x_2532_ = lean_nat_dec_lt(v___x_2526_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_dec_ref(v___x_2530_);
return v___x_2532_;
}
else
{
if (v___x_2532_ == 0)
{
lean_dec_ref(v___x_2530_);
return v___x_2532_;
}
else
{
size_t v___x_2533_; size_t v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = lean_usize_of_nat(v___x_2531_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v___x_2530_, v___x_2533_, v___x_2534_);
lean_dec_ref(v___x_2530_);
return v___x_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object* v_attrs_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2536_);
lean_dec(v_attrs_2536_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(lean_object* v_as_2545_, size_t v_i_2546_, size_t v_stop_2547_){
_start:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_usize_dec_eq(v_i_2546_, v_stop_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_array_uget_borrowed(v_as_2545_, v_i_2546_);
v___x_2551_ = l_Lean_Syntax_getArg(v___x_2550_, v___x_2549_);
v___x_2552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1));
v___x_2553_ = l_Lean_Syntax_isOfKind(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
size_t v___x_2554_; size_t v___x_2555_; 
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_add(v_i_2546_, v___x_2554_);
v_i_2546_ = v___x_2555_;
goto _start;
}
else
{
return v___x_2553_;
}
}
else
{
uint8_t v___x_2557_; 
v___x_2557_ = 0;
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___boxed(lean_object* v_as_2558_, lean_object* v_i_2559_, lean_object* v_stop_2560_){
_start:
{
size_t v_i_boxed_2561_; size_t v_stop_boxed_2562_; uint8_t v_res_2563_; lean_object* v_r_2564_; 
v_i_boxed_2561_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_stop_boxed_2562_ = lean_unbox_usize(v_stop_2560_);
lean_dec(v_stop_2560_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v_as_2558_, v_i_boxed_2561_, v_stop_boxed_2562_);
lean_dec_ref(v_as_2558_);
v_r_2564_ = lean_box(v_res_2563_);
return v_r_2564_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasTacticAlt(lean_object* v_attrs_2565_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = l_Lean_Syntax_getArg(v_attrs_2565_, v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = l_Lean_Syntax_getArg(v___x_2567_, v___x_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = l_Lean_Syntax_getSepArgs(v___x_2569_);
lean_dec(v___x_2569_);
v___x_2571_ = lean_array_get_size(v___x_2570_);
v___x_2572_ = lean_nat_dec_lt(v___x_2566_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_dec_ref(v___x_2570_);
return v___x_2572_;
}
else
{
if (v___x_2572_ == 0)
{
lean_dec_ref(v___x_2570_);
return v___x_2572_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = ((size_t)0ULL);
v___x_2574_ = lean_usize_of_nat(v___x_2571_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v___x_2570_, v___x_2573_, v___x_2574_);
lean_dec_ref(v___x_2570_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasTacticAlt___boxed(lean_object* v_attrs_2576_){
_start:
{
uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_res_2577_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2576_);
lean_dec(v_attrs_2576_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus(lean_object* v_mods_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_st_ref_get(v_a_2591_);
v___x_2594_ = l_Lean_Elab_Command_getScope___redArg(v_a_2591_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2659_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2659_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2659_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
uint8_t v___y_2605_; lean_object* v_env_2648_; lean_object* v___x_2649_; uint8_t v_isModule_2650_; 
v_env_2648_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_ref(v_env_2648_);
lean_dec(v___x_2593_);
v___x_2649_ = l_Lean_Environment_header(v_env_2648_);
lean_dec_ref(v_env_2648_);
v_isModule_2650_ = lean_ctor_get_uint8(v___x_2649_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2649_);
if (v_isModule_2650_ == 0)
{
lean_dec(v_a_2595_);
goto v___jp_2639_;
}
else
{
uint8_t v_isPublic_2651_; 
v_isPublic_2651_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*10 + 1);
lean_dec(v_a_2595_);
if (v_isPublic_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2652_ = lean_unsigned_to_nat(2u);
v___x_2653_ = l_Lean_Syntax_getArg(v_mods_2589_, v___x_2652_);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = l_Lean_Syntax_getArg(v___x_2653_, v___x_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = l_Lean_Syntax_getKind(v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1));
v___x_2658_ = lean_name_eq(v___x_2656_, v___x_2657_);
lean_dec(v___x_2656_);
if (v___x_2658_ == 0)
{
goto v___jp_2599_;
}
else
{
v___y_2605_ = v_isModule_2650_;
goto v___jp_2604_;
}
}
else
{
goto v___jp_2639_;
}
}
v___jp_2599_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = lean_box(0);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = lean_unsigned_to_nat(1u);
v___x_2607_ = l_Lean_Syntax_getArg(v_mods_2589_, v___x_2606_);
v___x_2608_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v___x_2607_);
lean_dec(v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
lean_del_object(v___x_2597_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = l_Lean_Syntax_getArg(v_mods_2589_, v___x_2609_);
v___x_2611_ = l_Lean_Syntax_isNone(v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_2610_, v_a_2590_, v_a_2591_);
lean_dec(v___x_2610_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2627_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2627_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2627_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_unbox(v_a_2613_);
lean_dec(v_a_2613_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_box(0);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2618_);
v___x_2620_ = v___x_2615_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_box(v___y_2605_);
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2623_);
v___x_2625_ = v___x_2615_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
v_a_2628_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2612_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2612_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec(v___x_2610_);
v___x_2636_ = lean_box(v___x_2608_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
else
{
goto v___jp_2599_;
}
}
v___jp_2639_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2640_ = lean_unsigned_to_nat(2u);
v___x_2641_ = l_Lean_Syntax_getArg(v_mods_2589_, v___x_2640_);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = l_Lean_Syntax_getArg(v___x_2641_, v___x_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = l_Lean_Syntax_getKind(v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_2646_ = lean_name_eq(v___x_2644_, v___x_2645_);
lean_dec(v___x_2644_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; 
v___x_2647_ = 1;
v___y_2605_ = v___x_2647_;
goto v___jp_2604_;
}
else
{
goto v___jp_2599_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v___x_2593_);
v_a_2660_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2594_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2594_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___boxed(lean_object* v_mods_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_mods_2668_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object* v_mods_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2673_, v_a_2674_, v_a_2675_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2692_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2692_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2692_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
if (lean_obj_tag(v_a_2678_) == 0)
{
uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2682_ = 0;
v___x_2683_ = lean_box(v___x_2682_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2683_);
v___x_2685_ = v___x_2680_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
else
{
uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_dec_ref_known(v_a_2678_, 1);
v___x_2687_ = 1;
v___x_2688_ = lean_box(v___x_2687_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2688_);
v___x_2690_ = v___x_2680_;
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
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_a_2693_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2677_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2677_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object* v_mods_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(v_mods_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_mods_2701_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(uint8_t v_isEmpty_2706_, lean_object* v_stx_2707_, lean_object* v_msg_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
if (v_isEmpty_2706_ == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_Linter_MissingDocs_lint(v_stx_2707_, v_msg_2708_, v_a_2709_, v_a_2710_);
return v___x_2712_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2707_, v_msg_2708_, v_a_2709_, v_a_2710_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus___boxed(lean_object* v_isEmpty_2714_, lean_object* v_stx_2715_, lean_object* v_msg_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_isEmpty_boxed_2720_; lean_object* v_res_2721_; 
v_isEmpty_boxed_2720_ = lean_unbox(v_isEmpty_2714_);
v_res_2721_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v_isEmpty_boxed_2720_, v_stx_2715_, v_msg_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(uint8_t v_isEmpty_2722_, lean_object* v_stx_2723_, lean_object* v_msg_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
if (v_isEmpty_2722_ == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2723_, v_msg_2724_, v_a_2725_, v_a_2726_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2723_, v_msg_2724_, v_a_2725_, v_a_2726_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed___boxed(lean_object* v_isEmpty_2730_, lean_object* v_stx_2731_, lean_object* v_msg_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_isEmpty_boxed_2736_; lean_object* v_res_2737_; 
v_isEmpty_boxed_2736_ = lean_unbox(v_isEmpty_2730_);
v_res_2737_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_boxed_2736_, v_stx_2731_, v_msg_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(uint8_t v_isEmpty_2738_, lean_object* v_parent_2739_, lean_object* v_stx_2740_, lean_object* v_msg_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
if (v_isEmpty_2738_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2739_, v_stx_2740_, v_msg_2741_, v_a_2742_, v_a_2743_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2739_, v_stx_2740_, v_msg_2741_, v_a_2742_, v_a_2743_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField___boxed(lean_object* v_isEmpty_2747_, lean_object* v_parent_2748_, lean_object* v_stx_2749_, lean_object* v_msg_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
uint8_t v_isEmpty_boxed_2754_; lean_object* v_res_2755_; 
v_isEmpty_boxed_2754_ = lean_unbox(v_isEmpty_2747_);
v_res_2755_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_isEmpty_boxed_2754_, v_parent_2748_, v_stx_2749_, v_msg_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_parent_2748_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object* v_k_2804_, lean_object* v_id_2805_, uint8_t v_isEmpty_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__1));
v___x_2811_ = lean_name_eq(v_k_2804_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__3));
v___x_2813_ = lean_name_eq(v_k_2804_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__5));
v___x_2815_ = lean_name_eq(v_k_2804_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__7));
v___x_2817_ = lean_name_eq(v_k_2804_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_2819_ = lean_name_eq(v_k_2804_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_2821_ = lean_name_eq(v_k_2804_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_2823_ = lean_name_eq(v_k_2804_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v_id_2805_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__14));
v___x_2827_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2826_, v_a_2807_, v_a_2808_);
return v___x_2827_;
}
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2829_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2828_, v_a_2807_, v_a_2808_);
return v___x_2829_;
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2831_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2830_, v_a_2807_, v_a_2808_);
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__16));
v___x_2833_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2832_, v_a_2807_, v_a_2808_);
return v___x_2833_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__17));
v___x_2835_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2834_, v_a_2807_, v_a_2808_);
return v___x_2835_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__18));
v___x_2837_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2836_, v_a_2807_, v_a_2808_);
return v___x_2837_;
}
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__19));
v___x_2839_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2806_, v_id_2805_, v___x_2838_, v_a_2807_, v_a_2808_);
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object* v_k_2840_, lean_object* v_id_2841_, lean_object* v_isEmpty_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
uint8_t v_isEmpty_boxed_2846_; lean_object* v_res_2847_; 
v_isEmpty_boxed_2846_ = lean_unbox(v_isEmpty_2842_);
v_res_2847_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_2840_, v_id_2841_, v_isEmpty_boxed_2846_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_k_2840_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(lean_object* v_docOpt_2851_, lean_object* v_attrs_2852_, uint8_t v_checkTacticAlt_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
uint8_t v___x_2857_; 
v___x_2857_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2852_);
if (v___x_2857_ == 0)
{
uint8_t v___y_2859_; 
if (v_checkTacticAlt_2853_ == 0)
{
v___y_2859_ = v_checkTacticAlt_2853_;
goto v___jp_2858_;
}
else
{
uint8_t v___x_2887_; 
v___x_2887_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2852_);
if (v___x_2887_ == 0)
{
v___y_2859_ = v___x_2887_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
v___jp_2858_:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_Syntax_isNone(v_docOpt_2851_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
v___x_2861_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2851_, v_a_2854_, v_a_2855_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2875_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2875_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2875_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_unbox(v_a_2862_);
lean_dec(v_a_2862_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_box(0);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2867_);
v___x_2869_ = v___x_2864_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0));
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2871_);
v___x_2873_ = v___x_2864_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2861_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2861_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_box(v___y_2859_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___boxed(lean_object* v_docOpt_2892_, lean_object* v_attrs_2893_, lean_object* v_checkTacticAlt_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
uint8_t v_checkTacticAlt_boxed_2898_; lean_object* v_res_2899_; 
v_checkTacticAlt_boxed_2898_ = lean_unbox(v_checkTacticAlt_2894_);
v_res_2899_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v_docOpt_2892_, v_attrs_2893_, v_checkTacticAlt_boxed_2898_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_attrs_2893_);
lean_dec(v_docOpt_2892_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object* v_rest_2901_, lean_object* v_as_2902_, size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_a_2910_; uint8_t v___x_2914_; 
v___x_2914_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_b_2905_);
return v___x_2915_;
}
else
{
lean_object* v___x_2916_; lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v_a_2917_ = lean_array_uget_borrowed(v_as_2902_, v_i_2904_);
v___x_2918_ = l_Lean_Syntax_getArg(v_a_2917_, v___x_2916_);
v___x_2919_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_2918_, v___y_2906_, v___y_2907_);
lean_dec(v___x_2918_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_box(0);
if (lean_obj_tag(v_a_2920_) == 1)
{
lean_object* v_val_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; 
v_val_2922_ = lean_ctor_get(v_a_2920_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_a_2920_, 1);
v___x_2923_ = lean_unsigned_to_nat(1u);
v___x_2924_ = l_Lean_Syntax_getArg(v_rest_2901_, v___x_2923_);
v___x_2925_ = l_Lean_Syntax_getArg(v___x_2924_, v___x_2916_);
lean_dec(v___x_2924_);
v___x_2926_ = l_Lean_Syntax_getArg(v_a_2917_, v___x_2923_);
v___x_2927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0));
v___x_2928_ = lean_unbox(v_val_2922_);
lean_dec(v_val_2922_);
v___x_2929_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_2928_, v___x_2925_, v___x_2926_, v___x_2927_, v___y_2906_, v___y_2907_);
lean_dec(v___x_2925_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref_known(v___x_2929_, 1);
v_a_2910_ = v___x_2921_;
goto v___jp_2909_;
}
else
{
return v___x_2929_;
}
}
else
{
lean_dec(v_a_2920_);
v_a_2910_ = v___x_2921_;
goto v___jp_2909_;
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2919_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2919_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
v___jp_2909_:
{
size_t v___x_2911_; size_t v___x_2912_; 
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2904_, v___x_2911_);
v_i_2904_ = v___x_2912_;
v_b_2905_ = v_a_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___boxed(lean_object* v_rest_2938_, lean_object* v_as_2939_, lean_object* v_sz_2940_, lean_object* v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
size_t v_sz_boxed_2946_; size_t v_i_boxed_2947_; lean_object* v_res_2948_; 
v_sz_boxed_2946_ = lean_unbox_usize(v_sz_2940_);
lean_dec(v_sz_2940_);
v_i_boxed_2947_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_res_2948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_2938_, v_as_2939_, v_sz_boxed_2946_, v_i_boxed_2947_, v_b_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v_as_2939_);
lean_dec(v_rest_2938_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
if (lean_obj_tag(v_x_2950_) == 0)
{
return v_x_2949_;
}
else
{
lean_object* v_key_2951_; lean_object* v_value_2952_; lean_object* v_tail_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2976_; 
v_key_2951_ = lean_ctor_get(v_x_2950_, 0);
v_value_2952_ = lean_ctor_get(v_x_2950_, 1);
v_tail_2953_ = lean_ctor_get(v_x_2950_, 2);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2950_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2955_ = v_x_2950_;
v_isShared_2956_ = v_isSharedCheck_2976_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_tail_2953_);
lean_inc(v_value_2952_);
lean_inc(v_key_2951_);
lean_dec(v_x_2950_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2976_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; uint64_t v___x_2960_; uint64_t v_fold_2961_; uint64_t v___x_2962_; uint64_t v___x_2963_; uint64_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2957_ = lean_array_get_size(v_x_2949_);
v___x_2958_ = l_String_instHashableRaw_hash(v_key_2951_);
v___x_2959_ = 32ULL;
v___x_2960_ = lean_uint64_shift_right(v___x_2958_, v___x_2959_);
v_fold_2961_ = lean_uint64_xor(v___x_2958_, v___x_2960_);
v___x_2962_ = 16ULL;
v___x_2963_ = lean_uint64_shift_right(v_fold_2961_, v___x_2962_);
v___x_2964_ = lean_uint64_xor(v_fold_2961_, v___x_2963_);
v___x_2965_ = lean_uint64_to_usize(v___x_2964_);
v___x_2966_ = lean_usize_of_nat(v___x_2957_);
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_sub(v___x_2966_, v___x_2967_);
v___x_2969_ = lean_usize_land(v___x_2965_, v___x_2968_);
v___x_2970_ = lean_array_uget_borrowed(v_x_2949_, v___x_2969_);
lean_inc(v___x_2970_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 2, v___x_2970_);
v___x_2972_ = v___x_2955_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_key_2951_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_value_2952_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_array_uset(v_x_2949_, v___x_2969_, v___x_2972_);
v_x_2949_ = v___x_2973_;
v_x_2950_ = v_tail_2953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(lean_object* v_i_2977_, lean_object* v_source_2978_, lean_object* v_target_2979_){
_start:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = lean_array_get_size(v_source_2978_);
v___x_2981_ = lean_nat_dec_lt(v_i_2977_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v_source_2978_);
lean_dec(v_i_2977_);
return v_target_2979_;
}
else
{
lean_object* v_es_2982_; lean_object* v___x_2983_; lean_object* v_source_2984_; lean_object* v_target_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_es_2982_ = lean_array_fget(v_source_2978_, v_i_2977_);
v___x_2983_ = lean_box(0);
v_source_2984_ = lean_array_fset(v_source_2978_, v_i_2977_, v___x_2983_);
v_target_2985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_target_2979_, v_es_2982_);
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = lean_nat_add(v_i_2977_, v___x_2986_);
lean_dec(v_i_2977_);
v_i_2977_ = v___x_2987_;
v_source_2978_ = v_source_2984_;
v_target_2979_ = v_target_2985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(lean_object* v_data_2989_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v_nbuckets_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2990_ = lean_array_get_size(v_data_2989_);
v___x_2991_ = lean_unsigned_to_nat(2u);
v_nbuckets_2992_ = lean_nat_mul(v___x_2990_, v___x_2991_);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_mk_array(v_nbuckets_2992_, v___x_2994_);
v___x_2996_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v___x_2993_, v_data_2989_, v___x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(lean_object* v_a_2997_, lean_object* v_x_2998_){
_start:
{
if (lean_obj_tag(v_x_2998_) == 0)
{
uint8_t v___x_2999_; 
v___x_2999_ = 0;
return v___x_2999_;
}
else
{
lean_object* v_key_3000_; lean_object* v_tail_3001_; uint8_t v___x_3002_; 
v_key_3000_ = lean_ctor_get(v_x_2998_, 0);
v_tail_3001_ = lean_ctor_get(v_x_2998_, 2);
v___x_3002_ = lean_nat_dec_eq(v_key_3000_, v_a_2997_);
if (v___x_3002_ == 0)
{
v_x_2998_ = v_tail_3001_;
goto _start;
}
else
{
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg___boxed(lean_object* v_a_3004_, lean_object* v_x_3005_){
_start:
{
uint8_t v_res_3006_; lean_object* v_r_3007_; 
v_res_3006_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3004_, v_x_3005_);
lean_dec(v_x_3005_);
lean_dec(v_a_3004_);
v_r_3007_ = lean_box(v_res_3006_);
return v_r_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(lean_object* v_m_3008_, lean_object* v_a_3009_, lean_object* v_b_3010_){
_start:
{
lean_object* v_size_3011_; lean_object* v_buckets_3012_; lean_object* v___x_3013_; uint64_t v___x_3014_; uint64_t v___x_3015_; uint64_t v___x_3016_; uint64_t v_fold_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; size_t v___x_3025_; lean_object* v_bkt_3026_; uint8_t v___x_3027_; 
v_size_3011_ = lean_ctor_get(v_m_3008_, 0);
v_buckets_3012_ = lean_ctor_get(v_m_3008_, 1);
v___x_3013_ = lean_array_get_size(v_buckets_3012_);
v___x_3014_ = l_String_instHashableRaw_hash(v_a_3009_);
v___x_3015_ = 32ULL;
v___x_3016_ = lean_uint64_shift_right(v___x_3014_, v___x_3015_);
v_fold_3017_ = lean_uint64_xor(v___x_3014_, v___x_3016_);
v___x_3018_ = 16ULL;
v___x_3019_ = lean_uint64_shift_right(v_fold_3017_, v___x_3018_);
v___x_3020_ = lean_uint64_xor(v_fold_3017_, v___x_3019_);
v___x_3021_ = lean_uint64_to_usize(v___x_3020_);
v___x_3022_ = lean_usize_of_nat(v___x_3013_);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_sub(v___x_3022_, v___x_3023_);
v___x_3025_ = lean_usize_land(v___x_3021_, v___x_3024_);
v_bkt_3026_ = lean_array_uget_borrowed(v_buckets_3012_, v___x_3025_);
v___x_3027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3009_, v_bkt_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3048_; 
lean_inc_ref(v_buckets_3012_);
lean_inc(v_size_3011_);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_m_3008_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; lean_object* v_unused_3050_; 
v_unused_3049_ = lean_ctor_get(v_m_3008_, 1);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v_m_3008_, 0);
lean_dec(v_unused_3050_);
v___x_3029_ = v_m_3008_;
v_isShared_3030_ = v_isSharedCheck_3048_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v_m_3008_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3048_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v_size_x27_3032_; lean_object* v___x_3033_; lean_object* v_buckets_x27_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3031_ = lean_unsigned_to_nat(1u);
v_size_x27_3032_ = lean_nat_add(v_size_3011_, v___x_3031_);
lean_dec(v_size_3011_);
lean_inc(v_bkt_3026_);
v___x_3033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3009_);
lean_ctor_set(v___x_3033_, 1, v_b_3010_);
lean_ctor_set(v___x_3033_, 2, v_bkt_3026_);
v_buckets_x27_3034_ = lean_array_uset(v_buckets_3012_, v___x_3025_, v___x_3033_);
v___x_3035_ = lean_unsigned_to_nat(4u);
v___x_3036_ = lean_nat_mul(v_size_x27_3032_, v___x_3035_);
v___x_3037_ = lean_unsigned_to_nat(3u);
v___x_3038_ = lean_nat_div(v___x_3036_, v___x_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_array_get_size(v_buckets_x27_3034_);
v___x_3040_ = lean_nat_dec_le(v___x_3038_, v___x_3039_);
lean_dec(v___x_3038_);
if (v___x_3040_ == 0)
{
lean_object* v_val_3041_; lean_object* v___x_3043_; 
v_val_3041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_buckets_x27_3034_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v_val_3041_);
lean_ctor_set(v___x_3029_, 0, v_size_x27_3032_);
v___x_3043_ = v___x_3029_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_size_x27_3032_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_val_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v___x_3046_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v_buckets_x27_3034_);
lean_ctor_set(v___x_3029_, 0, v_size_x27_3032_);
v___x_3046_ = v___x_3029_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_size_x27_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_buckets_x27_3034_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_dec(v_b_3010_);
lean_dec(v_a_3009_);
return v_m_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(uint8_t v___x_3051_, lean_object* v_x_3052_, lean_object* v_info_3053_, lean_object* v_s_3054_){
_start:
{
if (lean_obj_tag(v_info_3053_) == 12)
{
lean_object* v_i_3055_; lean_object* v___x_3056_; 
v_i_3055_ = lean_ctor_get(v_info_3053_, 0);
v___x_3056_ = l_Lean_Syntax_getRange_x3f(v_i_3055_, v___x_3051_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v_start_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_start_3058_ = lean_ctor_get(v_val_3057_, 0);
lean_inc(v_start_3058_);
lean_dec(v_val_3057_);
v___x_3059_ = lean_box(0);
v___x_3060_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_s_3054_, v_start_3058_, v___x_3059_);
return v___x_3060_;
}
else
{
lean_dec(v___x_3056_);
return v_s_3054_;
}
}
else
{
return v_s_3054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed(lean_object* v___x_3061_, lean_object* v_x_3062_, lean_object* v_info_3063_, lean_object* v_s_3064_){
_start:
{
uint8_t v___x_11624__boxed_3065_; lean_object* v_res_3066_; 
v___x_11624__boxed_3065_ = lean_unbox(v___x_3061_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(v___x_11624__boxed_3065_, v_x_3062_, v_info_3063_, v_s_3064_);
lean_dec_ref(v_info_3063_);
lean_dec_ref(v_x_3062_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(uint8_t v___x_3067_, lean_object* v_as_3068_, size_t v_i_3069_, size_t v_stop_3070_, lean_object* v_b_3071_){
_start:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_usize_dec_eq(v_i_3069_, v_stop_3070_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; 
v___x_3073_ = lean_box(v___x_3067_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3074_, 0, v___x_3073_);
v___x_3075_ = lean_array_uget_borrowed(v_as_3068_, v_i_3069_);
lean_inc(v___x_3075_);
v___x_3076_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_3074_, v_b_3071_, v___x_3075_);
v___x_3077_ = ((size_t)1ULL);
v___x_3078_ = lean_usize_add(v_i_3069_, v___x_3077_);
v_i_3069_ = v___x_3078_;
v_b_3071_ = v___x_3076_;
goto _start;
}
else
{
return v_b_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___boxed(lean_object* v___x_3080_, lean_object* v_as_3081_, lean_object* v_i_3082_, lean_object* v_stop_3083_, lean_object* v_b_3084_){
_start:
{
uint8_t v___x_11640__boxed_3085_; size_t v_i_boxed_3086_; size_t v_stop_boxed_3087_; lean_object* v_res_3088_; 
v___x_11640__boxed_3085_ = lean_unbox(v___x_3080_);
v_i_boxed_3086_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_stop_boxed_3087_ = lean_unbox_usize(v_stop_3083_);
lean_dec(v_stop_3083_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_11640__boxed_3085_, v_as_3081_, v_i_boxed_3086_, v_stop_boxed_3087_, v_b_3084_);
lean_dec_ref(v_as_3081_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(uint8_t v___x_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 0)
{
lean_object* v_cs_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_cs_3092_ = lean_ctor_get(v_x_3090_, 0);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_array_get_size(v_cs_3092_);
v___x_3095_ = lean_nat_dec_lt(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
return v_x_3091_;
}
else
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_nat_dec_le(v___x_3094_, v___x_3094_);
if (v___x_3096_ == 0)
{
if (v___x_3095_ == 0)
{
return v_x_3091_;
}
else
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = lean_usize_of_nat(v___x_3094_);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3089_, v_cs_3092_, v___x_3097_, v___x_3098_, v_x_3091_);
return v___x_3099_;
}
}
else
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = lean_usize_of_nat(v___x_3094_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3089_, v_cs_3092_, v___x_3100_, v___x_3101_, v_x_3091_);
return v___x_3102_;
}
}
}
else
{
lean_object* v_vs_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_vs_3103_ = lean_ctor_get(v_x_3090_, 0);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_array_get_size(v_vs_3103_);
v___x_3106_ = lean_nat_dec_lt(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
return v_x_3091_;
}
else
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_nat_dec_le(v___x_3105_, v___x_3105_);
if (v___x_3107_ == 0)
{
if (v___x_3106_ == 0)
{
return v_x_3091_;
}
else
{
size_t v___x_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = lean_usize_of_nat(v___x_3105_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3089_, v_vs_3103_, v___x_3108_, v___x_3109_, v_x_3091_);
return v___x_3110_;
}
}
else
{
size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = lean_usize_of_nat(v___x_3105_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3089_, v_vs_3103_, v___x_3111_, v___x_3112_, v_x_3091_);
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(uint8_t v___x_3114_, lean_object* v_as_3115_, size_t v_i_3116_, size_t v_stop_3117_, lean_object* v_b_3118_){
_start:
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_usize_dec_eq(v_i_3116_, v_stop_3117_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; size_t v___x_3122_; size_t v___x_3123_; 
v___x_3120_ = lean_array_uget_borrowed(v_as_3115_, v_i_3116_);
v___x_3121_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3114_, v___x_3120_, v_b_3118_);
v___x_3122_ = ((size_t)1ULL);
v___x_3123_ = lean_usize_add(v_i_3116_, v___x_3122_);
v_i_3116_ = v___x_3123_;
v_b_3118_ = v___x_3121_;
goto _start;
}
else
{
return v_b_3118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7___boxed(lean_object* v___x_3125_, lean_object* v_as_3126_, lean_object* v_i_3127_, lean_object* v_stop_3128_, lean_object* v_b_3129_){
_start:
{
uint8_t v___x_11659__boxed_3130_; size_t v_i_boxed_3131_; size_t v_stop_boxed_3132_; lean_object* v_res_3133_; 
v___x_11659__boxed_3130_ = lean_unbox(v___x_3125_);
v_i_boxed_3131_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_stop_boxed_3132_ = lean_unbox_usize(v_stop_3128_);
lean_dec(v_stop_3128_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_11659__boxed_3130_, v_as_3126_, v_i_boxed_3131_, v_stop_boxed_3132_, v_b_3129_);
lean_dec_ref(v_as_3126_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7___boxed(lean_object* v___x_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_){
_start:
{
uint8_t v___x_11666__boxed_3137_; lean_object* v_res_3138_; 
v___x_11666__boxed_3137_ = lean_unbox(v___x_3134_);
v_res_3138_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_11666__boxed_3137_, v_x_3135_, v_x_3136_);
lean_dec_ref(v_x_3135_);
return v_res_3138_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(uint8_t v___x_3140_, lean_object* v_x_3141_, size_t v_x_3142_, size_t v_x_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 0)
{
lean_object* v_cs_3145_; lean_object* v___x_3146_; size_t v___x_3147_; lean_object* v_j_3148_; lean_object* v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; size_t v___x_3152_; size_t v___x_3153_; size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_cs_3145_ = lean_ctor_get(v_x_3141_, 0);
v___x_3146_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0);
v___x_3147_ = lean_usize_shift_right(v_x_3142_, v_x_3143_);
v_j_3148_ = lean_usize_to_nat(v___x_3147_);
v___x_3149_ = lean_array_get_borrowed(v___x_3146_, v_cs_3145_, v_j_3148_);
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_shift_left(v___x_3150_, v_x_3143_);
v___x_3152_ = lean_usize_sub(v___x_3151_, v___x_3150_);
v___x_3153_ = lean_usize_land(v_x_3142_, v___x_3152_);
v___x_3154_ = ((size_t)5ULL);
v___x_3155_ = lean_usize_sub(v_x_3143_, v___x_3154_);
v___x_3156_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3140_, v___x_3149_, v___x_3153_, v___x_3155_, v_x_3144_);
v___x_3157_ = lean_unsigned_to_nat(1u);
v___x_3158_ = lean_nat_add(v_j_3148_, v___x_3157_);
lean_dec(v_j_3148_);
v___x_3159_ = lean_array_get_size(v_cs_3145_);
v___x_3160_ = lean_nat_dec_lt(v___x_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_dec(v___x_3158_);
return v___x_3156_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_nat_dec_le(v___x_3159_, v___x_3159_);
if (v___x_3161_ == 0)
{
if (v___x_3160_ == 0)
{
lean_dec(v___x_3158_);
return v___x_3156_;
}
else
{
size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_usize_of_nat(v___x_3158_);
lean_dec(v___x_3158_);
v___x_3163_ = lean_usize_of_nat(v___x_3159_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3140_, v_cs_3145_, v___x_3162_, v___x_3163_, v___x_3156_);
return v___x_3164_;
}
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_usize_of_nat(v___x_3158_);
lean_dec(v___x_3158_);
v___x_3166_ = lean_usize_of_nat(v___x_3159_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3140_, v_cs_3145_, v___x_3165_, v___x_3166_, v___x_3156_);
return v___x_3167_;
}
}
}
else
{
lean_object* v_vs_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_vs_3168_ = lean_ctor_get(v_x_3141_, 0);
v___x_3169_ = lean_usize_to_nat(v_x_3142_);
v___x_3170_ = lean_array_get_size(v_vs_3168_);
v___x_3171_ = lean_nat_dec_lt(v___x_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_dec(v___x_3169_);
return v_x_3144_;
}
else
{
uint8_t v___x_3172_; 
v___x_3172_ = lean_nat_dec_le(v___x_3170_, v___x_3170_);
if (v___x_3172_ == 0)
{
if (v___x_3171_ == 0)
{
lean_dec(v___x_3169_);
return v_x_3144_;
}
else
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_usize_of_nat(v___x_3169_);
lean_dec(v___x_3169_);
v___x_3174_ = lean_usize_of_nat(v___x_3170_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3140_, v_vs_3168_, v___x_3173_, v___x_3174_, v_x_3144_);
return v___x_3175_;
}
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_usize_of_nat(v___x_3169_);
lean_dec(v___x_3169_);
v___x_3177_ = lean_usize_of_nat(v___x_3170_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3140_, v_vs_3168_, v___x_3176_, v___x_3177_, v_x_3144_);
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___boxed(lean_object* v___x_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_, lean_object* v_x_3182_, lean_object* v_x_3183_){
_start:
{
uint8_t v___x_11729__boxed_3184_; size_t v_x_11731__boxed_3185_; size_t v_x_11732__boxed_3186_; lean_object* v_res_3187_; 
v___x_11729__boxed_3184_ = lean_unbox(v___x_3179_);
v_x_11731__boxed_3185_ = lean_unbox_usize(v_x_3181_);
lean_dec(v_x_3181_);
v_x_11732__boxed_3186_ = lean_unbox_usize(v_x_3182_);
lean_dec(v_x_3182_);
v_res_3187_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_11729__boxed_3184_, v_x_3180_, v_x_11731__boxed_3185_, v_x_11732__boxed_3186_, v_x_3183_);
lean_dec_ref(v_x_3180_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(uint8_t v___x_3188_, lean_object* v_t_3189_, lean_object* v_init_3190_, lean_object* v_start_3191_){
_start:
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_nat_dec_eq(v_start_3191_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v_root_3194_; lean_object* v_tail_3195_; size_t v_shift_3196_; lean_object* v_tailOff_3197_; uint8_t v___x_3198_; 
v_root_3194_ = lean_ctor_get(v_t_3189_, 0);
v_tail_3195_ = lean_ctor_get(v_t_3189_, 1);
v_shift_3196_ = lean_ctor_get_usize(v_t_3189_, 4);
v_tailOff_3197_ = lean_ctor_get(v_t_3189_, 3);
v___x_3198_ = lean_nat_dec_le(v_tailOff_3197_, v_start_3191_);
if (v___x_3198_ == 0)
{
size_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3199_ = lean_usize_of_nat(v_start_3191_);
v___x_3200_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3188_, v_root_3194_, v___x_3199_, v_shift_3196_, v_init_3190_);
v___x_3201_ = lean_array_get_size(v_tail_3195_);
v___x_3202_ = lean_nat_dec_lt(v___x_3192_, v___x_3201_);
if (v___x_3202_ == 0)
{
return v___x_3200_;
}
else
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_nat_dec_le(v___x_3201_, v___x_3201_);
if (v___x_3203_ == 0)
{
if (v___x_3202_ == 0)
{
return v___x_3200_;
}
else
{
size_t v___x_3204_; size_t v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = ((size_t)0ULL);
v___x_3205_ = lean_usize_of_nat(v___x_3201_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3195_, v___x_3204_, v___x_3205_, v___x_3200_);
return v___x_3206_;
}
}
else
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((size_t)0ULL);
v___x_3208_ = lean_usize_of_nat(v___x_3201_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3195_, v___x_3207_, v___x_3208_, v___x_3200_);
return v___x_3209_;
}
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = lean_nat_sub(v_start_3191_, v_tailOff_3197_);
v___x_3211_ = lean_array_get_size(v_tail_3195_);
v___x_3212_ = lean_nat_dec_lt(v___x_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_dec(v___x_3210_);
return v_init_3190_;
}
else
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_nat_dec_le(v___x_3211_, v___x_3211_);
if (v___x_3213_ == 0)
{
if (v___x_3212_ == 0)
{
lean_dec(v___x_3210_);
return v_init_3190_;
}
else
{
size_t v___x_3214_; size_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = lean_usize_of_nat(v___x_3210_);
lean_dec(v___x_3210_);
v___x_3215_ = lean_usize_of_nat(v___x_3211_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3195_, v___x_3214_, v___x_3215_, v_init_3190_);
return v___x_3216_;
}
}
else
{
size_t v___x_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_usize_of_nat(v___x_3210_);
lean_dec(v___x_3210_);
v___x_3218_ = lean_usize_of_nat(v___x_3211_);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3195_, v___x_3217_, v___x_3218_, v_init_3190_);
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_root_3220_; lean_object* v_tail_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_root_3220_ = lean_ctor_get(v_t_3189_, 0);
v_tail_3221_ = lean_ctor_get(v_t_3189_, 1);
v___x_3222_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3188_, v_root_3220_, v_init_3190_);
v___x_3223_ = lean_array_get_size(v_tail_3221_);
v___x_3224_ = lean_nat_dec_lt(v___x_3192_, v___x_3223_);
if (v___x_3224_ == 0)
{
return v___x_3222_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_nat_dec_le(v___x_3223_, v___x_3223_);
if (v___x_3225_ == 0)
{
if (v___x_3224_ == 0)
{
return v___x_3222_;
}
else
{
size_t v___x_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = ((size_t)0ULL);
v___x_3227_ = lean_usize_of_nat(v___x_3223_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3221_, v___x_3226_, v___x_3227_, v___x_3222_);
return v___x_3228_;
}
}
else
{
size_t v___x_3229_; size_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = ((size_t)0ULL);
v___x_3230_ = lean_usize_of_nat(v___x_3223_);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3188_, v_tail_3221_, v___x_3229_, v___x_3230_, v___x_3222_);
return v___x_3231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3___boxed(lean_object* v___x_3232_, lean_object* v_t_3233_, lean_object* v_init_3234_, lean_object* v_start_3235_){
_start:
{
uint8_t v___x_11811__boxed_3236_; lean_object* v_res_3237_; 
v___x_11811__boxed_3236_ = lean_unbox(v___x_3232_);
v_res_3237_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_11811__boxed_3236_, v_t_3233_, v_init_3234_, v_start_3235_);
lean_dec(v_start_3235_);
lean_dec_ref(v_t_3233_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object* v_rest_3239_, uint8_t v___x_3240_, uint8_t v___y_3241_, lean_object* v_as_3242_, size_t v_sz_3243_, size_t v_i_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_a_3250_; uint8_t v___x_3254_; 
v___x_3254_ = lean_usize_dec_lt(v_i_3244_, v_sz_3243_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_b_3245_);
return v___x_3255_;
}
else
{
lean_object* v___x_3256_; lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3256_ = lean_unsigned_to_nat(0u);
v_a_3257_ = lean_array_uget_borrowed(v_as_3242_, v_i_3244_);
v___x_3258_ = l_Lean_Syntax_getArg(v_a_3257_, v___x_3256_);
v___x_3259_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3258_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___y_3265_; lean_object* v___x_3272_; uint8_t v___y_3288_; uint8_t v___x_3290_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_unsigned_to_nat(2u);
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3272_ = l_Lean_Syntax_getArg(v_a_3257_, v___x_3262_);
v___x_3290_ = l_Lean_Syntax_isNone(v___x_3258_);
lean_dec(v___x_3258_);
if (v___x_3290_ == 0)
{
v___y_3288_ = v___y_3241_;
goto v___jp_3287_;
}
else
{
v___y_3288_ = v___x_3240_;
goto v___jp_3287_;
}
v___jp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3266_ = l_Lean_Syntax_getArg(v_rest_3239_, v___x_3263_);
v___x_3267_ = l_Lean_Syntax_getArg(v___x_3266_, v___x_3256_);
lean_dec(v___x_3266_);
v___x_3268_ = lean_unsigned_to_nat(3u);
v___x_3269_ = l_Lean_Syntax_getArg(v_a_3257_, v___x_3268_);
v___x_3270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0));
v___x_3271_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___y_3265_, v___x_3267_, v___x_3269_, v___x_3270_, v___y_3246_, v___y_3247_);
lean_dec(v___x_3267_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_dec_ref_known(v___x_3271_, 1);
v_a_3250_ = v___x_3261_;
goto v___jp_3249_;
}
else
{
return v___x_3271_;
}
}
v___jp_3273_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3272_, v___y_3246_, v___y_3247_);
lean_dec(v___x_3272_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
if (lean_obj_tag(v_a_3275_) == 1)
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
if (v___x_3276_ == 0)
{
lean_object* v_val_3277_; uint8_t v___x_3278_; 
v_val_3277_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v_a_3275_, 1);
v___x_3278_ = lean_unbox(v_val_3277_);
lean_dec(v_val_3277_);
v___y_3265_ = v___x_3278_;
goto v___jp_3264_;
}
else
{
lean_dec_ref_known(v_a_3275_, 1);
v___y_3265_ = v___x_3254_;
goto v___jp_3264_;
}
}
else
{
lean_dec(v_a_3275_);
lean_dec(v_a_3260_);
v_a_3250_ = v___x_3261_;
goto v___jp_3249_;
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec(v_a_3260_);
v_a_3279_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3274_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3274_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
v___jp_3287_:
{
if (v___y_3288_ == 0)
{
goto v___jp_3273_;
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_unbox(v_a_3260_);
if (v___x_3289_ == 0)
{
lean_dec(v___x_3272_);
lean_dec(v_a_3260_);
v_a_3250_ = v___x_3261_;
goto v___jp_3249_;
}
else
{
if (v___x_3240_ == 0)
{
goto v___jp_3273_;
}
else
{
lean_dec(v___x_3272_);
lean_dec(v_a_3260_);
v_a_3250_ = v___x_3261_;
goto v___jp_3249_;
}
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v___x_3258_);
v_a_3291_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3259_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3259_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
v___jp_3249_:
{
size_t v___x_3251_; size_t v___x_3252_; 
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3244_, v___x_3251_);
v_i_3244_ = v___x_3252_;
v_b_3245_ = v_a_3250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object* v_rest_3299_, lean_object* v___x_3300_, lean_object* v___y_3301_, lean_object* v_as_3302_, lean_object* v_sz_3303_, lean_object* v_i_3304_, lean_object* v_b_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v___x_11884__boxed_3309_; uint8_t v___y_11885__boxed_3310_; size_t v_sz_boxed_3311_; size_t v_i_boxed_3312_; lean_object* v_res_3313_; 
v___x_11884__boxed_3309_ = lean_unbox(v___x_3300_);
v___y_11885__boxed_3310_ = lean_unbox(v___y_3301_);
v_sz_boxed_3311_ = lean_unbox_usize(v_sz_3303_);
lean_dec(v_sz_3303_);
v_i_boxed_3312_ = lean_unbox_usize(v_i_3304_);
lean_dec(v_i_3304_);
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3299_, v___x_11884__boxed_3309_, v___y_11885__boxed_3310_, v_as_3302_, v_sz_boxed_3311_, v_i_boxed_3312_, v_b_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_as_3302_);
lean_dec(v_rest_3299_);
return v_res_3313_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(lean_object* v_m_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_buckets_3316_; lean_object* v___x_3317_; uint64_t v___x_3318_; uint64_t v___x_3319_; uint64_t v___x_3320_; uint64_t v_fold_3321_; uint64_t v___x_3322_; uint64_t v___x_3323_; uint64_t v___x_3324_; size_t v___x_3325_; size_t v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; size_t v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v_buckets_3316_ = lean_ctor_get(v_m_3314_, 1);
v___x_3317_ = lean_array_get_size(v_buckets_3316_);
v___x_3318_ = l_String_instHashableRaw_hash(v_a_3315_);
v___x_3319_ = 32ULL;
v___x_3320_ = lean_uint64_shift_right(v___x_3318_, v___x_3319_);
v_fold_3321_ = lean_uint64_xor(v___x_3318_, v___x_3320_);
v___x_3322_ = 16ULL;
v___x_3323_ = lean_uint64_shift_right(v_fold_3321_, v___x_3322_);
v___x_3324_ = lean_uint64_xor(v_fold_3321_, v___x_3323_);
v___x_3325_ = lean_uint64_to_usize(v___x_3324_);
v___x_3326_ = lean_usize_of_nat(v___x_3317_);
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_sub(v___x_3326_, v___x_3327_);
v___x_3329_ = lean_usize_land(v___x_3325_, v___x_3328_);
v___x_3330_ = lean_array_uget_borrowed(v_buckets_3316_, v___x_3329_);
v___x_3331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3315_, v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg___boxed(lean_object* v_m_3332_, lean_object* v_a_3333_){
_start:
{
uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_res_3334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_m_3332_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(uint8_t v_val_3337_, lean_object* v___x_3338_, uint8_t v___x_3339_, lean_object* v___x_3340_, lean_object* v_as_3341_, size_t v_sz_3342_, size_t v_i_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_a_3349_; uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_lt(v_i_3343_, v_sz_3342_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_b_3344_);
return v___x_3354_;
}
else
{
lean_object* v___x_3355_; lean_object* v_a_3356_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___x_3362_; 
v___x_3355_ = lean_box(0);
v_a_3356_ = lean_array_uget_borrowed(v_as_3341_, v_i_3343_);
v___x_3362_ = l_Lean_Syntax_getRange_x3f(v_a_3356_, v___x_3339_);
if (lean_obj_tag(v___x_3362_) == 1)
{
lean_object* v_val_3363_; lean_object* v_start_3364_; uint8_t v___x_3365_; 
v_val_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_val_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v_start_3364_ = lean_ctor_get(v_val_3363_, 0);
lean_inc(v_start_3364_);
lean_dec(v_val_3363_);
v___x_3365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3340_, v_start_3364_);
lean_dec(v_start_3364_);
if (v___x_3365_ == 0)
{
v___y_3358_ = v___y_3345_;
v___y_3359_ = v___y_3346_;
goto v___jp_3357_;
}
else
{
v_a_3349_ = v___x_3355_;
goto v___jp_3348_;
}
}
else
{
lean_dec(v___x_3362_);
v___y_3358_ = v___y_3345_;
v___y_3359_ = v___y_3346_;
goto v___jp_3357_;
}
v___jp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3356_);
v___x_3361_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3337_, v___x_3338_, v_a_3356_, v___x_3360_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_dec_ref_known(v___x_3361_, 1);
v_a_3349_ = v___x_3355_;
goto v___jp_3348_;
}
else
{
return v___x_3361_;
}
}
}
v___jp_3348_:
{
size_t v___x_3350_; size_t v___x_3351_; 
v___x_3350_ = ((size_t)1ULL);
v___x_3351_ = lean_usize_add(v_i_3343_, v___x_3350_);
v_i_3343_ = v___x_3351_;
v_b_3344_ = v_a_3349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___boxed(lean_object* v_val_3366_, lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_as_3370_, lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v_val_12033__boxed_3377_; uint8_t v___x_12035__boxed_3378_; size_t v_sz_boxed_3379_; size_t v_i_boxed_3380_; lean_object* v_res_3381_; 
v_val_12033__boxed_3377_ = lean_unbox(v_val_3366_);
v___x_12035__boxed_3378_ = lean_unbox(v___x_3368_);
v_sz_boxed_3379_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3380_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_12033__boxed_3377_, v___x_3367_, v___x_12035__boxed_3378_, v___x_3369_, v_as_3370_, v_sz_boxed_3379_, v_i_boxed_3380_, v_b_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v_as_3370_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3367_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(lean_object* v___x_3382_, uint8_t v___x_3383_, lean_object* v___x_3384_, uint8_t v_val_3385_, lean_object* v_as_3386_, size_t v_sz_3387_, size_t v_i_3388_, lean_object* v_b_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_a_3394_; uint8_t v___x_3398_; 
v___x_3398_ = lean_usize_dec_lt(v_i_3388_, v_sz_3387_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v_b_3389_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v_a_3401_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___x_3407_; 
v___x_3400_ = lean_box(0);
v_a_3401_ = lean_array_uget_borrowed(v_as_3386_, v_i_3388_);
v___x_3407_ = l_Lean_Syntax_getRange_x3f(v_a_3401_, v___x_3383_);
if (lean_obj_tag(v___x_3407_) == 1)
{
lean_object* v_val_3408_; lean_object* v_start_3409_; uint8_t v___x_3410_; 
v_val_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_val_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v_start_3409_ = lean_ctor_get(v_val_3408_, 0);
lean_inc(v_start_3409_);
lean_dec(v_val_3408_);
v___x_3410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3384_, v_start_3409_);
lean_dec(v_start_3409_);
if (v___x_3410_ == 0)
{
v___y_3403_ = v___y_3390_;
v___y_3404_ = v___y_3391_;
goto v___jp_3402_;
}
else
{
v_a_3394_ = v___x_3400_;
goto v___jp_3393_;
}
}
else
{
lean_dec(v___x_3407_);
v___y_3403_ = v___y_3390_;
v___y_3404_ = v___y_3391_;
goto v___jp_3402_;
}
v___jp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3401_);
v___x_3406_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3385_, v___x_3382_, v_a_3401_, v___x_3405_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v_a_3394_ = v___x_3400_;
goto v___jp_3393_;
}
else
{
return v___x_3406_;
}
}
}
v___jp_3393_:
{
size_t v___x_3395_; size_t v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = ((size_t)1ULL);
v___x_3396_ = lean_usize_add(v_i_3388_, v___x_3395_);
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_3385_, v___x_3382_, v___x_3383_, v___x_3384_, v_as_3386_, v_sz_3387_, v___x_3396_, v_a_3394_, v___y_3390_, v___y_3391_);
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5___boxed(lean_object* v___x_3411_, lean_object* v___x_3412_, lean_object* v___x_3413_, lean_object* v_val_3414_, lean_object* v_as_3415_, lean_object* v_sz_3416_, lean_object* v_i_3417_, lean_object* v_b_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
uint8_t v___x_12091__boxed_3422_; uint8_t v_val_12093__boxed_3423_; size_t v_sz_boxed_3424_; size_t v_i_boxed_3425_; lean_object* v_res_3426_; 
v___x_12091__boxed_3422_ = lean_unbox(v___x_3412_);
v_val_12093__boxed_3423_ = lean_unbox(v_val_3414_);
v_sz_boxed_3424_ = lean_unbox_usize(v_sz_3416_);
lean_dec(v_sz_3416_);
v_i_boxed_3425_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3411_, v___x_12091__boxed_3422_, v___x_3413_, v_val_12093__boxed_3423_, v_as_3415_, v_sz_boxed_3424_, v_i_boxed_3425_, v_b_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v_as_3415_);
lean_dec_ref(v___x_3413_);
lean_dec(v___x_3411_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(lean_object* v___x_3433_, uint8_t v___x_3434_, lean_object* v___x_3435_, lean_object* v_as_3436_, size_t v_sz_3437_, size_t v_i_3438_, lean_object* v_b_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_a_3444_; uint8_t v___x_3448_; 
v___x_3448_ = lean_usize_dec_lt(v_i_3438_, v_sz_3437_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_b_3439_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v_a_3451_ = lean_array_uget_borrowed(v_as_3436_, v_i_3438_);
v___x_3452_ = l_Lean_Syntax_getArg(v_a_3451_, v___x_3450_);
v___x_3453_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3452_, v___y_3440_, v___y_3441_);
lean_dec(v___x_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = lean_box(0);
if (lean_obj_tag(v_a_3454_) == 1)
{
lean_object* v_val_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v_val_3456_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v_a_3454_, 1);
lean_inc(v_a_3451_);
v___x_3457_ = l_Lean_Syntax_getKind(v_a_3451_);
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3459_ = lean_name_eq(v___x_3457_, v___x_3458_);
lean_dec(v___x_3457_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; size_t v_sz_3463_; size_t v___x_3464_; uint8_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3460_ = lean_unsigned_to_nat(2u);
v___x_3461_ = l_Lean_Syntax_getArg(v_a_3451_, v___x_3460_);
v___x_3462_ = l_Lean_Syntax_getArgs(v___x_3461_);
lean_dec(v___x_3461_);
v_sz_3463_ = lean_array_size(v___x_3462_);
v___x_3464_ = ((size_t)0ULL);
v___x_3465_ = lean_unbox(v_val_3456_);
lean_dec(v_val_3456_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3433_, v___x_3434_, v___x_3435_, v___x_3465_, v___x_3462_, v_sz_3463_, v___x_3464_, v___x_3455_, v___y_3440_, v___y_3441_);
lean_dec_ref(v___x_3462_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_dec_ref_known(v___x_3466_, 1);
v_a_3444_ = v___x_3455_;
goto v___jp_3443_;
}
else
{
return v___x_3466_;
}
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___x_3475_; 
v___x_3467_ = lean_unsigned_to_nat(1u);
v___x_3468_ = l_Lean_Syntax_getArg(v_a_3451_, v___x_3467_);
v___x_3475_ = l_Lean_Syntax_getRange_x3f(v___x_3468_, v___x_3434_);
if (lean_obj_tag(v___x_3475_) == 1)
{
lean_object* v_val_3476_; lean_object* v_start_3477_; uint8_t v___x_3478_; 
v_val_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v_start_3477_ = lean_ctor_get(v_val_3476_, 0);
lean_inc(v_start_3477_);
lean_dec(v_val_3476_);
v___x_3478_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3435_, v_start_3477_);
lean_dec(v_start_3477_);
if (v___x_3478_ == 0)
{
v___y_3470_ = v___y_3440_;
v___y_3471_ = v___y_3441_;
goto v___jp_3469_;
}
else
{
lean_dec(v___x_3468_);
lean_dec(v_val_3456_);
v_a_3444_ = v___x_3455_;
goto v___jp_3443_;
}
}
else
{
lean_dec(v___x_3475_);
v___y_3470_ = v___y_3440_;
v___y_3471_ = v___y_3441_;
goto v___jp_3469_;
}
v___jp_3469_:
{
lean_object* v___x_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3473_ = lean_unbox(v_val_3456_);
lean_dec(v_val_3456_);
v___x_3474_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3473_, v___x_3433_, v___x_3468_, v___x_3472_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_dec_ref_known(v___x_3474_, 1);
v_a_3444_ = v___x_3455_;
goto v___jp_3443_;
}
else
{
return v___x_3474_;
}
}
}
}
else
{
lean_dec(v_a_3454_);
v_a_3444_ = v___x_3455_;
goto v___jp_3443_;
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
v_a_3479_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3453_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3453_);
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
v___jp_3443_:
{
size_t v___x_3445_; size_t v___x_3446_; 
v___x_3445_ = ((size_t)1ULL);
v___x_3446_ = lean_usize_add(v_i_3438_, v___x_3445_);
v_i_3438_ = v___x_3446_;
v_b_3439_ = v_a_3444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___boxed(lean_object* v___x_3487_, lean_object* v___x_3488_, lean_object* v___x_3489_, lean_object* v_as_3490_, lean_object* v_sz_3491_, lean_object* v_i_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_12162__boxed_3497_; size_t v_sz_boxed_3498_; size_t v_i_boxed_3499_; lean_object* v_res_3500_; 
v___x_12162__boxed_3497_ = lean_unbox(v___x_3488_);
v_sz_boxed_3498_ = lean_unbox_usize(v_sz_3491_);
lean_dec(v_sz_3491_);
v_i_boxed_3499_ = lean_unbox_usize(v_i_3492_);
lean_dec(v_i_3492_);
v_res_3500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3487_, v___x_12162__boxed_3497_, v___x_3489_, v_as_3490_, v_sz_boxed_3498_, v_i_boxed_3499_, v_b_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_as_3490_);
lean_dec_ref(v___x_3489_);
lean_dec(v___x_3487_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(lean_object* v___x_3501_, uint8_t v___x_3502_, lean_object* v___x_3503_, lean_object* v_as_3504_, size_t v_sz_3505_, size_t v_i_3506_, lean_object* v_b_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_a_3512_; uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3506_, v_sz_3505_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3507_);
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v_a_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v_a_3519_ = lean_array_uget_borrowed(v_as_3504_, v_i_3506_);
v___x_3520_ = l_Lean_Syntax_getArg(v_a_3519_, v___x_3518_);
v___x_3521_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3520_, v___y_3508_, v___y_3509_);
lean_dec(v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = lean_box(0);
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_val_3524_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_val_3524_);
lean_dec_ref_known(v_a_3522_, 1);
lean_inc(v_a_3519_);
v___x_3525_ = l_Lean_Syntax_getKind(v_a_3519_);
v___x_3526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3527_ = lean_name_eq(v___x_3525_, v___x_3526_);
lean_dec(v___x_3525_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; size_t v_sz_3531_; size_t v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; 
v___x_3528_ = lean_unsigned_to_nat(2u);
v___x_3529_ = l_Lean_Syntax_getArg(v_a_3519_, v___x_3528_);
v___x_3530_ = l_Lean_Syntax_getArgs(v___x_3529_);
lean_dec(v___x_3529_);
v_sz_3531_ = lean_array_size(v___x_3530_);
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = lean_unbox(v_val_3524_);
lean_dec(v_val_3524_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3501_, v___x_3502_, v___x_3503_, v___x_3533_, v___x_3530_, v_sz_3531_, v___x_3532_, v___x_3523_, v___y_3508_, v___y_3509_);
lean_dec_ref(v___x_3530_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_dec_ref_known(v___x_3534_, 1);
v_a_3512_ = v___x_3523_;
goto v___jp_3511_;
}
else
{
return v___x_3534_;
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___x_3543_; 
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3536_ = l_Lean_Syntax_getArg(v_a_3519_, v___x_3535_);
v___x_3543_ = l_Lean_Syntax_getRange_x3f(v___x_3536_, v___x_3502_);
if (lean_obj_tag(v___x_3543_) == 1)
{
lean_object* v_val_3544_; lean_object* v_start_3545_; uint8_t v___x_3546_; 
v_val_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v_start_3545_ = lean_ctor_get(v_val_3544_, 0);
lean_inc(v_start_3545_);
lean_dec(v_val_3544_);
v___x_3546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3503_, v_start_3545_);
lean_dec(v_start_3545_);
if (v___x_3546_ == 0)
{
v___y_3538_ = v___y_3508_;
v___y_3539_ = v___y_3509_;
goto v___jp_3537_;
}
else
{
lean_dec(v___x_3536_);
lean_dec(v_val_3524_);
v_a_3512_ = v___x_3523_;
goto v___jp_3511_;
}
}
else
{
lean_dec(v___x_3543_);
v___y_3538_ = v___y_3508_;
v___y_3539_ = v___y_3509_;
goto v___jp_3537_;
}
v___jp_3537_:
{
lean_object* v___x_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3541_ = lean_unbox(v_val_3524_);
lean_dec(v_val_3524_);
v___x_3542_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3541_, v___x_3501_, v___x_3536_, v___x_3540_, v___y_3538_, v___y_3539_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_dec_ref_known(v___x_3542_, 1);
v_a_3512_ = v___x_3523_;
goto v___jp_3511_;
}
else
{
return v___x_3542_;
}
}
}
}
else
{
lean_dec(v_a_3522_);
v_a_3512_ = v___x_3523_;
goto v___jp_3511_;
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
v_a_3547_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3521_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3521_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
v___jp_3511_:
{
size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3506_, v___x_3513_);
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3501_, v___x_3502_, v___x_3503_, v_as_3504_, v_sz_3505_, v___x_3514_, v_a_3512_, v___y_3508_, v___y_3509_);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6___boxed(lean_object* v___x_3555_, lean_object* v___x_3556_, lean_object* v___x_3557_, lean_object* v_as_3558_, lean_object* v_sz_3559_, lean_object* v_i_3560_, lean_object* v_b_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
uint8_t v___x_12282__boxed_3565_; size_t v_sz_boxed_3566_; size_t v_i_boxed_3567_; lean_object* v_res_3568_; 
v___x_12282__boxed_3565_ = lean_unbox(v___x_3556_);
v_sz_boxed_3566_ = lean_unbox_usize(v_sz_3559_);
lean_dec(v_sz_3559_);
v_i_boxed_3567_ = lean_unbox_usize(v_i_3560_);
lean_dec(v_i_3560_);
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3555_, v___x_12282__boxed_3565_, v___x_3557_, v_as_3558_, v_sz_boxed_3566_, v_i_boxed_3567_, v_b_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v_as_3558_);
lean_dec_ref(v___x_3557_);
lean_dec(v___x_3555_);
return v_res_3568_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_unsigned_to_nat(16u);
v___x_3571_ = lean_mk_array(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3572_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__0, &l_Lean_Linter_MissingDocs_checkDecl___closed__0_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0);
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v___x_3572_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object* v_stx_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3579_; lean_object* v_head_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3579_ = lean_unsigned_to_nat(0u);
v_head_3580_ = l_Lean_Syntax_getArg(v_stx_3575_, v___x_3579_);
v___x_3581_ = lean_unsigned_to_nat(2u);
v___x_3582_ = l_Lean_Syntax_getArg(v_head_3580_, v___x_3581_);
v___x_3583_ = l_Lean_Syntax_getArg(v___x_3582_, v___x_3579_);
lean_dec(v___x_3582_);
v___x_3584_ = l_Lean_Syntax_getKind(v___x_3583_);
v___x_3585_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_3586_ = lean_name_eq(v___x_3584_, v___x_3585_);
lean_dec(v___x_3584_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_head_3580_, v_a_3576_, v_a_3577_);
lean_dec(v_head_3580_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3678_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3678_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3678_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v_rest_3593_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; uint8_t v___x_3629_; lean_object* v_k_3630_; lean_object* v___y_3632_; lean_object* v___y_3633_; 
v___x_3592_ = lean_unsigned_to_nat(1u);
v_rest_3593_ = l_Lean_Syntax_getArg(v_stx_3575_, v___x_3592_);
v___x_3629_ = 1;
lean_inc(v_rest_3593_);
v_k_3630_ = l_Lean_Syntax_getKind(v_rest_3593_);
if (lean_obj_tag(v_a_3588_) == 1)
{
lean_object* v_val_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; 
v_val_3673_ = lean_ctor_get(v_a_3588_, 0);
lean_inc(v_val_3673_);
lean_dec_ref_known(v_a_3588_, 1);
v___x_3674_ = l_Lean_Syntax_getArg(v_rest_3593_, v___x_3592_);
v___x_3675_ = l_Lean_Syntax_getArg(v___x_3674_, v___x_3579_);
lean_dec(v___x_3674_);
v___x_3676_ = lean_unbox(v_val_3673_);
lean_dec(v_val_3673_);
v___x_3677_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_3630_, v___x_3675_, v___x_3676_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_dec_ref_known(v___x_3677_, 1);
v___y_3632_ = v_a_3576_;
v___y_3633_ = v_a_3577_;
goto v___jp_3631_;
}
else
{
lean_dec(v_k_3630_);
lean_dec(v_rest_3593_);
lean_del_object(v___x_3590_);
return v___x_3677_;
}
}
else
{
lean_dec(v_a_3588_);
v___y_3632_ = v_a_3576_;
v___y_3633_ = v_a_3577_;
goto v___jp_3631_;
}
v___jp_3594_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; size_t v_sz_3602_; size_t v___x_3603_; lean_object* v___x_3604_; 
v___x_3598_ = lean_unsigned_to_nat(4u);
v___x_3599_ = l_Lean_Syntax_getArg(v_rest_3593_, v___x_3598_);
v___x_3600_ = l_Lean_Syntax_getArgs(v___x_3599_);
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_sz_3602_ = lean_array_size(v___x_3600_);
v___x_3603_ = ((size_t)0ULL);
v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3593_, v___x_3586_, v___y_3597_, v___x_3600_, v_sz_3602_, v___x_3603_, v___x_3601_, v___y_3596_, v___y_3595_);
lean_dec_ref(v___x_3600_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3627_; 
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3628_);
v___x_3606_ = v___x_3604_;
v_isShared_3607_ = v_isSharedCheck_3627_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3627_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3608_ = lean_unsigned_to_nat(5u);
v___x_3609_ = l_Lean_Syntax_getArg(v_rest_3593_, v___x_3608_);
v___x_3610_ = l_Lean_Syntax_isNone(v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; size_t v_sz_3614_; lean_object* v___x_3615_; 
lean_del_object(v___x_3606_);
v___x_3611_ = l_Lean_Syntax_getArg(v___x_3609_, v___x_3579_);
lean_dec(v___x_3609_);
v___x_3612_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3592_);
lean_dec(v___x_3611_);
v___x_3613_ = l_Lean_Syntax_getArgs(v___x_3612_);
lean_dec(v___x_3612_);
v_sz_3614_ = lean_array_size(v___x_3613_);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_3593_, v___x_3613_, v_sz_3614_, v___x_3603_, v___x_3601_, v___y_3596_, v___y_3595_);
lean_dec_ref(v___x_3613_);
lean_dec(v_rest_3593_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3623_);
v___x_3617_ = v___x_3615_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_dec(v___x_3615_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3601_);
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3601_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
return v___x_3615_;
}
}
else
{
lean_object* v___x_3625_; 
lean_dec(v___x_3609_);
lean_dec(v_rest_3593_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
v___x_3625_ = v___x_3606_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3601_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_dec(v_rest_3593_);
return v___x_3604_;
}
}
v___jp_3631_:
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_3635_ = lean_name_eq(v_k_3630_, v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3636_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_3637_ = lean_name_eq(v_k_3630_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_3639_ = lean_name_eq(v_k_3630_, v___x_3638_);
lean_dec(v_k_3630_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
lean_dec(v_rest_3593_);
v___x_3640_ = lean_box(0);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3640_);
v___x_3642_ = v___x_3590_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3644_ = lean_unsigned_to_nat(4u);
v___x_3645_ = l_Lean_Syntax_getArg(v_rest_3593_, v___x_3644_);
v___x_3646_ = l_Lean_Syntax_getArg(v___x_3645_, v___x_3581_);
lean_dec(v___x_3645_);
v___x_3647_ = l_Lean_Syntax_isNone(v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v_infoState_3649_; lean_object* v_trees_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; size_t v_sz_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
lean_del_object(v___x_3590_);
v___x_3648_ = lean_st_ref_get(v___y_3633_);
v_infoState_3649_ = lean_ctor_get(v___x_3648_, 8);
lean_inc_ref(v_infoState_3649_);
lean_dec(v___x_3648_);
v_trees_3650_ = lean_ctor_get(v_infoState_3649_, 2);
lean_inc_ref(v_trees_3650_);
lean_dec_ref(v_infoState_3649_);
v___x_3651_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__1, &l_Lean_Linter_MissingDocs_checkDecl___closed__1_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1);
v___x_3652_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_3647_, v_trees_3650_, v___x_3651_, v___x_3579_);
lean_dec_ref(v_trees_3650_);
v___x_3653_ = l_Lean_Syntax_getArg(v_rest_3593_, v___x_3592_);
lean_dec(v_rest_3593_);
v___x_3654_ = l_Lean_Syntax_getArg(v___x_3653_, v___x_3579_);
lean_dec(v___x_3653_);
v___x_3655_ = l_Lean_Syntax_getArg(v___x_3646_, v___x_3579_);
lean_dec(v___x_3646_);
v___x_3656_ = l_Lean_Syntax_getArgs(v___x_3655_);
lean_dec(v___x_3655_);
v___x_3657_ = lean_box(0);
v_sz_3658_ = lean_array_size(v___x_3656_);
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3654_, v___x_3647_, v___x_3652_, v___x_3656_, v_sz_3658_, v___x_3659_, v___x_3657_, v___y_3632_, v___y_3633_);
lean_dec_ref(v___x_3656_);
lean_dec_ref(v___x_3652_);
lean_dec(v___x_3654_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; 
v_unused_3668_ = lean_ctor_get(v___x_3660_, 0);
lean_dec(v_unused_3668_);
v___x_3662_ = v___x_3660_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v___x_3660_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3657_);
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3657_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
else
{
return v___x_3660_;
}
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_dec(v___x_3646_);
lean_dec(v_rest_3593_);
v___x_3669_ = lean_box(0);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3669_);
v___x_3671_ = v___x_3590_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_dec(v_k_3630_);
lean_del_object(v___x_3590_);
v___y_3595_ = v___y_3633_;
v___y_3596_ = v___y_3632_;
v___y_3597_ = v___x_3637_;
goto v___jp_3594_;
}
}
else
{
lean_dec(v_k_3630_);
lean_del_object(v___x_3590_);
v___y_3595_ = v___y_3633_;
v___y_3596_ = v___y_3632_;
v___y_3597_ = v___x_3629_;
goto v___jp_3594_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_a_3679_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3587_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3587_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_dec(v_head_3580_);
v___x_3687_ = lean_box(0);
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object* v_stx_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Linter_MissingDocs_checkDecl(v_stx_3689_, v_a_3690_, v_a_3691_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_stx_3689_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2(lean_object* v_00_u03b2_3694_, lean_object* v_m_3695_, lean_object* v_a_3696_, lean_object* v_b_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_m_3695_, v_a_3696_, v_b_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object* v_00_u03b2_3699_, lean_object* v_m_3700_, lean_object* v_a_3701_){
_start:
{
uint8_t v___x_3702_; 
v___x_3702_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3700_, v_a_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object* v_00_u03b2_3703_, lean_object* v_m_3704_, lean_object* v_a_3705_){
_start:
{
uint8_t v_res_3706_; lean_object* v_r_3707_; 
v_res_3706_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(v_00_u03b2_3703_, v_m_3704_, v_a_3705_);
lean_dec(v_a_3705_);
lean_dec_ref(v_m_3704_);
v_r_3707_ = lean_box(v_res_3706_);
return v_r_3707_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(lean_object* v_00_u03b2_3708_, lean_object* v_a_3709_, lean_object* v_x_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3709_, v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3712_, lean_object* v_a_3713_, lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(v_00_u03b2_3712_, v_a_3713_, v_x_3714_);
lean_dec(v_x_3714_);
lean_dec(v_a_3713_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3(lean_object* v_00_u03b2_3717_, lean_object* v_data_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_data_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3720_, lean_object* v_i_3721_, lean_object* v_source_3722_, lean_object* v_target_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v_i_3721_, v_source_3722_, v_target_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_3725_, lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_x_3726_, v_x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkDecl___boxed), 4, 0);
v___x_3736_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3736_, 0, v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1));
v___x_3739_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2);
v___x_3740_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3738_, v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___boxed(lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object* v_stx_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3748_ = lean_unsigned_to_nat(2u);
v___x_3749_ = l_Lean_Syntax_getArg(v_stx_3744_, v___x_3748_);
v___x_3750_ = l_Lean_Syntax_isNone(v___x_3749_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = lean_unsigned_to_nat(0u);
v___x_3752_ = l_Lean_Syntax_getArg(v_stx_3744_, v___x_3751_);
v___x_3753_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3752_, v_a_3745_, v_a_3746_);
lean_dec(v___x_3752_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3767_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_3767_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3767_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
if (lean_obj_tag(v_a_3754_) == 1)
{
lean_object* v_val_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; lean_object* v___x_3762_; 
lean_del_object(v___x_3756_);
v_val_3758_ = lean_ctor_get(v_a_3754_, 0);
lean_inc(v_val_3758_);
lean_dec_ref_known(v_a_3754_, 1);
v___x_3759_ = l_Lean_Syntax_getArg(v___x_3749_, v___x_3751_);
lean_dec(v___x_3749_);
v___x_3760_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkInit___closed__0));
v___x_3761_ = lean_unbox(v_val_3758_);
lean_dec(v_val_3758_);
v___x_3762_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3761_, v___x_3759_, v___x_3760_, v_a_3745_, v_a_3746_);
return v___x_3762_;
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_dec(v_a_3754_);
lean_dec(v___x_3749_);
v___x_3763_ = lean_box(0);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v___x_3763_);
v___x_3765_ = v___x_3756_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v___x_3749_);
v_a_3768_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3753_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3753_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec(v___x_3749_);
v___x_3776_ = lean_box(0);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
return v___x_3777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object* v_stx_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Linter_MissingDocs_checkInit(v_stx_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_stx_3778_);
return v_res_3782_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkInit___boxed), 4, 0);
v___x_3790_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1));
v___x_3793_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2);
v___x_3794_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3792_, v___x_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___boxed(lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object* v_stx_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v___x_3808_ = lean_unsigned_to_nat(2u);
v___x_3809_ = l_Lean_Syntax_getArg(v_stx_3804_, v___x_3808_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = l_Lean_Syntax_getArg(v___x_3809_, v___x_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = l_Lean_Syntax_getArg(v___x_3811_, v___x_3810_);
lean_dec(v___x_3811_);
v___x_3813_ = l_Lean_Syntax_getKind(v___x_3812_);
v___x_3814_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3815_ = lean_name_eq(v___x_3813_, v___x_3814_);
lean_dec(v___x_3813_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3816_ = l_Lean_Syntax_getArg(v_stx_3804_, v___x_3810_);
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = l_Lean_Syntax_getArg(v_stx_3804_, v___x_3817_);
v___x_3819_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3816_, v___x_3818_, v___x_3815_, v_a_3805_, v_a_3806_);
lean_dec(v___x_3818_);
lean_dec(v___x_3816_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3843_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3843_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3843_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
if (lean_obj_tag(v_a_3820_) == 1)
{
lean_object* v_val_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
lean_del_object(v___x_3822_);
v_val_3824_ = lean_ctor_get(v_a_3820_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_a_3820_, 1);
v___x_3825_ = lean_unsigned_to_nat(5u);
v___x_3826_ = l_Lean_Syntax_getArg(v_stx_3804_, v___x_3825_);
v___x_3827_ = l_Lean_Syntax_isNone(v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3828_ = l_Lean_Syntax_getArg(v___x_3826_, v___x_3810_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_unsigned_to_nat(3u);
v___x_3830_ = l_Lean_Syntax_getArg(v___x_3828_, v___x_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3832_ = lean_unbox(v_val_3824_);
lean_dec(v_val_3824_);
v___x_3833_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3832_, v___x_3830_, v___x_3831_, v_a_3805_, v_a_3806_);
return v___x_3833_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; lean_object* v___x_3838_; 
lean_dec(v___x_3826_);
v___x_3834_ = lean_unsigned_to_nat(3u);
v___x_3835_ = l_Lean_Syntax_getArg(v_stx_3804_, v___x_3834_);
v___x_3836_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3837_ = lean_unbox(v_val_3824_);
lean_dec(v_val_3824_);
v___x_3838_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3837_, v___x_3835_, v___x_3836_, v_a_3805_, v_a_3806_);
return v___x_3838_;
}
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_dec(v_a_3820_);
v___x_3839_ = lean_box(0);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3839_);
v___x_3841_ = v___x_3822_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v_a_3844_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3819_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3819_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
return v___x_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object* v_stx_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Linter_MissingDocs_checkNotation(v_stx_3854_, v_a_3855_, v_a_3856_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_stx_3854_);
return v_res_3858_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkNotation___boxed), 4, 0);
v___x_3865_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0));
v___x_3868_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1);
v___x_3869_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3867_, v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___boxed(lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object* v_stx_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3876_ = lean_unsigned_to_nat(2u);
v___x_3877_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3876_);
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = l_Lean_Syntax_getArg(v___x_3877_, v___x_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = l_Lean_Syntax_getArg(v___x_3879_, v___x_3878_);
lean_dec(v___x_3879_);
v___x_3881_ = l_Lean_Syntax_getKind(v___x_3880_);
v___x_3882_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3883_ = lean_name_eq(v___x_3881_, v___x_3882_);
lean_dec(v___x_3881_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3884_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3878_);
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3885_);
v___x_3887_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3884_, v___x_3886_, v___x_3883_, v_a_3873_, v_a_3874_);
lean_dec(v___x_3886_);
lean_dec(v___x_3884_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3914_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3890_ = v___x_3887_;
v_isShared_3891_ = v_isSharedCheck_3914_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3914_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
if (lean_obj_tag(v_a_3888_) == 1)
{
lean_object* v_val_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
lean_del_object(v___x_3890_);
v_val_3892_ = lean_ctor_get(v_a_3888_, 0);
lean_inc(v_val_3892_);
lean_dec_ref_known(v_a_3888_, 1);
v___x_3893_ = lean_unsigned_to_nat(5u);
v___x_3894_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3893_);
v___x_3895_ = l_Lean_Syntax_isNone(v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3896_ = l_Lean_Syntax_getArg(v___x_3894_, v___x_3878_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_unsigned_to_nat(3u);
v___x_3898_ = l_Lean_Syntax_getArg(v___x_3896_, v___x_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3897_);
v___x_3900_ = l_Lean_Syntax_getArg(v___x_3899_, v___x_3878_);
lean_dec(v___x_3899_);
v___x_3901_ = l_Lean_Syntax_getAtomVal(v___x_3900_);
lean_dec(v___x_3900_);
v___x_3902_ = lean_unbox(v_val_3892_);
lean_dec(v_val_3892_);
v___x_3903_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3902_, v___x_3898_, v___x_3901_, v_a_3873_, v_a_3874_);
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v___x_3894_);
v___x_3904_ = lean_unsigned_to_nat(3u);
v___x_3905_ = l_Lean_Syntax_getArg(v_stx_3872_, v___x_3904_);
v___x_3906_ = l_Lean_Syntax_getArg(v___x_3905_, v___x_3878_);
v___x_3907_ = l_Lean_Syntax_getAtomVal(v___x_3906_);
lean_dec(v___x_3906_);
v___x_3908_ = lean_unbox(v_val_3892_);
lean_dec(v_val_3892_);
v___x_3909_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3908_, v___x_3905_, v___x_3907_, v_a_3873_, v_a_3874_);
return v___x_3909_;
}
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
lean_dec(v_a_3888_);
v___x_3910_ = lean_box(0);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3910_);
v___x_3912_ = v___x_3890_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
v_a_3915_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3887_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3887_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object* v_stx_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Linter_MissingDocs_checkMixfix(v_stx_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_stx_3925_);
return v_res_3929_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMixfix___boxed), 4, 0);
v___x_3937_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1));
v___x_3940_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2);
v___x_3941_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3939_, v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___boxed(lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object* v_stx_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3949_ = lean_unsigned_to_nat(2u);
v___x_3950_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3949_);
v___x_3951_ = lean_unsigned_to_nat(0u);
v___x_3952_ = l_Lean_Syntax_getArg(v___x_3950_, v___x_3951_);
lean_dec(v___x_3950_);
v___x_3953_ = l_Lean_Syntax_getArg(v___x_3952_, v___x_3951_);
lean_dec(v___x_3952_);
v___x_3954_ = l_Lean_Syntax_getKind(v___x_3953_);
v___x_3955_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3956_ = lean_name_eq(v___x_3954_, v___x_3955_);
lean_dec(v___x_3954_);
if (v___x_3956_ == 0)
{
uint8_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3957_ = 1;
v___x_3958_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3951_);
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3959_);
v___x_3961_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3958_, v___x_3960_, v___x_3957_, v_a_3946_, v_a_3947_);
lean_dec(v___x_3960_);
lean_dec(v___x_3958_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3985_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3985_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3985_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
if (lean_obj_tag(v_a_3962_) == 1)
{
lean_object* v_val_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
lean_del_object(v___x_3964_);
v_val_3966_ = lean_ctor_get(v_a_3962_, 0);
lean_inc(v_val_3966_);
lean_dec_ref_known(v_a_3962_, 1);
v___x_3967_ = lean_unsigned_to_nat(5u);
v___x_3968_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3967_);
v___x_3969_ = l_Lean_Syntax_isNone(v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; 
v___x_3970_ = l_Lean_Syntax_getArg(v___x_3968_, v___x_3951_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_unsigned_to_nat(3u);
v___x_3972_ = l_Lean_Syntax_getArg(v___x_3970_, v___x_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3974_ = lean_unbox(v_val_3966_);
lean_dec(v_val_3966_);
v___x_3975_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3974_, v___x_3972_, v___x_3973_, v_a_3946_, v_a_3947_);
return v___x_3975_;
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v___x_3968_);
v___x_3976_ = lean_unsigned_to_nat(3u);
v___x_3977_ = l_Lean_Syntax_getArg(v_stx_3945_, v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3979_ = lean_unbox(v_val_3966_);
lean_dec(v_val_3966_);
v___x_3980_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3979_, v___x_3977_, v___x_3978_, v_a_3946_, v_a_3947_);
return v___x_3980_;
}
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3983_; 
lean_dec(v_a_3962_);
v___x_3981_ = lean_box(0);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3981_);
v___x_3983_ = v___x_3964_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
v_a_3986_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3961_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3961_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_box(0);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object* v_stx_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Linter_MissingDocs_checkSyntax(v_stx_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_stx_3996_);
return v_res_4000_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntax___boxed), 4, 0);
v___x_4007_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0));
v___x_4010_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1);
v___x_4011_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4009_, v___x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___boxed(lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object* v_name_4014_, lean_object* v_declNameStxIdx_4015_, lean_object* v_stx_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = lean_unsigned_to_nat(0u);
v___x_4021_ = l_Lean_Syntax_getArg(v_stx_4016_, v___x_4020_);
v___x_4022_ = l_Lean_Linter_MissingDocs_isMissingDoc(v___x_4021_, v_a_4017_, v_a_4018_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4047_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4047_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4047_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_unbox(v_a_4023_);
lean_dec(v_a_4023_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
lean_dec(v___x_4021_);
lean_dec_ref(v_name_4014_);
v___x_4028_ = lean_box(0);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
else
{
lean_object* v___x_4032_; 
lean_del_object(v___x_4025_);
v___x_4032_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_4021_, v_a_4017_, v_a_4018_);
lean_dec(v___x_4021_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; uint8_t v___x_4034_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = lean_unbox(v_a_4033_);
lean_dec(v_a_4033_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = l_Lean_Syntax_getArg(v_stx_4016_, v_declNameStxIdx_4015_);
v___x_4036_ = l_Lean_Linter_MissingDocs_lintNamed(v___x_4035_, v_name_4014_, v_a_4017_, v_a_4018_);
return v___x_4036_;
}
else
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = l_Lean_Syntax_getArg(v_stx_4016_, v_declNameStxIdx_4015_);
v___x_4038_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v___x_4037_, v_name_4014_, v_a_4017_, v_a_4018_);
return v___x_4038_;
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec_ref(v_name_4014_);
v_a_4039_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4032_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4032_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v___x_4021_);
lean_dec_ref(v_name_4014_);
v_a_4048_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4022_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4022_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object* v_name_4056_, lean_object* v_declNameStxIdx_4057_, lean_object* v_stx_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v_name_4056_, v_declNameStxIdx_4057_, v_stx_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_stx_4058_);
lean_dec(v_declNameStxIdx_4057_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_4068_ = lean_unsigned_to_nat(2u);
v___x_4069_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4067_, v___x_4068_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
return v_res_4074_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed), 4, 0);
v___x_4082_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1));
v___x_4085_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2);
v___x_4086_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4084_, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___boxed(lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0));
v___x_4095_ = lean_unsigned_to_nat(2u);
v___x_4096_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4094_, v___x_4095_, v_a_4090_, v_a_4091_, v_a_4092_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Linter_MissingDocs_checkSyntaxCat(v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
return v_res_4101_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed), 4, 0);
v___x_4109_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4111_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1));
v___x_4112_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2);
v___x_4113_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4111_, v___x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___boxed(lean_object* v_a_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object* v_stx_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4121_ = lean_unsigned_to_nat(2u);
v___x_4122_ = l_Lean_Syntax_getArg(v_stx_4117_, v___x_4121_);
v___x_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = l_Lean_Syntax_getArg(v___x_4122_, v___x_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = l_Lean_Syntax_getArg(v___x_4124_, v___x_4123_);
lean_dec(v___x_4124_);
v___x_4126_ = l_Lean_Syntax_getKind(v___x_4125_);
v___x_4127_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4128_ = lean_name_eq(v___x_4126_, v___x_4127_);
lean_dec(v___x_4126_);
if (v___x_4128_ == 0)
{
uint8_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4129_ = 1;
v___x_4130_ = l_Lean_Syntax_getArg(v_stx_4117_, v___x_4123_);
v___x_4131_ = lean_unsigned_to_nat(1u);
v___x_4132_ = l_Lean_Syntax_getArg(v_stx_4117_, v___x_4131_);
v___x_4133_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4130_, v___x_4132_, v___x_4129_, v_a_4118_, v_a_4119_);
lean_dec(v___x_4132_);
lean_dec(v___x_4130_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4157_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4157_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4157_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
if (lean_obj_tag(v_a_4134_) == 1)
{
lean_object* v_val_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
lean_del_object(v___x_4136_);
v_val_4138_ = lean_ctor_get(v_a_4134_, 0);
lean_inc(v_val_4138_);
lean_dec_ref_known(v_a_4134_, 1);
v___x_4139_ = lean_unsigned_to_nat(5u);
v___x_4140_ = l_Lean_Syntax_getArg(v_stx_4117_, v___x_4139_);
v___x_4141_ = l_Lean_Syntax_isNone(v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; 
v___x_4142_ = l_Lean_Syntax_getArg(v___x_4140_, v___x_4123_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_unsigned_to_nat(3u);
v___x_4144_ = l_Lean_Syntax_getArg(v___x_4142_, v___x_4143_);
lean_dec(v___x_4142_);
v___x_4145_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4146_ = lean_unbox(v_val_4138_);
lean_dec(v_val_4138_);
v___x_4147_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4146_, v___x_4144_, v___x_4145_, v_a_4118_, v_a_4119_);
return v___x_4147_;
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v___x_4140_);
v___x_4148_ = lean_unsigned_to_nat(3u);
v___x_4149_ = l_Lean_Syntax_getArg(v_stx_4117_, v___x_4148_);
v___x_4150_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4151_ = lean_unbox(v_val_4138_);
lean_dec(v_val_4138_);
v___x_4152_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4151_, v___x_4149_, v___x_4150_, v_a_4118_, v_a_4119_);
return v___x_4152_;
}
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
lean_dec(v_a_4134_);
v___x_4153_ = lean_box(0);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v___x_4153_);
v___x_4155_ = v___x_4136_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
v_a_4158_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4133_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4133_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_box(0);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object* v_stx_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Linter_MissingDocs_checkMacro(v_stx_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_stx_4168_);
return v_res_4172_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMacro___boxed), 4, 0);
v___x_4179_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0));
v___x_4182_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1);
v___x_4183_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4181_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___boxed(lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object* v_stx_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4191_ = lean_unsigned_to_nat(2u);
v___x_4192_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = l_Lean_Syntax_getArg(v___x_4192_, v___x_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = l_Lean_Syntax_getArg(v___x_4194_, v___x_4193_);
lean_dec(v___x_4194_);
v___x_4196_ = l_Lean_Syntax_getKind(v___x_4195_);
v___x_4197_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4198_ = lean_name_eq(v___x_4196_, v___x_4197_);
lean_dec(v___x_4196_);
if (v___x_4198_ == 0)
{
uint8_t v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4199_ = 1;
v___x_4200_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4193_);
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4201_);
v___x_4203_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4200_, v___x_4202_, v___x_4199_, v_a_4188_, v_a_4189_);
lean_dec(v___x_4202_);
lean_dec(v___x_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4227_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4227_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4227_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
if (lean_obj_tag(v_a_4204_) == 1)
{
lean_object* v_val_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
lean_del_object(v___x_4206_);
v_val_4208_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_val_4208_);
lean_dec_ref_known(v_a_4204_, 1);
v___x_4209_ = lean_unsigned_to_nat(5u);
v___x_4210_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4209_);
v___x_4211_ = l_Lean_Syntax_isNone(v___x_4210_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; lean_object* v___x_4217_; 
v___x_4212_ = l_Lean_Syntax_getArg(v___x_4210_, v___x_4193_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_unsigned_to_nat(3u);
v___x_4214_ = l_Lean_Syntax_getArg(v___x_4212_, v___x_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4216_ = lean_unbox(v_val_4208_);
lean_dec(v_val_4208_);
v___x_4217_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4216_, v___x_4214_, v___x_4215_, v_a_4188_, v_a_4189_);
return v___x_4217_;
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; 
lean_dec(v___x_4210_);
v___x_4218_ = lean_unsigned_to_nat(3u);
v___x_4219_ = l_Lean_Syntax_getArg(v_stx_4187_, v___x_4218_);
v___x_4220_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4221_ = lean_unbox(v_val_4208_);
lean_dec(v_val_4208_);
v___x_4222_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4221_, v___x_4219_, v___x_4220_, v_a_4188_, v_a_4189_);
return v___x_4222_;
}
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
lean_dec(v_a_4204_);
v___x_4223_ = lean_box(0);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4223_);
v___x_4225_ = v___x_4206_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4203_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4203_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_box(0);
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4236_);
return v___x_4237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object* v_stx_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Linter_MissingDocs_checkElab(v_stx_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_stx_4238_);
return v_res_4242_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1(void){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkElab___boxed), 4, 0);
v___x_4249_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4249_, 0, v___x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0));
v___x_4252_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1);
v___x_4253_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4251_, v___x_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___boxed(lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object* v_stx_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = lean_unsigned_to_nat(0u);
v___x_4262_ = l_Lean_Syntax_getArg(v_stx_4257_, v___x_4261_);
v___x_4263_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4262_, v_a_4258_, v_a_4259_);
lean_dec(v___x_4262_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4278_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4278_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4278_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
if (lean_obj_tag(v_a_4264_) == 1)
{
lean_object* v_val_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; lean_object* v___x_4273_; 
lean_del_object(v___x_4266_);
v_val_4268_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_val_4268_);
lean_dec_ref_known(v_a_4264_, 1);
v___x_4269_ = lean_unsigned_to_nat(3u);
v___x_4270_ = l_Lean_Syntax_getArg(v_stx_4257_, v___x_4269_);
v___x_4271_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0));
v___x_4272_ = lean_unbox(v_val_4268_);
lean_dec(v_val_4268_);
v___x_4273_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4272_, v___x_4270_, v___x_4271_, v_a_4258_, v_a_4259_);
return v___x_4273_;
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
lean_dec(v_a_4264_);
v___x_4274_ = lean_box(0);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4274_);
v___x_4276_ = v___x_4266_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4263_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4263_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object* v_stx_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Linter_MissingDocs_checkClassAbbrev(v_stx_4287_, v_a_4288_, v_a_4289_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_stx_4287_);
return v_res_4291_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed), 4, 0);
v___x_4299_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4301_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1));
v___x_4302_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2);
v___x_4303_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4301_, v___x_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___boxed(lean_object* v_a_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSimpLike___closed__0));
v___x_4312_ = lean_unsigned_to_nat(2u);
v___x_4313_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4311_, v___x_4312_, v_a_4307_, v_a_4308_, v_a_4309_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lean_Linter_MissingDocs_checkSimpLike(v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
return v_res_4318_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3(void){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSimpLike___boxed), 4, 0);
v___x_4327_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2));
v___x_4330_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3);
v___x_4331_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4329_, v___x_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___boxed(lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4340_ = lean_unsigned_to_nat(3u);
v___x_4341_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4339_, v___x_4340_, v_a_4335_, v_a_4336_, v_a_4337_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(v_a_4342_, v_a_4343_, v_a_4344_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
return v_res_4346_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3(void){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4353_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed), 4, 0);
v___x_4354_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4354_, 0, v___x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2));
v___x_4357_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3);
v___x_4358_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4356_, v___x_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___boxed(lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object* v_stx_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4365_);
v___x_4367_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4366_, v_a_4362_, v_a_4363_);
lean_dec(v___x_4366_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4382_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4382_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4382_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
if (lean_obj_tag(v_a_4368_) == 1)
{
lean_object* v_val_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; 
lean_del_object(v___x_4370_);
v_val_4372_ = lean_ctor_get(v_a_4368_, 0);
lean_inc(v_val_4372_);
lean_dec_ref_known(v_a_4368_, 1);
v___x_4373_ = lean_unsigned_to_nat(2u);
v___x_4374_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4373_);
v___x_4375_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4376_ = lean_unbox(v_val_4372_);
lean_dec(v_val_4372_);
v___x_4377_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4376_, v___x_4374_, v___x_4375_, v_a_4362_, v_a_4363_);
return v___x_4377_;
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
lean_dec(v_a_4368_);
v___x_4378_ = lean_box(0);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4378_);
v___x_4380_ = v___x_4370_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
v_a_4383_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4367_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4367_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object* v_stx_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Linter_MissingDocs_checkRegisterOption(v_stx_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_stx_4391_);
return v_res_4395_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterOption___boxed), 4, 0);
v___x_4402_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4402_, 0, v___x_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1));
v___x_4405_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2);
v___x_4406_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4404_, v___x_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___boxed(lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0));
v___x_4415_ = lean_unsigned_to_nat(2u);
v___x_4416_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4414_, v___x_4415_, v_a_4410_, v_a_4411_, v_a_4412_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(v_a_4417_, v_a_4418_, v_a_4419_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_a_4417_);
return v_res_4421_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed), 4, 0);
v___x_4429_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1));
v___x_4432_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2);
v___x_4433_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4431_, v___x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___boxed(lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(lean_object* v_t_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v_infoState_4440_; uint8_t v_enabled_4441_; 
v___x_4439_ = lean_st_ref_get(v___y_4437_);
v_infoState_4440_ = lean_ctor_get(v___x_4439_, 8);
lean_inc_ref(v_infoState_4440_);
lean_dec(v___x_4439_);
v_enabled_4441_ = lean_ctor_get_uint8(v_infoState_4440_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4440_);
if (v_enabled_4441_ == 0)
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
lean_dec_ref(v_t_4436_);
v___x_4442_ = lean_box(0);
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
return v___x_4443_;
}
else
{
lean_object* v___x_4444_; lean_object* v_infoState_4445_; lean_object* v_env_4446_; lean_object* v_messages_4447_; lean_object* v_scopes_4448_; lean_object* v_usedQuotCtxts_4449_; lean_object* v_nextMacroScope_4450_; lean_object* v_maxRecDepth_4451_; lean_object* v_ngen_4452_; lean_object* v_auxDeclNGen_4453_; lean_object* v_traceState_4454_; lean_object* v_snapshotTasks_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4477_; 
v___x_4444_ = lean_st_ref_take(v___y_4437_);
v_infoState_4445_ = lean_ctor_get(v___x_4444_, 8);
v_env_4446_ = lean_ctor_get(v___x_4444_, 0);
v_messages_4447_ = lean_ctor_get(v___x_4444_, 1);
v_scopes_4448_ = lean_ctor_get(v___x_4444_, 2);
v_usedQuotCtxts_4449_ = lean_ctor_get(v___x_4444_, 3);
v_nextMacroScope_4450_ = lean_ctor_get(v___x_4444_, 4);
v_maxRecDepth_4451_ = lean_ctor_get(v___x_4444_, 5);
v_ngen_4452_ = lean_ctor_get(v___x_4444_, 6);
v_auxDeclNGen_4453_ = lean_ctor_get(v___x_4444_, 7);
v_traceState_4454_ = lean_ctor_get(v___x_4444_, 9);
v_snapshotTasks_4455_ = lean_ctor_get(v___x_4444_, 10);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4457_ = v___x_4444_;
v_isShared_4458_ = v_isSharedCheck_4477_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_snapshotTasks_4455_);
lean_inc(v_traceState_4454_);
lean_inc(v_infoState_4445_);
lean_inc(v_auxDeclNGen_4453_);
lean_inc(v_ngen_4452_);
lean_inc(v_maxRecDepth_4451_);
lean_inc(v_nextMacroScope_4450_);
lean_inc(v_usedQuotCtxts_4449_);
lean_inc(v_scopes_4448_);
lean_inc(v_messages_4447_);
lean_inc(v_env_4446_);
lean_dec(v___x_4444_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4477_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
uint8_t v_enabled_4459_; lean_object* v_assignment_4460_; lean_object* v_lazyAssignment_4461_; lean_object* v_trees_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4476_; 
v_enabled_4459_ = lean_ctor_get_uint8(v_infoState_4445_, sizeof(void*)*3);
v_assignment_4460_ = lean_ctor_get(v_infoState_4445_, 0);
v_lazyAssignment_4461_ = lean_ctor_get(v_infoState_4445_, 1);
v_trees_4462_ = lean_ctor_get(v_infoState_4445_, 2);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_infoState_4445_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4464_ = v_infoState_4445_;
v_isShared_4465_ = v_isSharedCheck_4476_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_trees_4462_);
lean_inc(v_lazyAssignment_4461_);
lean_inc(v_assignment_4460_);
lean_dec(v_infoState_4445_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4476_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4466_ = l_Lean_PersistentArray_push___redArg(v_trees_4462_, v_t_4436_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 2, v___x_4466_);
v___x_4468_ = v___x_4464_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_assignment_4460_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_lazyAssignment_4461_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v___x_4466_);
lean_ctor_set_uint8(v_reuseFailAlloc_4475_, sizeof(void*)*3, v_enabled_4459_);
v___x_4468_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 8, v___x_4468_);
v___x_4470_ = v___x_4457_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_env_4446_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_messages_4447_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v_scopes_4448_);
lean_ctor_set(v_reuseFailAlloc_4474_, 3, v_usedQuotCtxts_4449_);
lean_ctor_set(v_reuseFailAlloc_4474_, 4, v_nextMacroScope_4450_);
lean_ctor_set(v_reuseFailAlloc_4474_, 5, v_maxRecDepth_4451_);
lean_ctor_set(v_reuseFailAlloc_4474_, 6, v_ngen_4452_);
lean_ctor_set(v_reuseFailAlloc_4474_, 7, v_auxDeclNGen_4453_);
lean_ctor_set(v_reuseFailAlloc_4474_, 8, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4474_, 9, v_traceState_4454_);
lean_ctor_set(v_reuseFailAlloc_4474_, 10, v_snapshotTasks_4455_);
v___x_4470_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = lean_st_ref_set(v___y_4437_, v___x_4470_);
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_t_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_4478_, v___y_4479_);
lean_dec(v___y_4479_);
return v_res_4481_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = lean_unsigned_to_nat(32u);
v___x_4483_ = lean_mk_empty_array_with_capacity(v___x_4482_);
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4485_ = ((size_t)5ULL);
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = lean_unsigned_to_nat(32u);
v___x_4488_ = lean_mk_empty_array_with_capacity(v___x_4487_);
v___x_4489_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0);
v___x_4490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
lean_ctor_set(v___x_4490_, 1, v___x_4488_);
lean_ctor_set(v___x_4490_, 2, v___x_4486_);
lean_ctor_set(v___x_4490_, 3, v___x_4486_);
lean_ctor_set_usize(v___x_4490_, 4, v___x_4485_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(lean_object* v_t_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; lean_object* v_infoState_4496_; uint8_t v_enabled_4497_; 
v___x_4495_ = lean_st_ref_get(v___y_4493_);
v_infoState_4496_ = lean_ctor_get(v___x_4495_, 8);
lean_inc_ref(v_infoState_4496_);
lean_dec(v___x_4495_);
v_enabled_4497_ = lean_ctor_get_uint8(v_infoState_4496_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4496_);
if (v_enabled_4497_ == 0)
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_dec_ref(v_t_4491_);
v___x_4498_ = lean_box(0);
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4500_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1);
v___x_4501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4501_, 0, v_t_4491_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
v___x_4502_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v___x_4501_, v___y_4493_);
return v___x_4502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___boxed(lean_object* v_t_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v_t_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(lean_object* v_info_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_4512_, 0, v_info_4508_);
v___x_4513_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4512_, v___y_4509_, v___y_4510_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0___boxed(lean_object* v_info_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v_info_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4518_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0));
v___x_4521_ = l_Lean_stringToMessageData(v___x_4520_);
return v___x_4521_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2));
v___x_4524_ = l_Lean_stringToMessageData(v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(lean_object* v_optionName_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4529_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1);
v___x_4530_ = l_Lean_MessageData_ofName(v_optionName_4525_);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4529_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4533_, v___y_4526_, v___y_4527_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___boxed(lean_object* v_optionName_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(lean_object* v_o_4540_, lean_object* v_k_4541_, lean_object* v_v_4542_){
_start:
{
lean_object* v_map_4543_; uint8_t v_hasTrace_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4557_; 
v_map_4543_ = lean_ctor_get(v_o_4540_, 0);
v_hasTrace_4544_ = lean_ctor_get_uint8(v_o_4540_, sizeof(void*)*1);
v_isSharedCheck_4557_ = !lean_is_exclusive(v_o_4540_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4546_ = v_o_4540_;
v_isShared_4547_ = v_isSharedCheck_4557_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_map_4543_);
lean_dec(v_o_4540_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4557_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; 
lean_inc(v_k_4541_);
v___x_4548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4541_, v_v_4542_, v_map_4543_);
if (v_hasTrace_4544_ == 0)
{
lean_object* v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4552_; 
v___x_4549_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_4550_ = l_Lean_Name_isPrefixOf(v___x_4549_, v_k_4541_);
lean_dec(v_k_4541_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4552_ = v___x_4546_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4548_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_ctor_set_uint8(v___x_4552_, sizeof(void*)*1, v___x_4550_);
return v___x_4552_;
}
}
else
{
lean_object* v___x_4555_; 
lean_dec(v_k_4541_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4555_ = v___x_4546_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4548_);
lean_ctor_set_uint8(v_reuseFailAlloc_4556_, sizeof(void*)*1, v_hasTrace_4544_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_msg_4558_){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = l_Lean_instInhabitedExpr;
v___x_4560_ = lean_panic_fn_borrowed(v___x_4559_, v_msg_4558_);
return v___x_4560_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_4563_ = l_Lean_stringToMessageData(v___x_4562_);
return v___x_4563_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_4566_ = l_Lean_stringToMessageData(v___x_4565_);
return v___x_4566_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4));
v___x_4569_ = l_Lean_stringToMessageData(v___x_4568_);
return v___x_4569_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6));
v___x_4572_ = l_Lean_stringToMessageData(v___x_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16(void){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4584_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15));
v___x_4585_ = lean_unsigned_to_nat(14u);
v___x_4586_ = lean_unsigned_to_nat(22u);
v___x_4587_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14));
v___x_4588_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13));
v___x_4589_ = l_mkPanicMessageWithDecl(v___x_4588_, v___x_4587_, v___x_4586_, v___x_4585_, v___x_4584_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(lean_object* v_optionName_4590_, lean_object* v_found_4591_, lean_object* v_defVal_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_4592_);
if (lean_obj_tag(v___x_4596_) == 1)
{
lean_object* v_val_4597_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4620_; lean_object* v___x_4668_; 
v_val_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_val_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v___x_4668_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_4591_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16);
v___x_4670_ = l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(v___x_4669_);
v___y_4620_ = v___x_4670_;
goto v___jp_4619_;
}
else
{
lean_object* v_val_4671_; 
v_val_4671_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v___x_4668_, 1);
v___y_4620_ = v_val_4671_;
goto v___jp_4619_;
}
v___jp_4598_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4602_ = l_Lean_MessageData_ofFormat(v___y_4601_);
v___x_4603_ = l_Lean_indentD(v___x_4602_);
lean_inc_ref(v___y_4600_);
v___x_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___y_4600_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1);
v___x_4606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4604_);
lean_ctor_set(v___x_4606_, 1, v___x_4605_);
v___x_4607_ = l_Lean_MessageData_ofExpr(v___y_4599_);
v___x_4608_ = l_Lean_indentD(v___x_4607_);
v___x_4609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4606_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3);
v___x_4611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = l_Lean_MessageData_ofName(v_optionName_4590_);
v___x_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4611_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
v___x_4614_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5);
v___x_4615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
v___x_4616_ = l_Lean_indentExpr(v_val_4597_);
v___x_4617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4615_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
v___x_4618_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4617_, v___y_4593_, v___y_4594_);
return v___x_4618_;
}
v___jp_4619_:
{
lean_object* v___x_4621_; 
v___x_4621_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7);
switch(lean_obj_tag(v_found_4591_))
{
case 0:
{
lean_object* v_v_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4630_; 
v_v_4622_ = lean_ctor_get(v_found_4591_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_found_4591_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4624_ = v_found_4591_;
v_isShared_4625_ = v_isSharedCheck_4630_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_v_4622_);
lean_dec(v_found_4591_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4630_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = l_String_quote(v_v_4622_);
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
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4628_;
goto v___jp_4598_;
}
}
}
case 1:
{
uint8_t v_v_4631_; 
v_v_4631_ = lean_ctor_get_uint8(v_found_4591_, 0);
lean_dec_ref_known(v_found_4591_, 0);
if (v_v_4631_ == 0)
{
lean_object* v___x_4632_; 
v___x_4632_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9));
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4632_;
goto v___jp_4598_;
}
else
{
lean_object* v___x_4633_; 
v___x_4633_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11));
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4633_;
goto v___jp_4598_;
}
}
case 2:
{
lean_object* v_v_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4645_; 
v_v_4634_ = lean_ctor_get(v_found_4591_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_found_4591_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4636_ = v_found_4591_;
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_v_4634_);
lean_dec(v_found_4591_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4638_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12));
v___x_4639_ = 1;
v___x_4640_ = l_Lean_Name_toString(v_v_4634_, v___x_4639_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set_tag(v___x_4636_, 3);
lean_ctor_set(v___x_4636_, 0, v___x_4640_);
v___x_4642_ = v___x_4636_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4638_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4643_;
goto v___jp_4598_;
}
}
}
case 3:
{
lean_object* v_v_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4654_; 
v_v_4646_ = lean_ctor_get(v_found_4591_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_found_4591_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4648_ = v_found_4591_;
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_v_4646_);
lean_dec(v_found_4591_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4650_ = l_Nat_reprFast(v_v_4646_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 0, v___x_4650_);
v___x_4652_ = v___x_4648_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4652_;
goto v___jp_4598_;
}
}
}
case 4:
{
lean_object* v_v_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4663_; 
v_v_4655_ = lean_ctor_get(v_found_4591_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_found_4591_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4657_ = v_found_4591_;
v_isShared_4658_ = v_isSharedCheck_4663_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_v_4655_);
lean_dec(v_found_4591_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4663_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4659_ = l_Int_repr(v_v_4655_);
lean_dec(v_v_4655_);
if (v_isShared_4658_ == 0)
{
lean_ctor_set_tag(v___x_4657_, 3);
lean_ctor_set(v___x_4657_, 0, v___x_4659_);
v___x_4661_ = v___x_4657_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4661_;
goto v___jp_4598_;
}
}
}
default: 
{
lean_object* v_v_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; lean_object* v___x_4667_; 
v_v_4664_ = lean_ctor_get(v_found_4591_, 0);
lean_inc(v_v_4664_);
lean_dec_ref_known(v_found_4591_, 1);
v___x_4665_ = lean_box(0);
v___x_4666_ = 0;
v___x_4667_ = l_Lean_Syntax_formatStx(v_v_4664_, v___x_4665_, v___x_4666_);
v___y_4599_ = v___y_4620_;
v___y_4600_ = v___x_4621_;
v___y_4601_ = v___x_4667_;
goto v___jp_4598_;
}
}
}
}
else
{
lean_object* v___x_4672_; 
lean_dec(v___x_4596_);
lean_dec_ref(v_found_4591_);
v___x_4672_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4590_, v___y_4593_, v___y_4594_);
return v___x_4672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_optionName_4673_, lean_object* v_found_4674_, lean_object* v_defVal_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4673_, v_found_4674_, v_defVal_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v_defVal_4675_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(lean_object* v_optionName_4680_, lean_object* v_decl_4681_, lean_object* v_val_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_defValue_4686_; uint8_t v___x_4687_; 
v_defValue_4686_ = lean_ctor_get(v_decl_4681_, 2);
v___x_4687_ = l_Lean_DataValue_sameCtor(v_defValue_4686_, v_val_4682_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4680_, v_val_4682_, v_defValue_4686_, v___y_4683_, v___y_4684_);
return v___x_4688_;
}
else
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_dec_ref(v_val_4682_);
lean_dec(v_optionName_4680_);
v___x_4689_ = lean_box(0);
v___x_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
return v___x_4690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5___boxed(lean_object* v_optionName_4691_, lean_object* v_decl_4692_, lean_object* v_val_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4691_, v_decl_4692_, v_val_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec_ref(v_decl_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(lean_object* v_optionName_4698_, lean_object* v_decl_4699_, lean_object* v_val_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; 
lean_inc_ref(v_val_4700_);
lean_inc(v_optionName_4698_);
v___x_4704_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4698_, v_decl_4699_, v_val_4700_, v___y_4701_, v___y_4702_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4718_; 
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4718_ == 0)
{
lean_object* v_unused_4719_; 
v_unused_4719_ = lean_ctor_get(v___x_4704_, 0);
lean_dec(v_unused_4719_);
v___x_4706_ = v___x_4704_;
v_isShared_4707_ = v_isSharedCheck_4718_;
goto v_resetjp_4705_;
}
else
{
lean_dec(v___x_4704_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4718_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v_scopes_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v_opts_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4708_ = lean_st_ref_get(v___y_4702_);
v_scopes_4709_ = lean_ctor_get(v___x_4708_, 2);
lean_inc(v_scopes_4709_);
lean_dec(v___x_4708_);
v___x_4710_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4711_ = l_List_head_x21___redArg(v___x_4710_, v_scopes_4709_);
lean_dec(v_scopes_4709_);
v_opts_4712_ = lean_ctor_get(v___x_4711_, 1);
lean_inc_ref(v_opts_4712_);
lean_dec(v___x_4711_);
v___x_4713_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(v_opts_4712_, v_optionName_4698_, v_val_4700_);
v___x_4714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
lean_ctor_set(v___x_4714_, 1, v_decl_4699_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4714_);
v___x_4716_ = v___x_4706_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec_ref(v_val_4700_);
lean_dec_ref(v_decl_4699_);
lean_dec(v_optionName_4698_);
v_a_4720_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4704_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4704_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3___boxed(lean_object* v_optionName_4728_, lean_object* v_decl_4729_, lean_object* v_val_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4728_, v_decl_4729_, v_val_4730_, v___y_4731_, v___y_4732_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
return v_res_4734_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0));
v___x_4737_ = l_Lean_stringToMessageData(v___x_4736_);
return v___x_4737_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4739_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2));
v___x_4740_ = l_Lean_stringToMessageData(v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(lean_object* v_id_4741_, lean_object* v_val_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_Elab_Command_getRef___redArg(v___y_4743_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4827_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc_n(v_a_4747_, 2);
lean_dec_ref_known(v___x_4746_, 1);
v___x_4748_ = l_Lean_Syntax_getArgs(v_a_4747_);
v___x_4749_ = lean_unsigned_to_nat(3u);
v___x_4750_ = lean_unsigned_to_nat(0u);
v___x_4751_ = l_Array_toSubarray___redArg(v___x_4748_, v___x_4750_, v___x_4749_);
v___x_4752_ = l_Subarray_copy___redArg(v___x_4751_);
v___x_4753_ = l_Lean_Syntax_setArgs(v_a_4747_, v___x_4752_);
v___x_4754_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
v___x_4755_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v___x_4754_, v___y_4743_, v___y_4744_);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4827_ == 0)
{
lean_object* v_unused_4828_; 
v_unused_4828_ = lean_ctor_get(v___x_4755_, 0);
lean_dec(v_unused_4828_);
v___x_4757_ = v___x_4755_;
v_isShared_4758_ = v_isSharedCheck_4827_;
goto v_resetjp_4756_;
}
else
{
lean_dec(v___x_4755_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4827_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v_optionName_4760_; lean_object* v___x_4761_; 
v___x_4759_ = l_Lean_Syntax_getId(v_id_4741_);
v_optionName_4760_ = lean_erase_macro_scopes(v___x_4759_);
lean_inc(v_optionName_4760_);
v___x_4761_ = l_Lean_getOptionDecl(v_optionName_4760_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v_declName_4763_; lean_object* v_defValue_4764_; lean_object* v___x_4765_; lean_object* v___x_4767_; 
lean_dec(v_a_4747_);
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v_declName_4763_ = lean_ctor_get(v_a_4762_, 1);
v_defValue_4764_ = lean_ctor_get(v_a_4762_, 2);
lean_inc(v_declName_4763_);
lean_inc(v_optionName_4760_);
v___x_4765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4765_, 0, v_id_4741_);
lean_ctor_set(v___x_4765_, 1, v_optionName_4760_);
lean_ctor_set(v___x_4765_, 2, v_declName_4763_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set_tag(v___x_4757_, 5);
lean_ctor_set(v___x_4757_, 0, v___x_4765_);
v___x_4767_ = v___x_4757_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4768_; lean_object* v___x_4783_; 
v___x_4768_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4767_, v___y_4743_, v___y_4744_);
lean_dec_ref(v___x_4768_);
v___x_4783_ = l_Lean_Syntax_isStrLit_x3f(v_val_4742_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Lean_Syntax_isNatLit_x3f(v_val_4742_);
if (lean_obj_tag(v___x_4784_) == 0)
{
if (lean_obj_tag(v_val_4742_) == 2)
{
lean_object* v_val_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v_val_4785_ = lean_ctor_get(v_val_4742_, 1);
v___x_4786_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10));
v___x_4787_ = lean_string_dec_eq(v_val_4785_, v___x_4786_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8));
v___x_4789_ = lean_string_dec_eq(v_val_4785_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_inc_ref(v_defValue_4764_);
lean_dec(v_a_4762_);
goto v___jp_4769_;
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_dec_ref_known(v_val_4742_, 2);
v___x_4790_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4790_, 0, v___x_4787_);
v___x_4791_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4760_, v_a_4762_, v___x_4790_, v___y_4743_, v___y_4744_);
return v___x_4791_;
}
}
else
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
lean_dec_ref_known(v_val_4742_, 2);
v___x_4792_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4792_, 0, v___x_4787_);
v___x_4793_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4760_, v_a_4762_, v___x_4792_, v___y_4743_, v___y_4744_);
return v___x_4793_;
}
}
else
{
lean_inc_ref(v_defValue_4764_);
lean_dec(v_a_4762_);
goto v___jp_4769_;
}
}
else
{
lean_object* v_val_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4802_; 
lean_dec(v_val_4742_);
v_val_4794_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4796_ = v___x_4784_;
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_val_4794_);
lean_dec(v___x_4784_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
lean_ctor_set_tag(v___x_4796_, 3);
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_val_4794_);
v___x_4799_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; 
v___x_4800_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4760_, v_a_4762_, v___x_4799_, v___y_4743_, v___y_4744_);
return v___x_4800_;
}
}
}
}
else
{
lean_object* v_val_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4811_; 
lean_dec(v_val_4742_);
v_val_4803_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4805_ = v___x_4783_;
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_val_4803_);
lean_dec(v___x_4783_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 0);
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_val_4803_);
v___x_4808_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; 
v___x_4809_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4760_, v_a_4762_, v___x_4808_, v___y_4743_, v___y_4744_);
return v___x_4809_;
}
}
}
v___jp_4769_:
{
lean_object* v___x_4770_; 
v___x_4770_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_4764_);
lean_dec_ref(v_defValue_4764_);
if (lean_obj_tag(v___x_4770_) == 1)
{
lean_object* v_val_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
lean_dec(v_optionName_4760_);
v_val_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_val_4771_);
lean_dec_ref_known(v___x_4770_, 1);
v___x_4772_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1);
v___x_4773_ = l_Lean_MessageData_ofSyntax(v_val_4742_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_MessageData_ofExpr(v_val_4771_);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4778_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4780_, v___y_4743_, v___y_4744_);
return v___x_4781_;
}
else
{
lean_object* v___x_4782_; 
lean_dec(v___x_4770_);
lean_dec(v_val_4742_);
v___x_4782_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4760_, v___y_4743_, v___y_4744_);
return v___x_4782_;
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v_optionName_4760_);
lean_dec(v_val_4742_);
lean_dec(v_id_4741_);
v_a_4813_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4815_ = v___x_4761_;
v_isShared_4816_ = v_isSharedCheck_4826_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4761_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4826_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; lean_object* v___x_4819_; 
v___x_4817_ = lean_io_error_to_string(v_a_4813_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set_tag(v___x_4757_, 3);
lean_ctor_set(v___x_4757_, 0, v___x_4817_);
v___x_4819_ = v___x_4757_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4820_ = l_Lean_MessageData_ofFormat(v___x_4819_);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v_a_4747_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4821_);
v___x_4823_ = v___x_4815_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec(v_val_4742_);
lean_dec(v_id_4741_);
v_a_4829_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4746_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4746_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___boxed(lean_object* v_id_4837_, lean_object* v_val_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v_id_4837_, v_val_4838_, v___y_4839_, v___y_4840_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object* v___x_4843_, lean_object* v___x_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v___x_4843_, v___x_4844_, v___y_4845_, v___y_4846_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4857_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v_fst_4853_; lean_object* v___x_4855_; 
v_fst_4853_ = lean_ctor_get(v_a_4849_, 0);
lean_inc(v_fst_4853_);
lean_dec(v_a_4849_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v_fst_4853_);
v___x_4855_ = v___x_4851_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_fst_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4874_; 
v_a_4858_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4860_ = v___x_4848_;
v_isShared_4861_ = v_isSharedCheck_4874_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4848_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4874_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
uint8_t v___x_4862_; 
v___x_4862_ = l_Lean_Exception_isInterrupt(v_a_4858_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; lean_object* v_scopes_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v_opts_4867_; lean_object* v___x_4869_; 
lean_dec(v_a_4858_);
v___x_4863_ = lean_st_ref_get(v___y_4846_);
v_scopes_4864_ = lean_ctor_get(v___x_4863_, 2);
lean_inc(v_scopes_4864_);
lean_dec(v___x_4863_);
v___x_4865_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4866_ = l_List_head_x21___redArg(v___x_4865_, v_scopes_4864_);
lean_dec(v_scopes_4864_);
v_opts_4867_ = lean_ctor_get(v___x_4866_, 1);
lean_inc_ref(v_opts_4867_);
lean_dec(v___x_4866_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set_tag(v___x_4860_, 0);
lean_ctor_set(v___x_4860_, 0, v_opts_4867_);
v___x_4869_ = v___x_4860_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_opts_4867_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
else
{
lean_object* v___x_4872_; 
if (v_isShared_4861_ == 0)
{
v___x_4872_ = v___x_4860_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4858_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object* v___x_4875_, lean_object* v___x_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(v___x_4875_, v___x_4876_, v___y_4877_, v___y_4878_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1(lean_object* v_a_4881_, lean_object* v_x_4882_){
_start:
{
lean_object* v_header_4883_; lean_object* v_currNamespace_4884_; lean_object* v_openDecls_4885_; lean_object* v_levelNames_4886_; lean_object* v_varDecls_4887_; lean_object* v_varUIds_4888_; lean_object* v_includedVars_4889_; lean_object* v_omittedVars_4890_; uint8_t v_isNoncomputable_4891_; uint8_t v_isPublic_4892_; uint8_t v_isMeta_4893_; lean_object* v_attrs_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
v_header_4883_ = lean_ctor_get(v_x_4882_, 0);
v_currNamespace_4884_ = lean_ctor_get(v_x_4882_, 2);
v_openDecls_4885_ = lean_ctor_get(v_x_4882_, 3);
v_levelNames_4886_ = lean_ctor_get(v_x_4882_, 4);
v_varDecls_4887_ = lean_ctor_get(v_x_4882_, 5);
v_varUIds_4888_ = lean_ctor_get(v_x_4882_, 6);
v_includedVars_4889_ = lean_ctor_get(v_x_4882_, 7);
v_omittedVars_4890_ = lean_ctor_get(v_x_4882_, 8);
v_isNoncomputable_4891_ = lean_ctor_get_uint8(v_x_4882_, sizeof(void*)*10);
v_isPublic_4892_ = lean_ctor_get_uint8(v_x_4882_, sizeof(void*)*10 + 1);
v_isMeta_4893_ = lean_ctor_get_uint8(v_x_4882_, sizeof(void*)*10 + 2);
v_attrs_4894_ = lean_ctor_get(v_x_4882_, 9);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_x_4882_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v_x_4882_, 1);
lean_dec(v_unused_4902_);
v___x_4896_ = v_x_4882_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_attrs_4894_);
lean_inc(v_omittedVars_4890_);
lean_inc(v_includedVars_4889_);
lean_inc(v_varUIds_4888_);
lean_inc(v_varDecls_4887_);
lean_inc(v_levelNames_4886_);
lean_inc(v_openDecls_4885_);
lean_inc(v_currNamespace_4884_);
lean_inc(v_header_4883_);
lean_dec(v_x_4882_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 1, v_a_4881_);
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_header_4883_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_a_4881_);
lean_ctor_set(v_reuseFailAlloc_4900_, 2, v_currNamespace_4884_);
lean_ctor_set(v_reuseFailAlloc_4900_, 3, v_openDecls_4885_);
lean_ctor_set(v_reuseFailAlloc_4900_, 4, v_levelNames_4886_);
lean_ctor_set(v_reuseFailAlloc_4900_, 5, v_varDecls_4887_);
lean_ctor_set(v_reuseFailAlloc_4900_, 6, v_varUIds_4888_);
lean_ctor_set(v_reuseFailAlloc_4900_, 7, v_includedVars_4889_);
lean_ctor_set(v_reuseFailAlloc_4900_, 8, v_omittedVars_4890_);
lean_ctor_set(v_reuseFailAlloc_4900_, 9, v_attrs_4894_);
lean_ctor_set_uint8(v_reuseFailAlloc_4900_, sizeof(void*)*10, v_isNoncomputable_4891_);
lean_ctor_set_uint8(v_reuseFailAlloc_4900_, sizeof(void*)*10 + 1, v_isPublic_4892_);
lean_ctor_set_uint8(v_reuseFailAlloc_4900_, sizeof(void*)*10 + 2, v_isMeta_4893_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(uint8_t v_flag_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v___x_4906_; lean_object* v_infoState_4907_; lean_object* v_env_4908_; lean_object* v_messages_4909_; lean_object* v_scopes_4910_; lean_object* v_usedQuotCtxts_4911_; lean_object* v_nextMacroScope_4912_; lean_object* v_maxRecDepth_4913_; lean_object* v_ngen_4914_; lean_object* v_auxDeclNGen_4915_; lean_object* v_traceState_4916_; lean_object* v_snapshotTasks_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4937_; 
v___x_4906_ = lean_st_ref_take(v___y_4904_);
v_infoState_4907_ = lean_ctor_get(v___x_4906_, 8);
v_env_4908_ = lean_ctor_get(v___x_4906_, 0);
v_messages_4909_ = lean_ctor_get(v___x_4906_, 1);
v_scopes_4910_ = lean_ctor_get(v___x_4906_, 2);
v_usedQuotCtxts_4911_ = lean_ctor_get(v___x_4906_, 3);
v_nextMacroScope_4912_ = lean_ctor_get(v___x_4906_, 4);
v_maxRecDepth_4913_ = lean_ctor_get(v___x_4906_, 5);
v_ngen_4914_ = lean_ctor_get(v___x_4906_, 6);
v_auxDeclNGen_4915_ = lean_ctor_get(v___x_4906_, 7);
v_traceState_4916_ = lean_ctor_get(v___x_4906_, 9);
v_snapshotTasks_4917_ = lean_ctor_get(v___x_4906_, 10);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4919_ = v___x_4906_;
v_isShared_4920_ = v_isSharedCheck_4937_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_snapshotTasks_4917_);
lean_inc(v_traceState_4916_);
lean_inc(v_infoState_4907_);
lean_inc(v_auxDeclNGen_4915_);
lean_inc(v_ngen_4914_);
lean_inc(v_maxRecDepth_4913_);
lean_inc(v_nextMacroScope_4912_);
lean_inc(v_usedQuotCtxts_4911_);
lean_inc(v_scopes_4910_);
lean_inc(v_messages_4909_);
lean_inc(v_env_4908_);
lean_dec(v___x_4906_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4937_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v_assignment_4921_; lean_object* v_lazyAssignment_4922_; lean_object* v_trees_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4936_; 
v_assignment_4921_ = lean_ctor_get(v_infoState_4907_, 0);
v_lazyAssignment_4922_ = lean_ctor_get(v_infoState_4907_, 1);
v_trees_4923_ = lean_ctor_get(v_infoState_4907_, 2);
v_isSharedCheck_4936_ = !lean_is_exclusive(v_infoState_4907_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4925_ = v_infoState_4907_;
v_isShared_4926_ = v_isSharedCheck_4936_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_trees_4923_);
lean_inc(v_lazyAssignment_4922_);
lean_inc(v_assignment_4921_);
lean_dec(v_infoState_4907_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4936_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_assignment_4921_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_lazyAssignment_4922_);
lean_ctor_set(v_reuseFailAlloc_4935_, 2, v_trees_4923_);
v___x_4928_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4930_; 
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*3, v_flag_4903_);
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 8, v___x_4928_);
v___x_4930_ = v___x_4919_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_env_4908_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_messages_4909_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_scopes_4910_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_usedQuotCtxts_4911_);
lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_nextMacroScope_4912_);
lean_ctor_set(v_reuseFailAlloc_4934_, 5, v_maxRecDepth_4913_);
lean_ctor_set(v_reuseFailAlloc_4934_, 6, v_ngen_4914_);
lean_ctor_set(v_reuseFailAlloc_4934_, 7, v_auxDeclNGen_4915_);
lean_ctor_set(v_reuseFailAlloc_4934_, 8, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4934_, 9, v_traceState_4916_);
lean_ctor_set(v_reuseFailAlloc_4934_, 10, v_snapshotTasks_4917_);
v___x_4930_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4931_ = lean_st_ref_set(v___y_4904_, v___x_4930_);
v___x_4932_ = lean_box(0);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg___boxed(lean_object* v_flag_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
uint8_t v_flag_boxed_4941_; lean_object* v_res_4942_; 
v_flag_boxed_4941_ = lean_unbox(v_flag_4938_);
v_res_4942_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_boxed_4941_, v___y_4939_);
lean_dec(v___y_4939_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(uint8_t v_flag_4943_, lean_object* v_x_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v___x_4948_; lean_object* v_infoState_4949_; uint8_t v_enabled_4950_; lean_object* v_a_4952_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4948_ = lean_st_ref_get(v___y_4946_);
v_infoState_4949_ = lean_ctor_get(v___x_4948_, 8);
lean_inc_ref(v_infoState_4949_);
lean_dec(v___x_4948_);
v_enabled_4950_ = lean_ctor_get_uint8(v_infoState_4949_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4949_);
v___x_4962_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_4943_, v___y_4946_);
lean_dec_ref(v___x_4962_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
v___x_4963_ = lean_apply_3(v_x_4944_, v___y_4945_, v___y_4946_, lean_box(0));
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v___x_4965_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4950_, v___y_4946_);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4972_ == 0)
{
lean_object* v_unused_4973_; 
v_unused_4973_ = lean_ctor_get(v___x_4965_, 0);
lean_dec(v_unused_4973_);
v___x_4967_ = v___x_4965_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_dec(v___x_4965_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v_a_4964_);
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4964_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
else
{
lean_object* v_a_4974_; 
v_a_4974_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4963_, 1);
v_a_4952_ = v_a_4974_;
goto v___jp_4951_;
}
v___jp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
v___x_4953_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4950_, v___y_4946_);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4960_ == 0)
{
lean_object* v_unused_4961_; 
v_unused_4961_ = lean_ctor_get(v___x_4953_, 0);
lean_dec(v_unused_4961_);
v___x_4955_ = v___x_4953_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_dec(v___x_4953_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set_tag(v___x_4955_, 1);
lean_ctor_set(v___x_4955_, 0, v_a_4952_);
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4952_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg___boxed(lean_object* v_flag_4975_, lean_object* v_x_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
uint8_t v_flag_boxed_4980_; lean_object* v_res_4981_; 
v_flag_boxed_4980_ = lean_unbox(v_flag_4975_);
v_res_4981_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_boxed_4980_, v_x_4976_, v___y_4977_, v___y_4978_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object* v_stx_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; uint8_t v___x_4996_; 
v___x_4992_ = lean_unsigned_to_nat(0u);
v___x_4993_ = l_Lean_Syntax_getArg(v_stx_4988_, v___x_4992_);
lean_inc(v___x_4993_);
v___x_4994_ = l_Lean_Syntax_getKind(v___x_4993_);
v___x_4995_ = ((lean_object*)(l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1));
v___x_4996_ = lean_name_eq(v___x_4994_, v___x_4995_);
lean_dec(v___x_4994_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; lean_object* v_run_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
lean_dec(v___x_4993_);
v___x_4997_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4998_ = lean_ctor_get(v___x_4997_, 0);
v___x_4999_ = lean_unsigned_to_nat(2u);
v___x_5000_ = l_Lean_Syntax_getArg(v_stx_4988_, v___x_4999_);
lean_inc_ref(v_run_4998_);
lean_inc(v_a_4990_);
lean_inc_ref(v_a_4989_);
v___x_5001_ = lean_apply_4(v_run_4998_, v___x_5000_, v_a_4989_, v_a_4990_, lean_box(0));
return v___x_5001_;
}
else
{
uint8_t v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___f_5007_; lean_object* v___x_5008_; 
v___x_5002_ = 0;
v___x_5003_ = lean_unsigned_to_nat(1u);
v___x_5004_ = l_Lean_Syntax_getArg(v___x_4993_, v___x_5003_);
v___x_5005_ = lean_unsigned_to_nat(3u);
v___x_5006_ = l_Lean_Syntax_getArg(v___x_4993_, v___x_5005_);
lean_dec(v___x_4993_);
v___f_5007_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_5007_, 0, v___x_5004_);
lean_closure_set(v___f_5007_, 1, v___x_5006_);
v___x_5008_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v___x_5002_, v___f_5007_, v_a_4989_, v_a_4990_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___x_5010_; lean_object* v_run_5011_; lean_object* v___f_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_a_5009_);
lean_dec_ref_known(v___x_5008_, 1);
v___x_5010_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_5011_ = lean_ctor_get(v___x_5010_, 0);
v___f_5012_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5012_, 0, v_a_5009_);
v___x_5013_ = lean_unsigned_to_nat(2u);
v___x_5014_ = l_Lean_Syntax_getArg(v_stx_4988_, v___x_5013_);
lean_inc_ref(v_run_5011_);
v___x_5015_ = lean_apply_1(v_run_5011_, v___x_5014_);
v___x_5016_ = l_Lean_Elab_Command_withScope___redArg(v___f_5012_, v___x_5015_, v_a_4989_, v_a_4990_);
return v___x_5016_;
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v_a_5017_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5008_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5008_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object* v_stx_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_5025_, v_a_5026_, v_a_5027_);
lean_dec(v_a_5027_);
lean_dec_ref(v_a_5026_);
lean_dec(v_stx_5025_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t v_x_5030_, lean_object* v_stx_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_5031_, v_a_5032_, v_a_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object* v_x_5036_, lean_object* v_stx_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
uint8_t v_x_4511__boxed_5041_; lean_object* v_res_5042_; 
v_x_4511__boxed_5041_ = lean_unbox(v_x_5036_);
v_res_5042_ = l_Lean_Linter_MissingDocs_handleIn(v_x_4511__boxed_5041_, v_stx_5037_, v_a_5038_, v_a_5039_);
lean_dec(v_a_5039_);
lean_dec_ref(v_a_5038_);
lean_dec(v_stx_5037_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(uint8_t v_flag_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_5043_, v___y_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___boxed(lean_object* v_flag_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
uint8_t v_flag_boxed_5052_; lean_object* v_res_5053_; 
v_flag_boxed_5052_ = lean_unbox(v_flag_5048_);
v_res_5053_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(v_flag_boxed_5052_, v___y_5049_, v___y_5050_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(lean_object* v_00_u03b1_5054_, uint8_t v_flag_5055_, lean_object* v_x_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_5055_, v_x_5056_, v___y_5057_, v___y_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___boxed(lean_object* v_00_u03b1_5061_, lean_object* v_flag_5062_, lean_object* v_x_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
uint8_t v_flag_boxed_5067_; lean_object* v_res_5068_; 
v_flag_boxed_5067_ = lean_unbox(v_flag_5062_);
v_res_5068_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(v_00_u03b1_5061_, v_flag_boxed_5067_, v_x_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(lean_object* v_t_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v___x_5073_; 
v___x_5073_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_5069_, v___y_5071_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___boxed(lean_object* v_t_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(v_t_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(lean_object* v_00_u03b1_5079_, lean_object* v_optionName_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_5080_, v___y_5081_, v___y_5082_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___boxed(lean_object* v_00_u03b1_5085_, lean_object* v_optionName_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(v_00_u03b1_5085_, v_optionName_5086_, v___y_5087_, v___y_5088_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(){
_start:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5098_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1));
v___x_5099_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___boxed), 5, 0);
v___x_5100_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5098_, v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___boxed(lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object* v_as_5103_, size_t v_i_5104_, size_t v_stop_5105_, lean_object* v_b_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v___x_5110_; lean_object* v_run_5111_; uint8_t v___x_5112_; 
v___x_5110_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_5111_ = lean_ctor_get(v___x_5110_, 0);
v___x_5112_ = lean_usize_dec_eq(v_i_5104_, v_stop_5105_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = lean_array_uget_borrowed(v_as_5103_, v_i_5104_);
lean_inc_ref(v_run_5111_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
lean_inc(v___x_5113_);
v___x_5114_ = lean_apply_4(v_run_5111_, v___x_5113_, v___y_5107_, v___y_5108_, lean_box(0));
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_a_5115_; size_t v___x_5116_; size_t v___x_5117_; 
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
lean_inc(v_a_5115_);
lean_dec_ref_known(v___x_5114_, 1);
v___x_5116_ = ((size_t)1ULL);
v___x_5117_ = lean_usize_add(v_i_5104_, v___x_5116_);
v_i_5104_ = v___x_5117_;
v_b_5106_ = v_a_5115_;
goto _start;
}
else
{
return v___x_5114_;
}
}
else
{
lean_object* v___x_5119_; 
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v_b_5106_);
return v___x_5119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object* v_as_5120_, lean_object* v_i_5121_, lean_object* v_stop_5122_, lean_object* v_b_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
size_t v_i_boxed_5127_; size_t v_stop_boxed_5128_; lean_object* v_res_5129_; 
v_i_boxed_5127_ = lean_unbox_usize(v_i_5121_);
lean_dec(v_i_5121_);
v_stop_boxed_5128_ = lean_unbox_usize(v_stop_5122_);
lean_dec(v_stop_5122_);
v_res_5129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v_as_5120_, v_i_boxed_5127_, v_stop_boxed_5128_, v_b_5123_, v___y_5124_, v___y_5125_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec_ref(v_as_5120_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object* v_stx_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = l_Lean_Syntax_getArg(v_stx_5130_, v___x_5134_);
v___x_5136_ = l_Lean_Syntax_getArgs(v___x_5135_);
lean_dec(v___x_5135_);
v___x_5137_ = lean_unsigned_to_nat(0u);
v___x_5138_ = lean_array_get_size(v___x_5136_);
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_nat_dec_lt(v___x_5137_, v___x_5138_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; 
lean_dec_ref(v___x_5136_);
v___x_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
return v___x_5141_;
}
else
{
uint8_t v___x_5142_; 
v___x_5142_ = lean_nat_dec_le(v___x_5138_, v___x_5138_);
if (v___x_5142_ == 0)
{
if (v___x_5140_ == 0)
{
lean_object* v___x_5143_; 
lean_dec_ref(v___x_5136_);
v___x_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5139_);
return v___x_5143_;
}
else
{
size_t v___x_5144_; size_t v___x_5145_; lean_object* v___x_5146_; 
v___x_5144_ = ((size_t)0ULL);
v___x_5145_ = lean_usize_of_nat(v___x_5138_);
v___x_5146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5136_, v___x_5144_, v___x_5145_, v___x_5139_, v_a_5131_, v_a_5132_);
lean_dec_ref(v___x_5136_);
return v___x_5146_;
}
}
else
{
size_t v___x_5147_; size_t v___x_5148_; lean_object* v___x_5149_; 
v___x_5147_ = ((size_t)0ULL);
v___x_5148_ = lean_usize_of_nat(v___x_5138_);
v___x_5149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5136_, v___x_5147_, v___x_5148_, v___x_5139_, v_a_5131_, v_a_5132_);
lean_dec_ref(v___x_5136_);
return v___x_5149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object* v_stx_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5150_, v_a_5151_, v_a_5152_);
lean_dec(v_a_5152_);
lean_dec_ref(v_a_5151_);
lean_dec(v_stx_5150_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t v_x_5155_, lean_object* v_stx_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5156_, v_a_5157_, v_a_5158_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object* v_x_5161_, lean_object* v_stx_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
uint8_t v_x_403__boxed_5166_; lean_object* v_res_5167_; 
v_x_403__boxed_5166_ = lean_unbox(v_x_5161_);
v_res_5167_ = l_Lean_Linter_MissingDocs_handleMutual(v_x_403__boxed_5166_, v_stx_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec(v_stx_5162_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(){
_start:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5175_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1));
v___x_5176_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleMutual___boxed), 5, 0);
v___x_5177_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5175_, v___x_5176_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___boxed(lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
return v_res_5179_;
}
}
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_MissingDocs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
