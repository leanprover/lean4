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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
v___x_543_ = lean_st_ref_put(v___y_527_, v___x_542_);
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
v___x_569_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_569_, 10, v___x_567_);
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
return v___x_927_;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(lean_object* v_x_938_, size_t v_x_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_es_941_; lean_object* v___x_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v_j_945_; lean_object* v___x_946_; 
v_es_941_ = lean_ctor_get(v_x_938_, 0);
v___x_942_ = lean_box(2);
v___x_943_ = ((size_t)31ULL);
v___x_944_ = lean_usize_land(v_x_939_, v___x_943_);
v_j_945_ = lean_usize_to_nat(v___x_944_);
v___x_946_ = lean_array_get_borrowed(v___x_942_, v_es_941_, v_j_945_);
lean_dec(v_j_945_);
switch(lean_obj_tag(v___x_946_))
{
case 0:
{
lean_object* v_key_947_; uint8_t v___x_948_; 
v_key_947_ = lean_ctor_get(v___x_946_, 0);
v___x_948_ = l_Lean_instBEqExtraModUse_beq(v_x_940_, v_key_947_);
return v___x_948_;
}
case 1:
{
lean_object* v_node_949_; size_t v___x_950_; size_t v___x_951_; 
v_node_949_ = lean_ctor_get(v___x_946_, 0);
v___x_950_ = ((size_t)5ULL);
v___x_951_ = lean_usize_shift_right(v_x_939_, v___x_950_);
v_x_938_ = v_node_949_;
v_x_939_ = v___x_951_;
goto _start;
}
default: 
{
uint8_t v___x_953_; 
v___x_953_ = 0;
return v___x_953_;
}
}
}
else
{
lean_object* v_ks_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_ks_954_ = lean_ctor_get(v_x_938_, 0);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_ks_954_, v___x_955_, v_x_940_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
size_t v_x_8834__boxed_960_; uint8_t v_res_961_; lean_object* v_r_962_; 
v_x_8834__boxed_960_ = lean_unbox_usize(v_x_958_);
lean_dec(v_x_958_);
v_res_961_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_957_, v_x_8834__boxed_960_, v_x_959_);
lean_dec_ref(v_x_959_);
lean_dec_ref(v_x_957_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
uint64_t v___x_965_; size_t v___x_966_; uint8_t v___x_967_; 
v___x_965_ = l_Lean_instHashableExtraModUse_hash(v_x_964_);
v___x_966_ = lean_uint64_to_usize(v___x_965_);
v___x_967_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_963_, v___x_966_, v_x_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_968_, v_x_969_);
lean_dec_ref(v_x_969_);
lean_dec_ref(v_x_968_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_972_; double v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_float_of_nat(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_cls_977_, lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_ref_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1028_; 
v_ref_982_ = lean_ctor_get(v___y_979_, 5);
v___x_983_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_978_, v___y_979_, v___y_980_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1028_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1028_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v_traceState_989_; lean_object* v_env_990_; lean_object* v_nextMacroScope_991_; lean_object* v_ngen_992_; lean_object* v_auxDeclNGen_993_; lean_object* v_cache_994_; lean_object* v_messages_995_; lean_object* v_infoState_996_; lean_object* v_snapshotTasks_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1027_; 
v___x_988_ = lean_st_ref_take(v___y_980_);
v_traceState_989_ = lean_ctor_get(v___x_988_, 4);
v_env_990_ = lean_ctor_get(v___x_988_, 0);
v_nextMacroScope_991_ = lean_ctor_get(v___x_988_, 1);
v_ngen_992_ = lean_ctor_get(v___x_988_, 2);
v_auxDeclNGen_993_ = lean_ctor_get(v___x_988_, 3);
v_cache_994_ = lean_ctor_get(v___x_988_, 5);
v_messages_995_ = lean_ctor_get(v___x_988_, 6);
v_infoState_996_ = lean_ctor_get(v___x_988_, 7);
v_snapshotTasks_997_ = lean_ctor_get(v___x_988_, 8);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_999_ = v___x_988_;
v_isShared_1000_ = v_isSharedCheck_1027_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snapshotTasks_997_);
lean_inc(v_infoState_996_);
lean_inc(v_messages_995_);
lean_inc(v_cache_994_);
lean_inc(v_traceState_989_);
lean_inc(v_auxDeclNGen_993_);
lean_inc(v_ngen_992_);
lean_inc(v_nextMacroScope_991_);
lean_inc(v_env_990_);
lean_dec(v___x_988_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1027_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
uint64_t v_tid_1001_; lean_object* v_traces_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1026_; 
v_tid_1001_ = lean_ctor_get_uint64(v_traceState_989_, sizeof(void*)*1);
v_traces_1002_ = lean_ctor_get(v_traceState_989_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_traceState_989_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1004_ = v_traceState_989_;
v_isShared_1005_ = v_isSharedCheck_1026_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_traces_1002_);
lean_dec(v_traceState_989_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1026_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; double v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0);
v___x_1008_ = 0;
v___x_1009_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1010_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1010_, 0, v_cls_977_);
lean_ctor_set(v___x_1010_, 1, v___x_1006_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
lean_ctor_set_float(v___x_1010_, sizeof(void*)*3, v___x_1007_);
lean_ctor_set_float(v___x_1010_, sizeof(void*)*3 + 8, v___x_1007_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*3 + 16, v___x_1008_);
v___x_1011_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2));
v___x_1012_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v_a_984_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
lean_inc(v_ref_982_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_ref_982_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_PersistentArray_push___redArg(v_traces_1002_, v___x_1013_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1014_);
v___x_1016_ = v___x_1004_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1014_);
lean_ctor_set_uint64(v_reuseFailAlloc_1025_, sizeof(void*)*1, v_tid_1001_);
v___x_1016_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 4, v___x_1016_);
v___x_1018_ = v___x_999_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_env_990_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_nextMacroScope_991_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_ngen_992_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_auxDeclNGen_993_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 5, v_cache_994_);
lean_ctor_set(v_reuseFailAlloc_1024_, 6, v_messages_995_);
lean_ctor_set(v_reuseFailAlloc_1024_, 7, v_infoState_996_);
lean_ctor_set(v_reuseFailAlloc_1024_, 8, v_snapshotTasks_997_);
v___x_1018_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1019_ = lean_st_ref_put(v___y_980_, v___x_1018_);
v___x_1020_ = lean_box(0);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1020_);
v___x_1022_ = v___x_986_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_cls_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1029_, v_msg_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1));
v___x_1038_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0));
v___x_1039_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1038_, v___x_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_cls_1054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4));
v___x_1055_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_1056_ = l_Lean_Name_append(v___x_1055_, v_cls_1054_);
return v___x_1056_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_mod_1067_, uint8_t v_isMeta_1068_, lean_object* v_hint_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_env_1074_; uint8_t v_isExporting_1075_; lean_object* v___x_1076_; lean_object* v_env_1077_; lean_object* v___x_1078_; lean_object* v_entry_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___y_1084_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1073_ = lean_st_ref_get(v___y_1071_);
v_env_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1074_);
lean_dec(v___x_1073_);
v_isExporting_1075_ = lean_ctor_get_uint8(v_env_1074_, sizeof(void*)*8);
lean_dec_ref(v_env_1074_);
v___x_1076_ = lean_st_ref_get(v___y_1071_);
v_env_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_env_1077_);
lean_dec(v___x_1076_);
v___x_1078_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2);
lean_inc(v_mod_1067_);
v_entry_1079_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1079_, 0, v_mod_1067_);
lean_ctor_set_uint8(v_entry_1079_, sizeof(void*)*1, v_isExporting_1075_);
lean_ctor_set_uint8(v_entry_1079_, sizeof(void*)*1 + 1, v_isMeta_1068_);
v___x_1080_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1081_ = lean_box(1);
v___x_1082_ = lean_box(0);
v___x_1109_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1078_, v___x_1080_, v_env_1077_, v___x_1081_, v___x_1082_);
v___x_1110_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_1109_, v_entry_1079_);
lean_dec(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v_options_1111_; uint8_t v_hasTrace_1112_; 
v_options_1111_ = lean_ctor_get(v___y_1070_, 2);
v_hasTrace_1112_ = lean_ctor_get_uint8(v_options_1111_, sizeof(void*)*1);
if (v_hasTrace_1112_ == 0)
{
lean_dec(v_hint_1069_);
lean_dec(v_mod_1067_);
v___y_1084_ = v___y_1071_;
goto v___jp_1083_;
}
else
{
lean_object* v_inheritedTraceOptions_1113_; lean_object* v_cls_1114_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_inheritedTraceOptions_1113_ = lean_ctor_get(v___y_1070_, 13);
v_cls_1114_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4));
v___x_1134_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12);
v___x_1135_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1113_, v_options_1111_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec(v_hint_1069_);
lean_dec(v_mod_1067_);
v___y_1084_ = v___y_1071_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1136_; lean_object* v___y_1138_; 
v___x_1136_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14);
if (v_isExporting_1075_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__19));
v___y_1138_ = v___x_1145_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__20));
v___y_1138_ = v___x_1146_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v___y_1138_);
v___x_1139_ = l_Lean_stringToMessageData(v___y_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1136_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
if (v_isMeta_1068_ == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17));
v___y_1121_ = v___x_1142_;
v___y_1122_ = v___x_1143_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18));
v___y_1121_ = v___x_1142_;
v___y_1122_ = v___x_1144_;
goto v___jp_1120_;
}
}
}
v___jp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1116_);
lean_ctor_set(v___x_1118_, 1, v___y_1117_);
v___x_1119_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1114_, v___x_1118_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref_known(v___x_1119_, 1);
v___y_1084_ = v___y_1071_;
goto v___jp_1083_;
}
else
{
lean_dec_ref_known(v_entry_1079_, 1);
return v___x_1119_;
}
}
v___jp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
lean_inc_ref(v___y_1122_);
v___x_1123_ = l_Lean_stringToMessageData(v___y_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___y_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_ofName(v_mod_1067_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_Name_isAnonymous(v_hint_1069_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8);
v___x_1131_ = l_Lean_MessageData_ofName(v_hint_1069_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___y_1116_ = v___x_1128_;
v___y_1117_ = v___x_1132_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_hint_1069_);
v___x_1133_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9);
v___y_1116_ = v___x_1128_;
v___y_1117_ = v___x_1133_;
goto v___jp_1115_;
}
}
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref_known(v_entry_1079_, 1);
lean_dec(v_hint_1069_);
lean_dec(v_mod_1067_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v_toEnvExtension_1086_; lean_object* v_env_1087_; lean_object* v_nextMacroScope_1088_; lean_object* v_ngen_1089_; lean_object* v_auxDeclNGen_1090_; lean_object* v_traceState_1091_; lean_object* v_messages_1092_; lean_object* v_infoState_1093_; lean_object* v_snapshotTasks_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1107_; 
v___x_1085_ = lean_st_ref_take(v___y_1084_);
v_toEnvExtension_1086_ = lean_ctor_get(v___x_1080_, 0);
v_env_1087_ = lean_ctor_get(v___x_1085_, 0);
v_nextMacroScope_1088_ = lean_ctor_get(v___x_1085_, 1);
v_ngen_1089_ = lean_ctor_get(v___x_1085_, 2);
v_auxDeclNGen_1090_ = lean_ctor_get(v___x_1085_, 3);
v_traceState_1091_ = lean_ctor_get(v___x_1085_, 4);
v_messages_1092_ = lean_ctor_get(v___x_1085_, 6);
v_infoState_1093_ = lean_ctor_get(v___x_1085_, 7);
v_snapshotTasks_1094_ = lean_ctor_get(v___x_1085_, 8);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1085_, 5);
lean_dec(v_unused_1108_);
v___x_1096_ = v___x_1085_;
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snapshotTasks_1094_);
lean_inc(v_infoState_1093_);
lean_inc(v_messages_1092_);
lean_inc(v_traceState_1091_);
lean_inc(v_auxDeclNGen_1090_);
lean_inc(v_ngen_1089_);
lean_inc(v_nextMacroScope_1088_);
lean_inc(v_env_1087_);
lean_dec(v___x_1085_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_asyncMode_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v_asyncMode_1098_ = lean_ctor_get(v_toEnvExtension_1086_, 2);
v___x_1099_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1080_, v_env_1087_, v_entry_1079_, v_asyncMode_1098_, v___x_1082_);
v___x_1100_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 5, v___x_1100_);
lean_ctor_set(v___x_1096_, 0, v___x_1099_);
v___x_1102_ = v___x_1096_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_nextMacroScope_1088_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_ngen_1089_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_auxDeclNGen_1090_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_traceState_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 5, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 6, v_messages_1092_);
lean_ctor_set(v_reuseFailAlloc_1106_, 7, v_infoState_1093_);
lean_ctor_set(v_reuseFailAlloc_1106_, 8, v_snapshotTasks_1094_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_st_ref_put(v___y_1084_, v___x_1102_);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_mod_1149_, lean_object* v_isMeta_1150_, lean_object* v_hint_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v_isMeta_boxed_1155_; lean_object* v_res_1156_; 
v_isMeta_boxed_1155_ = lean_unbox(v_isMeta_1150_);
v_res_1156_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_mod_1149_, v_isMeta_boxed_1155_, v_hint_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object* v___x_1157_, lean_object* v_declName_1158_, lean_object* v_as_1159_, size_t v_sz_1160_, size_t v_i_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_usize_dec_lt(v_i_1161_, v_sz_1160_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_dec(v_declName_1158_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_b_1162_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v_modules_1169_; lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v_toImport_1173_; lean_object* v_module_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1168_ = l_Lean_Environment_header(v___x_1157_);
v_modules_1169_ = lean_ctor_get(v___x_1168_, 3);
lean_inc_ref(v_modules_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1171_ = lean_array_uget_borrowed(v_as_1159_, v_i_1161_);
v___x_1172_ = lean_array_get(v___x_1170_, v_modules_1169_, v_a_1171_);
lean_dec_ref(v_modules_1169_);
v_toImport_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_ref(v_toImport_1173_);
lean_dec(v___x_1172_);
v_module_1174_ = lean_ctor_get(v_toImport_1173_, 0);
lean_inc(v_module_1174_);
lean_dec_ref(v_toImport_1173_);
v___x_1175_ = 0;
lean_inc(v_declName_1158_);
v___x_1176_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1174_, v___x_1175_, v_declName_1158_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; 
lean_dec_ref_known(v___x_1176_, 1);
v___x_1177_ = lean_box(0);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1161_, v___x_1178_);
v_i_1161_ = v___x_1179_;
v_b_1162_ = v___x_1177_;
goto _start;
}
else
{
lean_dec(v_declName_1158_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v___x_1181_, lean_object* v_declName_1182_, lean_object* v_as_1183_, lean_object* v_sz_1184_, lean_object* v_i_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; lean_object* v_res_1192_; 
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1184_);
lean_dec(v_sz_1184_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1185_);
lean_dec(v_i_1185_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v___x_1181_, v_declName_1182_, v_as_1183_, v_sz_boxed_1190_, v_i_boxed_1191_, v_b_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_as_1183_);
lean_dec_ref(v___x_1181_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
else
{
lean_object* v_key_1196_; lean_object* v_value_1197_; lean_object* v_tail_1198_; uint8_t v___x_1199_; 
v_key_1196_ = lean_ctor_get(v_x_1194_, 0);
v_value_1197_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1198_ = lean_ctor_get(v_x_1194_, 2);
v___x_1199_ = lean_name_eq(v_key_1196_, v_a_1193_);
if (v___x_1199_ == 0)
{
v_x_1194_ = v_tail_1198_;
goto _start;
}
else
{
lean_object* v___x_1201_; 
lean_inc(v_value_1197_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_value_1197_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1202_, v_x_1203_);
lean_dec(v_x_1203_);
lean_dec(v_a_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_buckets_1207_; lean_object* v___x_1208_; uint64_t v___y_1210_; 
v_buckets_1207_ = lean_ctor_get(v_m_1205_, 1);
v___x_1208_ = lean_array_get_size(v_buckets_1207_);
if (lean_obj_tag(v_a_1206_) == 0)
{
uint64_t v___x_1224_; 
v___x_1224_ = 1723ULL;
v___y_1210_ = v___x_1224_;
goto v___jp_1209_;
}
else
{
uint64_t v_hash_1225_; 
v_hash_1225_ = lean_ctor_get_uint64(v_a_1206_, sizeof(void*)*2);
v___y_1210_ = v_hash_1225_;
goto v___jp_1209_;
}
v___jp_1209_:
{
uint64_t v___x_1211_; uint64_t v___x_1212_; uint64_t v_fold_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; uint64_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1211_ = 32ULL;
v___x_1212_ = lean_uint64_shift_right(v___y_1210_, v___x_1211_);
v_fold_1213_ = lean_uint64_xor(v___y_1210_, v___x_1212_);
v___x_1214_ = 16ULL;
v___x_1215_ = lean_uint64_shift_right(v_fold_1213_, v___x_1214_);
v___x_1216_ = lean_uint64_xor(v_fold_1213_, v___x_1215_);
v___x_1217_ = lean_uint64_to_usize(v___x_1216_);
v___x_1218_ = lean_usize_of_nat(v___x_1208_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_sub(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_usize_land(v___x_1217_, v___x_1220_);
v___x_1222_ = lean_array_uget_borrowed(v_buckets_1207_, v___x_1221_);
v___x_1223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1206_, v___x_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object* v_m_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_m_1226_);
return v_res_1228_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1));
v___x_1232_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0));
v___x_1233_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1232_, v___x_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(lean_object* v_declName_1236_, uint8_t v_isMeta_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_env_1245_; lean_object* v___y_1247_; lean_object* v___x_1260_; 
v___x_1241_ = lean_st_ref_get(v___y_1239_);
v_env_1245_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_env_1245_);
lean_dec(v___x_1241_);
v___x_1260_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1245_, v_declName_1236_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_dec_ref(v_env_1245_);
lean_dec(v_declName_1236_);
goto v___jp_1242_;
}
else
{
lean_object* v_val_1261_; lean_object* v___x_1262_; lean_object* v_modules_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l_Lean_Environment_header(v_env_1245_);
v_modules_1263_ = lean_ctor_get(v___x_1262_, 3);
lean_inc_ref(v_modules_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = lean_array_get_size(v_modules_1263_);
v___x_1265_ = lean_nat_dec_lt(v_val_1261_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v_modules_1263_);
lean_dec(v_val_1261_);
lean_dec_ref(v_env_1245_);
lean_dec(v_declName_1236_);
goto v___jp_1242_;
}
else
{
lean_object* v___x_1266_; lean_object* v_env_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___y_1271_; 
v___x_1266_ = lean_st_ref_get(v___y_1239_);
v_env_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc_ref(v_env_1267_);
lean_dec(v___x_1266_);
v___x_1268_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__2);
v___x_1269_ = lean_array_fget(v_modules_1263_, v_val_1261_);
lean_dec(v_val_1261_);
lean_dec_ref(v_modules_1263_);
if (v_isMeta_1237_ == 0)
{
lean_dec_ref(v_env_1267_);
v___y_1271_ = v_isMeta_1237_;
goto v___jp_1270_;
}
else
{
uint8_t v___x_1282_; 
lean_inc(v_declName_1236_);
v___x_1282_ = l_Lean_isMarkedMeta(v_env_1267_, v_declName_1236_);
if (v___x_1282_ == 0)
{
v___y_1271_ = v_isMeta_1237_;
goto v___jp_1270_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = 0;
v___y_1271_ = v___x_1283_;
goto v___jp_1270_;
}
}
v___jp_1270_:
{
lean_object* v_toImport_1272_; lean_object* v_module_1273_; lean_object* v___x_1274_; 
v_toImport_1272_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_toImport_1272_);
lean_dec(v___x_1269_);
v_module_1273_ = lean_ctor_get(v_toImport_1272_, 0);
lean_inc(v_module_1273_);
lean_dec_ref(v_toImport_1272_);
lean_inc(v_declName_1236_);
v___x_1274_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1273_, v___y_1271_, v_declName_1236_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1274_, 1);
v___x_1275_ = l_Lean_indirectModUseExt;
v___x_1276_ = lean_box(1);
v___x_1277_ = lean_box(0);
lean_inc_ref(v_env_1245_);
v___x_1278_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1268_, v___x_1275_, v_env_1245_, v___x_1276_, v___x_1277_);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v___x_1278_, v_declName_1236_);
lean_dec(v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__3));
v___y_1247_ = v___x_1280_;
goto v___jp_1246_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1279_, 1);
v___y_1247_ = v_val_1281_;
goto v___jp_1246_;
}
}
else
{
lean_dec_ref(v_env_1245_);
lean_dec(v_declName_1236_);
return v___x_1274_;
}
}
}
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; size_t v_sz_1249_; size_t v___x_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_box(0);
v_sz_1249_ = lean_array_size(v___y_1247_);
v___x_1250_ = ((size_t)0ULL);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v_env_1245_, v_declName_1236_, v___y_1247_, v_sz_1249_, v___x_1250_, v___x_1248_, v___y_1238_, v___y_1239_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_env_1245_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1259_);
v___x_1253_ = v___x_1251_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1251_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1248_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1248_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1284_, lean_object* v_isMeta_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_isMeta_boxed_1289_; lean_object* v_res_1290_; 
v_isMeta_boxed_1289_ = lean_unbox(v_isMeta_1285_);
v_res_1290_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_declName_1284_, v_isMeta_boxed_1289_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1290_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, uint8_t v_builtin_1308_, lean_object* v___x_1309_, lean_object* v_name_1310_, lean_object* v_declName_1311_, lean_object* v_stx_1312_, uint8_t v_kind_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = 0;
v___x_1461_ = l_Lean_instBEqAttributeKind_beq(v_kind_1313_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
lean_dec(v_stx_1312_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v___x_1462_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1310_, v_kind_1313_, v___y_1314_, v___y_1315_);
return v___x_1462_;
}
else
{
goto v___jp_1458_;
}
v___jp_1317_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1324_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1323_);
v___x_1325_ = l_Lean_mkConst(v___x_1324_, v___y_1319_);
v___x_1326_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___y_1321_);
v___x_1327_ = l_Lean_mkAppB(v___x_1325_, v___x_1326_, v___y_1322_);
v___x_1328_ = l_Lean_declareBuiltin(v_declName_1311_, v___x_1327_, v___y_1320_, v___y_1318_);
return v___x_1328_;
}
v___jp_1329_:
{
if (v_builtin_1308_ == 0)
{
lean_object* v___x_1335_; lean_object* v_env_1336_; lean_object* v_options_1337_; lean_object* v_ref_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref(v___y_1331_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v___x_1335_ = lean_st_ref_get(v___y_1334_);
v_env_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_ref(v_env_1336_);
lean_dec(v___x_1335_);
v_options_1337_ = lean_ctor_get(v___y_1333_, 2);
v_ref_1338_ = lean_ctor_get(v___y_1333_, 5);
lean_inc_ref(v_options_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_env_1336_);
lean_ctor_set(v___x_1339_, 1, v_options_1337_);
lean_inc(v_declName_1311_);
v___x_1340_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_declName_1311_, v___x_1339_);
lean_dec_ref_known(v___x_1339_, 2);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v_toEnvExtension_1343_; lean_object* v_asyncMode_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_1343_ = lean_ctor_get(v___x_1342_, 0);
v_asyncMode_1344_ = lean_ctor_get(v_toEnvExtension_1343_, 2);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___y_1332_);
lean_ctor_set(v___x_1345_, 1, v_a_1341_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_declName_1311_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1342_, v___y_1330_, v___x_1346_, v_asyncMode_1344_, v___x_1309_);
v___x_1348_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v___x_1347_, v___y_1334_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1330_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1351_ = v___x_1340_;
v_isShared_1352_ = v_isSharedCheck_1360_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1360_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1353_ = lean_io_error_to_string(v_a_1349_);
v___x_1354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
v___x_1355_ = l_Lean_MessageData_ofFormat(v___x_1354_);
lean_inc(v_ref_1338_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_ref_1338_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1356_);
v___x_1358_ = v___x_1351_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
lean_dec_ref(v___y_1330_);
lean_dec(v___x_1309_);
v___x_1361_ = l_Lean_ConstantInfo_type(v___y_1331_);
lean_dec_ref(v___y_1331_);
v___x_1362_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1307_);
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
v___x_1363_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1362_);
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Lean_Expr_const___override(v___x_1363_, v___x_1364_);
v___x_1366_ = lean_expr_eqv(v___x_1361_, v___x_1365_);
lean_dec_ref(v___x_1365_);
lean_dec_ref(v___x_1361_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_inc(v_declName_1311_);
v___x_1367_ = l_Lean_mkConst(v_declName_1311_, v___x_1364_);
v___y_1318_ = v___y_1334_;
v___y_1319_ = v___x_1364_;
v___y_1320_ = v___y_1333_;
v___y_1321_ = v___y_1332_;
v___y_1322_ = v___x_1367_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___x_1307_);
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
v___x_1369_ = l_Lean_Name_mkStr5(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1362_, v___x_1368_);
v___x_1370_ = l_Lean_mkConst(v___x_1369_, v___x_1364_);
lean_inc(v_declName_1311_);
v___x_1371_ = l_Lean_mkConst(v_declName_1311_, v___x_1364_);
v___x_1372_ = l_Lean_Expr_app___override(v___x_1370_, v___x_1371_);
v___y_1318_ = v___y_1334_;
v___y_1319_ = v___x_1364_;
v___y_1320_ = v___y_1333_;
v___y_1321_ = v___y_1332_;
v___y_1322_ = v___x_1372_;
goto v___jp_1317_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1374_);
v___x_1380_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1381_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1307_);
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
v___x_1382_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1381_);
v___x_1383_ = l_Lean_MessageData_ofConstName(v___x_1382_, v___y_1375_);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1380_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
v___x_1388_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1387_);
v___x_1389_ = l_Lean_MessageData_ofConstName(v___x_1388_, v___y_1375_);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1386_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = l_Lean_MessageData_ofName(v_declName_1311_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_ConstantInfo_type(v___y_1377_);
lean_dec_ref(v___y_1377_);
v___x_1398_ = l_Lean_indentExpr(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1396_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_1399_, v___y_1376_, v___y_1378_);
return v___x_1400_;
}
v___jp_1401_:
{
lean_object* v___x_1405_; 
lean_inc(v_declName_1311_);
v___x_1405_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_declName_1311_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1312_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = lean_box(0);
v___x_1410_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_1408_, v___x_1409_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_n(v_a_1411_, 2);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = 0;
v___x_1413_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_a_1411_, v___x_1412_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
lean_dec_ref_known(v___x_1413_, 1);
v___x_1414_ = l_Lean_ConstantInfo_levelParams(v_a_1406_);
v___x_1415_ = l_List_isEmpty___redArg(v___x_1414_);
lean_dec(v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec(v___x_1309_);
v___y_1374_ = v___y_1402_;
v___y_1375_ = v___x_1412_;
v___y_1376_ = v___y_1403_;
v___y_1377_ = v_a_1406_;
v___y_1378_ = v___y_1404_;
v___y_1379_ = v_a_1411_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1416_ = l_Lean_ConstantInfo_type(v_a_1406_);
v___x_1417_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1307_);
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
v___x_1418_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1417_);
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_Expr_const___override(v___x_1418_, v___x_1419_);
v___x_1421_ = lean_expr_eqv(v___x_1416_, v___x_1420_);
lean_dec_ref(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1422_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1307_);
lean_inc_ref(v___x_1306_);
lean_inc_ref(v___x_1305_);
v___x_1423_ = l_Lean_Name_mkStr4(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1422_);
v___x_1424_ = l_Lean_Expr_const___override(v___x_1423_, v___x_1419_);
v___x_1425_ = lean_expr_eqv(v___x_1416_, v___x_1424_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1416_);
if (v___x_1425_ == 0)
{
lean_dec(v___x_1309_);
v___y_1374_ = v___y_1402_;
v___y_1375_ = v___x_1412_;
v___y_1376_ = v___y_1403_;
v___y_1377_ = v_a_1406_;
v___y_1378_ = v___y_1404_;
v___y_1379_ = v_a_1411_;
goto v___jp_1373_;
}
else
{
v___y_1330_ = v___y_1402_;
v___y_1331_ = v_a_1406_;
v___y_1332_ = v_a_1411_;
v___y_1333_ = v___y_1403_;
v___y_1334_ = v___y_1404_;
goto v___jp_1329_;
}
}
else
{
lean_dec_ref(v___x_1416_);
v___y_1330_ = v___y_1402_;
v___y_1331_ = v_a_1406_;
v___y_1332_ = v_a_1411_;
v___y_1333_ = v___y_1403_;
v___y_1334_ = v___y_1404_;
goto v___jp_1329_;
}
}
}
else
{
lean_dec(v_a_1411_);
lean_dec(v_a_1406_);
lean_dec_ref(v___y_1402_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
return v___x_1413_;
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1406_);
lean_dec_ref(v___y_1402_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v_a_1426_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1410_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1410_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1406_);
lean_dec_ref(v___y_1402_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v_a_1434_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1407_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1407_);
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
lean_dec_ref(v___y_1402_);
lean_dec(v_stx_1312_);
lean_dec(v_declName_1311_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v_a_1442_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1405_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1405_);
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
v___jp_1450_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_st_ref_get(v___y_1452_);
if (v_builtin_1308_ == 0)
{
lean_object* v_env_1454_; lean_object* v___x_1455_; 
v_env_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc_ref(v_env_1454_);
lean_dec(v___x_1453_);
v___x_1455_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1454_, v_declName_1311_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_dec(v_name_1310_);
v___y_1402_ = v_env_1454_;
v___y_1403_ = v___y_1451_;
v___y_1404_ = v___y_1452_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1456_; 
lean_dec_ref_known(v___x_1455_, 1);
lean_dec_ref(v_env_1454_);
lean_dec(v_stx_1312_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
v___x_1456_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_name_1310_, v_declName_1311_, v___y_1451_, v___y_1452_);
return v___x_1456_;
}
}
else
{
lean_object* v_env_1457_; 
lean_dec(v_name_1310_);
v_env_1457_ = lean_ctor_get(v___x_1453_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1453_);
v___y_1402_ = v_env_1457_;
v___y_1403_ = v___y_1451_;
v___y_1404_ = v___y_1452_;
goto v___jp_1401_;
}
}
v___jp_1458_:
{
if (v_builtin_1308_ == 0)
{
lean_object* v___x_1459_; 
lean_inc(v_declName_1311_);
lean_inc(v_name_1310_);
v___x_1459_ = l_Lean_ensureAttrDeclIsMeta(v_name_1310_, v_declName_1311_, v_kind_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref_known(v___x_1459_, 1);
v___y_1451_ = v___y_1314_;
v___y_1452_ = v___y_1315_;
goto v___jp_1450_;
}
else
{
lean_dec(v_stx_1312_);
lean_dec(v_declName_1311_);
lean_dec(v_name_1310_);
lean_dec(v___x_1309_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1305_);
return v___x_1459_;
}
}
else
{
v___y_1451_ = v___y_1314_;
v___y_1452_ = v___y_1315_;
goto v___jp_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v___x_1465_, lean_object* v_builtin_1466_, lean_object* v___x_1467_, lean_object* v_name_1468_, lean_object* v_declName_1469_, lean_object* v_stx_1470_, lean_object* v_kind_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v_builtin_boxed_1475_; uint8_t v_kind_boxed_1476_; lean_object* v_res_1477_; 
v_builtin_boxed_1475_ = lean_unbox(v_builtin_1466_);
v_kind_boxed_1476_ = lean_unbox(v_kind_1471_);
v_res_1477_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1463_, v___x_1464_, v___x_1465_, v_builtin_boxed_1475_, v___x_1467_, v_name_1468_, v_declName_1469_, v_stx_1470_, v_kind_boxed_1476_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t v_builtin_1536_, lean_object* v_name_1537_){
_start:
{
lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; lean_object* v___y_1548_; 
lean_inc_n(v_name_1537_, 2);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1539_, 0, v_name_1537_);
v___x_1540_ = lean_box(0);
v___x_1541_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1542_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1543_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4));
v___x_1544_ = lean_box(v_builtin_1536_);
v___f_1545_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1545_, 0, v___x_1541_);
lean_closure_set(v___f_1545_, 1, v___x_1542_);
lean_closure_set(v___f_1545_, 2, v___x_1543_);
lean_closure_set(v___f_1545_, 3, v___x_1544_);
lean_closure_set(v___f_1545_, 4, v___x_1540_);
lean_closure_set(v___f_1545_, 5, v_name_1537_);
v___x_1546_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
if (v_builtin_1536_ == 0)
{
lean_object* v___x_1555_; 
v___x_1555_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___y_1548_ = v___x_1555_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___y_1548_ = v___x_1556_;
goto v___jp_1547_;
}
v___jp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___y_1548_);
v___x_1550_ = lean_string_append(v___y_1548_, v___x_1549_);
v___x_1551_ = 1;
v___x_1552_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1552_, 0, v___x_1546_);
lean_ctor_set(v___x_1552_, 1, v_name_1537_);
lean_ctor_set(v___x_1552_, 2, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*3, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v___f_1545_);
lean_ctor_set(v___x_1553_, 2, v___f_1539_);
v___x_1554_ = l_Lean_registerBuiltinAttribute(v___x_1553_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_builtin_1557_, lean_object* v_name_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_builtin_boxed_1560_; lean_object* v_res_1561_; 
v_builtin_boxed_1560_ = lean_unbox(v_builtin_1557_);
v_res_1561_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_builtin_boxed_1560_, v_name_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = 1;
v___x_1570_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1571_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1569_, v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1571_, 1);
v___x_1572_ = 0;
v___x_1573_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1574_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1572_, v___x_1573_);
return v___x_1574_;
}
else
{
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1577_, lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(v_00_u03b1_1583_, v_msg_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1589_, lean_object* v_attrName_1590_, lean_object* v_declName_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_1590_, v_declName_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_attrName_1597_, lean_object* v_declName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(v_00_u03b1_1596_, v_attrName_1597_, v_declName_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1603_, lean_object* v_name_1604_, uint8_t v_kind_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1604_, v_kind_1605_, v___y_1606_, v___y_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_name_1611_, lean_object* v_kind_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_kind_boxed_1616_; lean_object* v_res_1617_; 
v_kind_boxed_1616_ = lean_unbox(v_kind_1612_);
v_res_1617_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(v_00_u03b1_1610_, v_name_1611_, v_kind_boxed_1616_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_1618_, lean_object* v_constName_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_1619_, v___y_1620_, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_constName_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_1624_, v_constName_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(lean_object* v_00_u03b2_1630_, lean_object* v_m_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1631_, v_a_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_m_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(v_00_u03b2_1634_, v_m_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_m_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1638_, lean_object* v_ref_1639_, lean_object* v_constName_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_1639_, v_constName_1640_, v___y_1641_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_ref_1646_, lean_object* v_constName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b1_1645_, v_ref_1646_, v_constName_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v_ref_1646_);
return v_res_1651_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(v_00_u03b2_1656_, v_x_1657_, v_x_1658_);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_x_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(lean_object* v_00_u03b2_1661_, lean_object* v_a_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_a_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(v_00_u03b2_1665_, v_a_1666_, v_x_1667_);
lean_dec(v_x_1667_);
lean_dec(v_a_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1669_, lean_object* v_ref_1670_, lean_object* v_msg_1671_, lean_object* v_declHint_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_1670_, v_msg_1671_, v_declHint_1672_, v___y_1673_, v___y_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1677_, lean_object* v_ref_1678_, lean_object* v_msg_1679_, lean_object* v_declHint_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_00_u03b1_1677_, v_ref_1678_, v_msg_1679_, v_declHint_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_ref_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, size_t v_x_1687_, lean_object* v_x_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_1686_, v_x_1687_, v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
size_t v_x_10100__boxed_1694_; uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_x_10100__boxed_1694_ = lean_unbox_usize(v_x_1692_);
lean_dec(v_x_1692_);
v_res_1695_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(v_00_u03b2_1690_, v_x_1691_, v_x_10100__boxed_1694_, v_x_1693_);
lean_dec_ref(v_x_1693_);
lean_dec_ref(v_x_1691_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(lean_object* v_msg_1697_, lean_object* v_declHint_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_1697_, v_declHint_1698_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___boxed(lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(v_msg_1703_, v_declHint_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b1_1709_, lean_object* v_ref_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_1710_, v_msg_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_ref_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(v_00_u03b1_1716_, v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_ref_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(lean_object* v_00_u03b2_1723_, lean_object* v_keys_1724_, lean_object* v_vals_1725_, lean_object* v_heq_1726_, lean_object* v_i_1727_, lean_object* v_k_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_1724_, v_i_1727_, v_k_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1730_, lean_object* v_keys_1731_, lean_object* v_vals_1732_, lean_object* v_heq_1733_, lean_object* v_i_1734_, lean_object* v_k_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(v_00_u03b2_1730_, v_keys_1731_, v_vals_1732_, v_heq_1733_, v_i_1734_, v_k_1735_);
lean_dec_ref(v_k_1735_);
lean_dec_ref(v_vals_1732_);
lean_dec_ref(v_keys_1731_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1738_, lean_object* v_opt_1739_){
_start:
{
lean_object* v_name_1740_; lean_object* v_defValue_1741_; lean_object* v_map_1742_; lean_object* v___x_1743_; 
v_name_1740_ = lean_ctor_get(v_opt_1739_, 0);
v_defValue_1741_ = lean_ctor_get(v_opt_1739_, 1);
v_map_1742_ = lean_ctor_get(v_opts_1738_, 0);
v___x_1743_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1742_, v_name_1740_);
if (lean_obj_tag(v___x_1743_) == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_unbox(v_defValue_1741_);
return v___x_1744_;
}
else
{
lean_object* v_val_1745_; 
v_val_1745_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1743_, 1);
if (lean_obj_tag(v_val_1745_) == 1)
{
uint8_t v_v_1746_; 
v_v_1746_ = lean_ctor_get_uint8(v_val_1745_, 0);
lean_dec_ref_known(v_val_1745_, 0);
return v_v_1746_;
}
else
{
uint8_t v___x_1747_; 
lean_dec(v_val_1745_);
v___x_1747_ = lean_unbox(v_defValue_1741_);
return v___x_1747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1748_, lean_object* v_opt_1749_){
_start:
{
uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_res_1750_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1748_, v_opt_1749_);
lean_dec_ref(v_opt_1749_);
lean_dec_ref(v_opts_1748_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1752_, uint8_t v___y_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1754_) == 1)
{
lean_object* v_pre_1755_; 
v_pre_1755_ = lean_ctor_get(v_x_1754_, 0);
if (lean_obj_tag(v_pre_1755_) == 0)
{
lean_object* v_str_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_str_1756_ = lean_ctor_get(v_x_1754_, 1);
v___x_1757_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10));
v___x_1758_ = lean_string_dec_eq(v_str_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
return v___x_1758_;
}
else
{
return v_suppressElabErrors_1752_;
}
}
else
{
return v___y_1753_;
}
}
else
{
return v___y_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1759_, lean_object* v___y_1760_, lean_object* v_x_1761_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1762_; uint8_t v___y_2271__boxed_1763_; uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_suppressElabErrors_boxed_1762_ = lean_unbox(v_suppressElabErrors_1759_);
v___y_2271__boxed_1763_ = lean_unbox(v___y_1760_);
v_res_1764_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1762_, v___y_2271__boxed_1763_, v_x_1761_);
lean_dec(v_x_1761_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_env_1770_; lean_object* v___x_1771_; lean_object* v_scopes_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_opts_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1769_ = lean_st_ref_get(v___y_1767_);
v_env_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1769_);
v___x_1771_ = lean_st_ref_get(v___y_1767_);
v_scopes_1772_ = lean_ctor_get(v___x_1771_, 2);
lean_inc(v_scopes_1772_);
lean_dec(v___x_1771_);
v___x_1773_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1774_ = l_List_head_x21___redArg(v___x_1773_, v_scopes_1772_);
lean_dec(v_scopes_1772_);
v_opts_1775_ = lean_ctor_get(v___x_1774_, 1);
lean_inc_ref(v_opts_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1777_ = lean_unsigned_to_nat(32u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
lean_dec_ref(v___x_1778_);
v___x_1779_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_1780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1780_, 0, v_env_1770_);
lean_ctor_set(v___x_1780_, 1, v___x_1776_);
lean_ctor_set(v___x_1780_, 2, v___x_1779_);
lean_ctor_set(v___x_1780_, 3, v_opts_1775_);
v___x_1781_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_msgData_1766_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_1783_, v___y_1784_);
lean_dec(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(lean_object* v_ref_1787_, lean_object* v_msgData_1788_, uint8_t v_severity_1789_, uint8_t v_isSilent_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; uint8_t v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; uint8_t v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; uint8_t v___y_1896_; uint8_t v___y_1897_; uint8_t v___y_1898_; uint8_t v___x_1913_; uint8_t v___y_1915_; uint8_t v___y_1916_; uint8_t v___y_1917_; uint8_t v___y_1919_; uint8_t v___x_1931_; 
v___x_1913_ = 2;
v___x_1931_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1789_, v___x_1913_);
if (v___x_1931_ == 0)
{
v___y_1919_ = v___x_1931_;
goto v___jp_1918_;
}
else
{
uint8_t v___x_1932_; 
lean_inc_ref(v_msgData_1788_);
v___x_1932_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1788_);
v___y_1919_ = v___x_1932_;
goto v___jp_1918_;
}
v___jp_1794_:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Elab_Command_getScope___redArg(v___y_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l_Lean_Elab_Command_getScope___redArg(v___y_1802_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1842_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1842_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1842_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v_currNamespace_1811_; lean_object* v_openDecls_1812_; lean_object* v_env_1813_; lean_object* v_messages_1814_; lean_object* v_scopes_1815_; lean_object* v_usedQuotCtxts_1816_; lean_object* v_nextMacroScope_1817_; lean_object* v_maxRecDepth_1818_; lean_object* v_ngen_1819_; lean_object* v_auxDeclNGen_1820_; lean_object* v_infoState_1821_; lean_object* v_traceState_1822_; lean_object* v_snapshotTasks_1823_; lean_object* v_prevLinterStates_1824_; lean_object* v_codeQualityEntryTasks_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1841_; 
v___x_1810_ = lean_st_ref_take(v___y_1802_);
v_currNamespace_1811_ = lean_ctor_get(v_a_1804_, 2);
lean_inc(v_currNamespace_1811_);
lean_dec(v_a_1804_);
v_openDecls_1812_ = lean_ctor_get(v_a_1806_, 3);
lean_inc(v_openDecls_1812_);
lean_dec(v_a_1806_);
v_env_1813_ = lean_ctor_get(v___x_1810_, 0);
v_messages_1814_ = lean_ctor_get(v___x_1810_, 1);
v_scopes_1815_ = lean_ctor_get(v___x_1810_, 2);
v_usedQuotCtxts_1816_ = lean_ctor_get(v___x_1810_, 3);
v_nextMacroScope_1817_ = lean_ctor_get(v___x_1810_, 4);
v_maxRecDepth_1818_ = lean_ctor_get(v___x_1810_, 5);
v_ngen_1819_ = lean_ctor_get(v___x_1810_, 6);
v_auxDeclNGen_1820_ = lean_ctor_get(v___x_1810_, 7);
v_infoState_1821_ = lean_ctor_get(v___x_1810_, 8);
v_traceState_1822_ = lean_ctor_get(v___x_1810_, 9);
v_snapshotTasks_1823_ = lean_ctor_get(v___x_1810_, 10);
v_prevLinterStates_1824_ = lean_ctor_get(v___x_1810_, 11);
v_codeQualityEntryTasks_1825_ = lean_ctor_get(v___x_1810_, 12);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1827_ = v___x_1810_;
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1825_);
lean_inc(v_prevLinterStates_1824_);
lean_inc(v_snapshotTasks_1823_);
lean_inc(v_traceState_1822_);
lean_inc(v_infoState_1821_);
lean_inc(v_auxDeclNGen_1820_);
lean_inc(v_ngen_1819_);
lean_inc(v_maxRecDepth_1818_);
lean_inc(v_nextMacroScope_1817_);
lean_inc(v_usedQuotCtxts_1816_);
lean_inc(v_scopes_1815_);
lean_inc(v_messages_1814_);
lean_inc(v_env_1813_);
lean_dec(v___x_1810_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_currNamespace_1811_);
lean_ctor_set(v___x_1829_, 1, v_openDecls_1812_);
v___x_1830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___y_1798_);
lean_inc_ref(v___y_1799_);
lean_inc_ref(v___y_1797_);
v___x_1831_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1831_, 0, v___y_1797_);
lean_ctor_set(v___x_1831_, 1, v___y_1795_);
lean_ctor_set(v___x_1831_, 2, v___y_1796_);
lean_ctor_set(v___x_1831_, 3, v___y_1799_);
lean_ctor_set(v___x_1831_, 4, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*5, v___y_1801_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*5 + 1, v___y_1800_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*5 + 2, v_isSilent_1790_);
v___x_1832_ = l_Lean_MessageLog_add(v___x_1831_, v_messages_1814_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1832_);
v___x_1834_ = v___x_1827_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_env_1813_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_scopes_1815_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_usedQuotCtxts_1816_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_nextMacroScope_1817_);
lean_ctor_set(v_reuseFailAlloc_1840_, 5, v_maxRecDepth_1818_);
lean_ctor_set(v_reuseFailAlloc_1840_, 6, v_ngen_1819_);
lean_ctor_set(v_reuseFailAlloc_1840_, 7, v_auxDeclNGen_1820_);
lean_ctor_set(v_reuseFailAlloc_1840_, 8, v_infoState_1821_);
lean_ctor_set(v_reuseFailAlloc_1840_, 9, v_traceState_1822_);
lean_ctor_set(v_reuseFailAlloc_1840_, 10, v_snapshotTasks_1823_);
lean_ctor_set(v_reuseFailAlloc_1840_, 11, v_prevLinterStates_1824_);
lean_ctor_set(v_reuseFailAlloc_1840_, 12, v_codeQualityEntryTasks_1825_);
v___x_1834_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = lean_st_ref_put(v___y_1802_, v___x_1834_);
v___x_1836_ = lean_box(0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1836_);
v___x_1838_ = v___x_1808_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1804_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
v_a_1843_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1805_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1805_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
v_a_1851_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1803_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1803_);
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
v___jp_1859_:
{
lean_object* v_fileName_1865_; lean_object* v_fileMap_1866_; uint8_t v_suppressElabErrors_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1886_; 
v_fileName_1865_ = lean_ctor_get(v___y_1791_, 0);
v_fileMap_1866_ = lean_ctor_get(v___y_1791_, 1);
v_suppressElabErrors_1867_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*10);
v___x_1868_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1788_);
v___x_1869_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1868_, v___y_1792_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1886_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1886_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_inc_ref_n(v_fileMap_1866_, 2);
v___x_1874_ = l_Lean_FileMap_toPosition(v_fileMap_1866_, v___y_1861_);
lean_dec(v___y_1861_);
v___x_1875_ = l_Lean_FileMap_toPosition(v_fileMap_1866_, v___y_1864_);
lean_dec(v___y_1864_);
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
v___x_1877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
if (v_suppressElabErrors_1867_ == 0)
{
lean_del_object(v___x_1872_);
v___y_1795_ = v___x_1874_;
v___y_1796_ = v___x_1876_;
v___y_1797_ = v_fileName_1865_;
v___y_1798_ = v_a_1870_;
v___y_1799_ = v___x_1877_;
v___y_1800_ = v___y_1862_;
v___y_1801_ = v___y_1863_;
v___y_1802_ = v___y_1792_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; uint8_t v___x_1881_; 
v___x_1878_ = lean_box(v_suppressElabErrors_1867_);
v___x_1879_ = lean_box(v___y_1860_);
v___f_1880_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1880_, 0, v___x_1878_);
lean_closure_set(v___f_1880_, 1, v___x_1879_);
lean_inc(v_a_1870_);
v___x_1881_ = l_Lean_MessageData_hasTag(v___f_1880_, v_a_1870_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1876_, 1);
lean_dec_ref(v___x_1874_);
lean_dec(v_a_1870_);
v___x_1882_ = lean_box(0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1882_);
v___x_1884_ = v___x_1872_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
else
{
lean_del_object(v___x_1872_);
v___y_1795_ = v___x_1874_;
v___y_1796_ = v___x_1876_;
v___y_1797_ = v_fileName_1865_;
v___y_1798_ = v_a_1870_;
v___y_1799_ = v___x_1877_;
v___y_1800_ = v___y_1862_;
v___y_1801_ = v___y_1863_;
v___y_1802_ = v___y_1792_;
goto v___jp_1794_;
}
}
}
}
v___jp_1887_:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Syntax_getTailPos_x3f(v___y_1889_, v___y_1891_);
lean_dec(v___y_1889_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_inc(v___y_1892_);
v___y_1860_ = v___y_1888_;
v___y_1861_ = v___y_1892_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1892_;
goto v___jp_1859_;
}
else
{
lean_object* v_val_1894_; 
v_val_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___y_1860_ = v___y_1888_;
v___y_1861_ = v___y_1892_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v_val_1894_;
goto v___jp_1859_;
}
}
v___jp_1895_:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Elab_Command_getRef___redArg(v___y_1791_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v_ref_1901_; lean_object* v___x_1902_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v_ref_1901_ = l_Lean_replaceRef(v_ref_1787_, v_a_1900_);
lean_dec(v_a_1900_);
v___x_1902_ = l_Lean_Syntax_getPos_x3f(v_ref_1901_, v___y_1897_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___y_1888_ = v___y_1896_;
v___y_1889_ = v_ref_1901_;
v___y_1890_ = v___y_1898_;
v___y_1891_ = v___y_1897_;
v___y_1892_ = v___x_1903_;
goto v___jp_1887_;
}
else
{
lean_object* v_val_1904_; 
v_val_1904_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1902_, 1);
v___y_1888_ = v___y_1896_;
v___y_1889_ = v_ref_1901_;
v___y_1890_ = v___y_1898_;
v___y_1891_ = v___y_1897_;
v___y_1892_ = v_val_1904_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_msgData_1788_);
v_a_1905_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1899_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1899_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
v___jp_1914_:
{
if (v___y_1917_ == 0)
{
v___y_1896_ = v___y_1915_;
v___y_1897_ = v___y_1916_;
v___y_1898_ = v_severity_1789_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v___y_1915_;
v___y_1897_ = v___y_1916_;
v___y_1898_ = v___x_1913_;
goto v___jp_1895_;
}
}
v___jp_1918_:
{
if (v___y_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v_scopes_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_opts_1924_; uint8_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1920_ = lean_st_ref_get(v___y_1792_);
v_scopes_1921_ = lean_ctor_get(v___x_1920_, 2);
lean_inc(v_scopes_1921_);
lean_dec(v___x_1920_);
v___x_1922_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1923_ = l_List_head_x21___redArg(v___x_1922_, v_scopes_1921_);
lean_dec(v_scopes_1921_);
v_opts_1924_ = lean_ctor_get(v___x_1923_, 1);
lean_inc_ref(v_opts_1924_);
lean_dec(v___x_1923_);
v___x_1925_ = 1;
v___x_1926_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1789_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_dec_ref(v_opts_1924_);
v___y_1915_ = v___y_1919_;
v___y_1916_ = v___y_1919_;
v___y_1917_ = v___x_1926_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = l_Lean_warningAsError;
v___x_1928_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1924_, v___x_1927_);
lean_dec_ref(v_opts_1924_);
v___y_1915_ = v___y_1919_;
v___y_1916_ = v___y_1919_;
v___y_1917_ = v___x_1928_;
goto v___jp_1914_;
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec_ref(v_msgData_1788_);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1933_, lean_object* v_msgData_1934_, lean_object* v_severity_1935_, lean_object* v_isSilent_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v_severity_boxed_1940_; uint8_t v_isSilent_boxed_1941_; lean_object* v_res_1942_; 
v_severity_boxed_1940_ = lean_unbox(v_severity_1935_);
v_isSilent_boxed_1941_ = lean_unbox(v_isSilent_1936_);
v_res_1942_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1933_, v_msgData_1934_, v_severity_boxed_1940_, v_isSilent_boxed_1941_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v_ref_1933_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object* v_ref_1943_, lean_object* v_msgData_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = 1;
v___x_1949_ = 0;
v___x_1950_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1943_, v_msgData_1944_, v___x_1948_, v___x_1949_, v___y_1945_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object* v_ref_1951_, lean_object* v_msgData_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_ref_1951_, v_msgData_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_ref_1951_);
return v_res_1956_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0));
v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2));
v___x_1962_ = l_Lean_stringToMessageData(v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(lean_object* v_linterOption_1963_, lean_object* v_stx_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_name_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1987_; 
v_name_1969_ = lean_ctor_get(v_linterOption_1963_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_linterOption_1963_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v_linterOption_1963_, 1);
lean_dec(v_unused_1988_);
v___x_1971_ = v_linterOption_1963_;
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_name_1969_);
lean_dec(v_linterOption_1963_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1973_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1);
lean_inc(v_name_1969_);
v___x_1974_ = l_Lean_MessageData_ofName(v_name_1969_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 7);
lean_ctor_set(v___x_1971_, 1, v___x_1974_);
lean_ctor_set(v___x_1971_, 0, v___x_1973_);
v___x_1976_ = v___x_1971_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v_disable_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1977_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v_disable_1979_ = l_Lean_MessageData_note(v___x_1978_);
v___x_1980_ = l_Lean_Linter_linterMessageTag;
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_msg_1965_);
lean_ctor_set(v___x_1981_, 1, v_disable_1979_);
v___x_1982_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_name_1969_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_inc(v_stx_1964_);
v___x_1984_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_stx_1964_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_stx_1964_, v___x_1984_, v___y_1966_, v___y_1967_);
lean_dec(v_stx_1964_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object* v_linterOption_1989_, lean_object* v_stx_1990_, lean_object* v_msg_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v_linterOption_1989_, v_stx_1990_, v_msg_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lint___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lint___closed__0));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object* v_stx_1999_, lean_object* v_msg_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2004_ = l_Lean_Linter_linter_missingDocs;
v___x_2005_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lint___closed__1, &l_Lean_Linter_MissingDocs_lint___closed__1_once, _init_l_Lean_Linter_MissingDocs_lint___closed__1);
v___x_2006_ = l_Lean_stringToMessageData(v_msg_2000_);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2004_, v_stx_1999_, v___x_2007_, v_a_2001_, v_a_2002_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object* v_stx_2009_, lean_object* v_msg_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Linter_MissingDocs_lint(v_stx_2009_, v_msg_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2015_, v___y_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(v_msgData_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2024_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintEmpty___closed__0));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty(lean_object* v_stx_2028_, lean_object* v_msg_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2033_ = l_Lean_Linter_linter_missingDocs;
v___x_2034_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lintEmpty___closed__1, &l_Lean_Linter_MissingDocs_lintEmpty___closed__1_once, _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1);
v___x_2035_ = l_Lean_stringToMessageData(v_msg_2029_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2033_, v_stx_2028_, v___x_2036_, v_a_2030_, v_a_2031_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty___boxed(lean_object* v_stx_2038_, lean_object* v_msg_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2038_, v_msg_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object* v_stx_2044_, lean_object* v_msg_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2050_ = lean_string_append(v_msg_2045_, v___x_2049_);
v___x_2051_ = l_Lean_Syntax_getId(v_stx_2044_);
v___x_2052_ = 1;
v___x_2053_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_string_append(v___x_2050_, v___x_2053_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = l_Lean_Linter_MissingDocs_lint(v_stx_2044_, v___x_2054_, v_a_2046_, v_a_2047_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object* v_stx_2056_, lean_object* v_msg_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2056_, v_msg_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed(lean_object* v_stx_2062_, lean_object* v_msg_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2068_ = lean_string_append(v_msg_2063_, v___x_2067_);
v___x_2069_ = l_Lean_Syntax_getId(v_stx_2062_);
v___x_2070_ = 1;
v___x_2071_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_string_append(v___x_2068_, v___x_2071_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2062_, v___x_2072_, v_a_2064_, v_a_2065_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed___boxed(lean_object* v_stx_2074_, lean_object* v_msg_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2074_, v_msg_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object* v_parent_2081_, lean_object* v_stx_2082_, lean_object* v_msg_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2088_ = lean_string_append(v_msg_2083_, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_getId(v_parent_2081_);
v___x_2090_ = 1;
v___x_2091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_string_append(v___x_2088_, v___x_2091_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_getId(v_stx_2082_);
v___x_2096_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2095_, v___x_2090_);
v___x_2097_ = lean_string_append(v___x_2094_, v___x_2096_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = l_Lean_Linter_MissingDocs_lint(v_stx_2082_, v___x_2097_, v_a_2084_, v_a_2085_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object* v_parent_2099_, lean_object* v_stx_2100_, lean_object* v_msg_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2099_, v_stx_2100_, v_msg_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_parent_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField(lean_object* v_parent_2106_, lean_object* v_stx_2107_, lean_object* v_msg_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2113_ = lean_string_append(v_msg_2108_, v___x_2112_);
v___x_2114_ = l_Lean_Syntax_getId(v_parent_2106_);
v___x_2115_ = 1;
v___x_2116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2114_, v___x_2115_);
v___x_2117_ = lean_string_append(v___x_2113_, v___x_2116_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
v___x_2120_ = l_Lean_Syntax_getId(v_stx_2107_);
v___x_2121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2120_, v___x_2115_);
v___x_2122_ = lean_string_append(v___x_2119_, v___x_2121_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2107_, v___x_2122_, v_a_2109_, v_a_2110_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField___boxed(lean_object* v_parent_2124_, lean_object* v_stx_2125_, lean_object* v_msg_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2124_, v_stx_2125_, v_msg_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_parent_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object* v_parent_2131_, lean_object* v_stx_2132_, lean_object* v_msg_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___x_2138_ = lean_string_append(v_msg_2133_, v___x_2137_);
v___x_2139_ = l_Lean_Syntax_getId(v_parent_2131_);
v___x_2140_ = 1;
v___x_2141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2138_, v___x_2141_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2144_ = lean_string_append(v___x_2142_, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_getId(v_stx_2132_);
v___x_2146_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2145_, v___x_2140_);
v___x_2147_ = lean_string_append(v___x_2144_, v___x_2146_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = l_Lean_Linter_MissingDocs_lint(v_stx_2132_, v___x_2147_, v_a_2134_, v_a_2135_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object* v_parent_2149_, lean_object* v_stx_2150_, lean_object* v_msg_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Linter_MissingDocs_lintStructField(v_parent_2149_, v_stx_2150_, v_msg_2151_, v_a_2152_, v_a_2153_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_parent_2149_);
return v_res_2155_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_box(1);
v___x_2157_ = l_Lean_MessageData_ofFormat(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2));
v___x_2162_ = l_Lean_MessageData_ofFormat(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
if (lean_obj_tag(v_x_2164_) == 0)
{
return v_x_2163_;
}
else
{
lean_object* v_head_2165_; lean_object* v_tail_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2188_; 
v_head_2165_ = lean_ctor_get(v_x_2164_, 0);
v_tail_2166_ = lean_ctor_get(v_x_2164_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2164_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2168_ = v_x_2164_;
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_tail_2166_);
lean_inc(v_head_2165_);
lean_dec(v_x_2164_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_before_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2186_; 
v_before_2170_ = lean_ctor_get(v_head_2165_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_head_2165_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v_head_2165_, 1);
lean_dec(v_unused_2187_);
v___x_2172_ = v_head_2165_;
v_isShared_2173_ = v_isSharedCheck_2186_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_before_2170_);
lean_dec(v_head_2165_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2186_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 7);
lean_ctor_set(v___x_2172_, 1, v___x_2174_);
lean_ctor_set(v___x_2172_, 0, v_x_2163_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_x_2163_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 7);
lean_ctor_set(v___x_2168_, 1, v___x_2177_);
lean_ctor_set(v___x_2168_, 0, v___x_2176_);
v___x_2179_ = v___x_2168_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = l_Lean_MessageData_ofSyntax(v_before_2170_);
v___x_2181_ = l_Lean_indentD(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2179_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v_x_2163_ = v___x_2182_;
v_x_2164_ = v_tail_2166_;
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
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_2193_ = l_Lean_MessageData_ofFormat(v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_2194_, lean_object* v_macroStack_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v_scopes_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_opts_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2198_ = lean_st_ref_get(v___y_2196_);
v_scopes_2199_ = lean_ctor_get(v___x_2198_, 2);
lean_inc(v_scopes_2199_);
lean_dec(v___x_2198_);
v___x_2200_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2201_ = l_List_head_x21___redArg(v___x_2200_, v_scopes_2199_);
lean_dec(v_scopes_2199_);
v_opts_2202_ = lean_ctor_get(v___x_2201_, 1);
lean_inc_ref(v_opts_2202_);
lean_dec(v___x_2201_);
v___x_2203_ = l_Lean_Elab_pp_macroStack;
v___x_2204_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_2202_, v___x_2203_);
lean_dec_ref(v_opts_2202_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_dec(v_macroStack_2195_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_msgData_2194_);
return v___x_2205_;
}
else
{
if (lean_obj_tag(v_macroStack_2195_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_msgData_2194_);
return v___x_2206_;
}
else
{
lean_object* v_head_2207_; lean_object* v_after_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2223_; 
v_head_2207_ = lean_ctor_get(v_macroStack_2195_, 0);
lean_inc(v_head_2207_);
v_after_2208_ = lean_ctor_get(v_head_2207_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_head_2207_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v_head_2207_, 0);
lean_dec(v_unused_2224_);
v___x_2210_ = v_head_2207_;
v_isShared_2211_ = v_isSharedCheck_2223_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_after_2208_);
lean_dec(v_head_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2223_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 7);
lean_ctor_set(v___x_2210_, 1, v___x_2212_);
lean_ctor_set(v___x_2210_, 0, v_msgData_2194_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_msgData_2194_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_msgData_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2215_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_MessageData_ofSyntax(v_after_2208_);
v___x_2218_ = l_Lean_indentD(v___x_2217_);
v_msgData_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2219_, 0, v___x_2216_);
lean_ctor_set(v_msgData_2219_, 1, v___x_2218_);
v___x_2220_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(v_msgData_2219_, v_macroStack_2195_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2225_, lean_object* v_macroStack_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2225_, v_macroStack_2226_, v___y_2227_);
lean_dec(v___y_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Elab_Command_getRef___redArg(v___y_2231_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_macroStack_2236_; lean_object* v___x_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_macroStack_2236_ = lean_ctor_get(v___y_2231_, 4);
v___x_2237_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_2230_, v___y_2232_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = l_Lean_Elab_getBetterRef(v_a_2235_, v_macroStack_2236_);
lean_dec(v_a_2235_);
lean_inc(v_macroStack_2236_);
v___x_2240_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2238_, v_macroStack_2236_, v___y_2232_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2239_);
lean_ctor_set(v___x_2245_, 1, v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 1);
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_msg_2230_);
v_a_2250_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2234_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2234_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(lean_object* v_ref_2263_, lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Elab_Command_getRef___redArg(v___y_2265_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v_fileName_2270_; lean_object* v_fileMap_2271_; lean_object* v_currRecDepth_2272_; lean_object* v_cmdPos_2273_; lean_object* v_macroStack_2274_; lean_object* v_quotContext_x3f_2275_; lean_object* v_currMacroScope_2276_; lean_object* v_snap_x3f_2277_; lean_object* v_cancelTk_x3f_2278_; uint8_t v_suppressElabErrors_2279_; lean_object* v_ref_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v_fileName_2270_ = lean_ctor_get(v___y_2265_, 0);
v_fileMap_2271_ = lean_ctor_get(v___y_2265_, 1);
v_currRecDepth_2272_ = lean_ctor_get(v___y_2265_, 2);
v_cmdPos_2273_ = lean_ctor_get(v___y_2265_, 3);
v_macroStack_2274_ = lean_ctor_get(v___y_2265_, 4);
v_quotContext_x3f_2275_ = lean_ctor_get(v___y_2265_, 5);
v_currMacroScope_2276_ = lean_ctor_get(v___y_2265_, 6);
v_snap_x3f_2277_ = lean_ctor_get(v___y_2265_, 8);
v_cancelTk_x3f_2278_ = lean_ctor_get(v___y_2265_, 9);
v_suppressElabErrors_2279_ = lean_ctor_get_uint8(v___y_2265_, sizeof(void*)*10);
v_ref_2280_ = l_Lean_replaceRef(v_ref_2263_, v_a_2269_);
lean_dec(v_a_2269_);
lean_inc(v_cancelTk_x3f_2278_);
lean_inc(v_snap_x3f_2277_);
lean_inc(v_currMacroScope_2276_);
lean_inc(v_quotContext_x3f_2275_);
lean_inc(v_macroStack_2274_);
lean_inc(v_cmdPos_2273_);
lean_inc(v_currRecDepth_2272_);
lean_inc_ref(v_fileMap_2271_);
lean_inc_ref(v_fileName_2270_);
v___x_2281_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2281_, 0, v_fileName_2270_);
lean_ctor_set(v___x_2281_, 1, v_fileMap_2271_);
lean_ctor_set(v___x_2281_, 2, v_currRecDepth_2272_);
lean_ctor_set(v___x_2281_, 3, v_cmdPos_2273_);
lean_ctor_set(v___x_2281_, 4, v_macroStack_2274_);
lean_ctor_set(v___x_2281_, 5, v_quotContext_x3f_2275_);
lean_ctor_set(v___x_2281_, 6, v_currMacroScope_2276_);
lean_ctor_set(v___x_2281_, 7, v_ref_2280_);
lean_ctor_set(v___x_2281_, 8, v_snap_x3f_2277_);
lean_ctor_set(v___x_2281_, 9, v_cancelTk_x3f_2278_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*10, v_suppressElabErrors_2279_);
v___x_2282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2264_, v___x_2281_, v___y_2266_);
lean_dec_ref_known(v___x_2281_, 10);
return v___x_2282_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_msg_2264_);
v_a_2283_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2268_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2268_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ref_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2291_, v_msg_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v_ref_2291_);
return v_res_2296_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object* v_stx_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_val_2314_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = l_Lean_Syntax_getArg(v_stx_2303_, v___x_2321_);
switch(lean_obj_tag(v___x_2322_))
{
case 2:
{
lean_object* v_val_2323_; 
lean_dec(v_stx_2303_);
v_val_2323_ = lean_ctor_get(v___x_2322_, 1);
lean_inc_ref(v_val_2323_);
lean_dec_ref_known(v___x_2322_, 2);
v_val_2314_ = v_val_2323_;
goto v___jp_2313_;
}
case 1:
{
lean_object* v_kind_2324_; 
v_kind_2324_ = lean_ctor_get(v___x_2322_, 1);
lean_inc(v_kind_2324_);
if (lean_obj_tag(v_kind_2324_) == 1)
{
lean_object* v_pre_2325_; 
v_pre_2325_ = lean_ctor_get(v_kind_2324_, 0);
lean_inc(v_pre_2325_);
if (lean_obj_tag(v_pre_2325_) == 1)
{
lean_object* v_pre_2326_; 
v_pre_2326_ = lean_ctor_get(v_pre_2325_, 0);
lean_inc(v_pre_2326_);
if (lean_obj_tag(v_pre_2326_) == 1)
{
lean_object* v_pre_2327_; 
v_pre_2327_ = lean_ctor_get(v_pre_2326_, 0);
lean_inc(v_pre_2327_);
if (lean_obj_tag(v_pre_2327_) == 1)
{
lean_object* v_pre_2328_; 
v_pre_2328_ = lean_ctor_get(v_pre_2327_, 0);
if (lean_obj_tag(v_pre_2328_) == 0)
{
lean_object* v_str_2329_; lean_object* v_str_2330_; lean_object* v_str_2331_; lean_object* v_str_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_str_2329_ = lean_ctor_get(v_kind_2324_, 1);
lean_inc_ref(v_str_2329_);
lean_dec_ref_known(v_kind_2324_, 2);
v_str_2330_ = lean_ctor_get(v_pre_2325_, 1);
lean_inc_ref(v_str_2330_);
lean_dec_ref_known(v_pre_2325_, 2);
v_str_2331_ = lean_ctor_get(v_pre_2326_, 1);
lean_inc_ref(v_str_2331_);
lean_dec_ref_known(v_pre_2326_, 2);
v_str_2332_ = lean_ctor_get(v_pre_2327_, 1);
lean_inc_ref(v_str_2332_);
lean_dec_ref_known(v_pre_2327_, 2);
v___x_2333_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2334_ = lean_string_dec_eq(v_str_2332_, v___x_2333_);
lean_dec_ref(v_str_2332_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v_str_2331_);
lean_dec_ref(v_str_2330_);
lean_dec_ref(v_str_2329_);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
else
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2336_ = lean_string_dec_eq(v_str_2331_, v___x_2335_);
lean_dec_ref(v_str_2331_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v_str_2330_);
lean_dec_ref(v_str_2329_);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
else
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2338_ = lean_string_dec_eq(v_str_2330_, v___x_2337_);
lean_dec_ref(v_str_2330_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v_str_2329_);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
else
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2340_ = lean_string_dec_eq(v_str_2329_, v___x_2339_);
lean_dec_ref(v_str_2329_);
if (v___x_2340_ == 0)
{
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_unsigned_to_nat(0u);
v___x_2342_ = l_Lean_Syntax_getArg(v___x_2322_, v___x_2341_);
lean_dec_ref_known(v___x_2322_, 3);
if (lean_obj_tag(v___x_2342_) == 2)
{
lean_object* v_val_2343_; 
lean_dec(v_stx_2303_);
v_val_2343_ = lean_ctor_get(v___x_2342_, 1);
lean_inc_ref(v_val_2343_);
lean_dec_ref_known(v___x_2342_, 2);
v_val_2314_ = v_val_2343_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v___x_2342_);
v___x_2344_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2303_);
v___x_2345_ = l_Lean_MessageData_ofSyntax(v_stx_2303_);
v___x_2346_ = l_Lean_indentD(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2344_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2303_, v___x_2347_, v___y_2304_, v___y_2305_);
lean_dec(v_stx_2303_);
return v___x_2348_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2327_, 2);
lean_dec_ref_known(v_pre_2326_, 2);
lean_dec_ref_known(v_pre_2325_, 2);
lean_dec_ref_known(v_kind_2324_, 2);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
}
else
{
lean_dec(v_pre_2327_);
lean_dec_ref_known(v_pre_2326_, 2);
lean_dec_ref_known(v_pre_2325_, 2);
lean_dec_ref_known(v_kind_2324_, 2);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
}
else
{
lean_dec(v_pre_2326_);
lean_dec_ref_known(v_pre_2325_, 2);
lean_dec_ref_known(v_kind_2324_, 2);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
}
else
{
lean_dec_ref_known(v_kind_2324_, 2);
lean_dec(v_pre_2325_);
lean_dec_ref_known(v___x_2322_, 3);
goto v___jp_2307_;
}
}
else
{
lean_dec_ref_known(v___x_2322_, 3);
lean_dec(v_kind_2324_);
goto v___jp_2307_;
}
}
default: 
{
lean_dec(v___x_2322_);
goto v___jp_2307_;
}
}
v___jp_2307_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2308_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2303_);
v___x_2309_ = l_Lean_MessageData_ofSyntax(v_stx_2303_);
v___x_2310_ = l_Lean_indentD(v___x_2309_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2308_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2303_, v___x_2311_, v___y_2304_, v___y_2305_);
lean_dec(v_stx_2303_);
return v___x_2312_;
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_string_utf8_byte_size(v_val_2314_);
v___x_2317_ = lean_unsigned_to_nat(2u);
v___x_2318_ = lean_nat_sub(v___x_2316_, v___x_2317_);
v___x_2319_ = lean_string_utf8_extract(v_val_2314_, v___x_2315_, v___x_2318_);
lean_dec(v___x_2318_);
lean_dec_ref(v_val_2314_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object* v_stx_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_stx_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(lean_object* v_docOpt_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = l_Lean_Syntax_isNone(v_docOpt_2354_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v_docStx_2360_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2359_ = lean_unsigned_to_nat(0u);
v_docStx_2360_ = l_Lean_Syntax_getArg(v_docOpt_2354_, v___x_2359_);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = l_Lean_Syntax_getArg(v_docStx_2360_, v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 1)
{
lean_object* v_kind_2391_; 
v_kind_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_kind_2391_);
if (lean_obj_tag(v_kind_2391_) == 1)
{
lean_object* v_pre_2392_; 
v_pre_2392_ = lean_ctor_get(v_kind_2391_, 0);
lean_inc(v_pre_2392_);
if (lean_obj_tag(v_pre_2392_) == 1)
{
lean_object* v_pre_2393_; 
v_pre_2393_ = lean_ctor_get(v_pre_2392_, 0);
lean_inc(v_pre_2393_);
if (lean_obj_tag(v_pre_2393_) == 1)
{
lean_object* v_pre_2394_; 
v_pre_2394_ = lean_ctor_get(v_pre_2393_, 0);
lean_inc(v_pre_2394_);
if (lean_obj_tag(v_pre_2394_) == 1)
{
lean_object* v_pre_2395_; 
v_pre_2395_ = lean_ctor_get(v_pre_2394_, 0);
if (lean_obj_tag(v_pre_2395_) == 0)
{
lean_object* v_str_2396_; lean_object* v_str_2397_; lean_object* v_str_2398_; lean_object* v_str_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v_str_2396_ = lean_ctor_get(v_kind_2391_, 1);
lean_inc_ref(v_str_2396_);
lean_dec_ref_known(v_kind_2391_, 2);
v_str_2397_ = lean_ctor_get(v_pre_2392_, 1);
lean_inc_ref(v_str_2397_);
lean_dec_ref_known(v_pre_2392_, 2);
v_str_2398_ = lean_ctor_get(v_pre_2393_, 1);
lean_inc_ref(v_str_2398_);
lean_dec_ref_known(v_pre_2393_, 2);
v_str_2399_ = lean_ctor_get(v_pre_2394_, 1);
lean_inc_ref(v_str_2399_);
lean_dec_ref_known(v_pre_2394_, 2);
v___x_2400_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2401_ = lean_string_dec_eq(v_str_2399_, v___x_2400_);
lean_dec_ref(v_str_2399_);
if (v___x_2401_ == 0)
{
lean_dec_ref(v_str_2398_);
lean_dec_ref(v_str_2397_);
lean_dec_ref(v_str_2396_);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2403_ = lean_string_dec_eq(v_str_2398_, v___x_2402_);
lean_dec_ref(v_str_2398_);
if (v___x_2403_ == 0)
{
lean_dec_ref(v_str_2397_);
lean_dec_ref(v_str_2396_);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2405_ = lean_string_dec_eq(v_str_2397_, v___x_2404_);
lean_dec_ref(v_str_2397_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v_str_2396_);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2407_ = lean_string_dec_eq(v_str_2396_, v___x_2406_);
lean_dec_ref(v_str_2396_);
if (v___x_2407_ == 0)
{
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = l_Lean_Syntax_getArg(v___x_2390_, v___x_2359_);
lean_dec_ref_known(v___x_2390_, 3);
v___x_2409_ = l_Lean_Syntax_isAtom(v___x_2408_);
lean_dec(v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v_docStx_2360_);
v___x_2410_ = lean_box(v___x_2358_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
else
{
if (v___x_2358_ == 0)
{
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v_docStx_2360_);
v___x_2412_ = lean_box(v___x_2358_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2394_, 2);
lean_dec_ref_known(v_pre_2393_, 2);
lean_dec_ref_known(v_pre_2392_, 2);
lean_dec_ref_known(v_kind_2391_, 2);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
}
else
{
lean_dec_ref_known(v_pre_2393_, 2);
lean_dec(v_pre_2394_);
lean_dec_ref_known(v_pre_2392_, 2);
lean_dec_ref_known(v_kind_2391_, 2);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
}
else
{
lean_dec_ref_known(v_pre_2392_, 2);
lean_dec(v_pre_2393_);
lean_dec_ref_known(v_kind_2391_, 2);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
}
else
{
lean_dec_ref_known(v_kind_2391_, 2);
lean_dec(v_pre_2392_);
lean_dec_ref_known(v___x_2390_, 3);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
}
else
{
lean_dec_ref_known(v___x_2390_, 3);
lean_dec(v_kind_2391_);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
}
else
{
lean_dec(v___x_2390_);
v___y_2362_ = v_a_2355_;
v___y_2363_ = v_a_2356_;
goto v___jp_2361_;
}
v___jp_2361_:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_docStx_2360_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2380_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2380_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2380_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_startInclusive_2372_; lean_object* v_endExclusive_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2369_ = lean_string_utf8_byte_size(v_a_2365_);
v___x_2370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2370_, 0, v_a_2365_);
lean_ctor_set(v___x_2370_, 1, v___x_2359_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
v___x_2371_ = l_String_Slice_trimAscii(v___x_2370_);
v_startInclusive_2372_ = lean_ctor_get(v___x_2371_, 1);
lean_inc(v_startInclusive_2372_);
v_endExclusive_2373_ = lean_ctor_get(v___x_2371_, 2);
lean_inc(v_endExclusive_2373_);
lean_dec_ref(v___x_2371_);
v___x_2374_ = lean_nat_sub(v_endExclusive_2373_, v_startInclusive_2372_);
lean_dec(v_startInclusive_2372_);
lean_dec(v_endExclusive_2373_);
v___x_2375_ = lean_nat_dec_eq(v___x_2374_, v___x_2359_);
lean_dec(v___x_2374_);
v___x_2376_ = lean_box(v___x_2375_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2376_);
v___x_2378_ = v___x_2367_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2381_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2364_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2364_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
else
{
uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = 0;
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___boxed(lean_object* v_docOpt_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_docOpt_2417_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(lean_object* v_00_u03b1_2422_, lean_object* v_ref_2423_, lean_object* v_msg_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2423_, v_msg_2424_, v___y_2425_, v___y_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_ref_2430_, lean_object* v_msg_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(v_00_u03b1_2429_, v_ref_2430_, v_msg_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_ref_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2436_, lean_object* v_msg_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2437_, v___y_2438_, v___y_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_msg_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(v_00_u03b1_2442_, v_msg_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2448_, lean_object* v_macroStack_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2448_, v_macroStack_2449_, v___y_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2454_, lean_object* v_macroStack_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(v_msgData_2454_, v_macroStack_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc(lean_object* v_docOpt_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2460_, v_a_2461_, v_a_2462_);
if (lean_obj_tag(v___x_2464_) == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = l_Lean_Syntax_isNone(v_docOpt_2460_);
if (v___x_2465_ == 0)
{
return v___x_2464_;
}
else
{
lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2464_, 0);
lean_dec(v_unused_2474_);
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_box(v___x_2465_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc___boxed(lean_object* v_docOpt_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Linter_MissingDocs_isMissingDoc(v_docOpt_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_docOpt_2475_);
return v_res_2479_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object* v_as_2490_, size_t v_i_2491_, size_t v_stop_2492_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_eq(v_i_2491_, v_stop_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; uint8_t v___x_2495_; uint8_t v___y_2497_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = 1;
v___x_2501_ = lean_array_uget_borrowed(v_as_2490_, v_i_2491_);
v___x_2502_ = l_Lean_Syntax_getArg(v___x_2501_, v___x_2494_);
v___x_2503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2));
lean_inc(v___x_2502_);
v___x_2504_ = l_Lean_Syntax_isOfKind(v___x_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_dec(v___x_2502_);
v___y_2497_ = v___x_2504_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = l_Lean_Syntax_getArg(v___x_2502_, v___x_2505_);
lean_dec(v___x_2502_);
v___x_2507_ = l_Lean_Syntax_getId(v___x_2506_);
lean_dec(v___x_2506_);
v___x_2508_ = l_Lean_Name_eraseMacroScopes(v___x_2507_);
lean_dec(v___x_2507_);
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4));
v___x_2510_ = lean_name_eq(v___x_2508_, v___x_2509_);
lean_dec(v___x_2508_);
v___y_2497_ = v___x_2510_;
goto v___jp_2496_;
}
v___jp_2496_:
{
if (v___y_2497_ == 0)
{
size_t v___x_2498_; size_t v___x_2499_; 
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2491_, v___x_2498_);
v_i_2491_ = v___x_2499_;
goto _start;
}
else
{
return v___x_2495_;
}
}
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object* v_as_2512_, lean_object* v_i_2513_, lean_object* v_stop_2514_){
_start:
{
size_t v_i_boxed_2515_; size_t v_stop_boxed_2516_; uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_i_boxed_2515_ = lean_unbox_usize(v_i_2513_);
lean_dec(v_i_2513_);
v_stop_boxed_2516_ = lean_unbox_usize(v_stop_2514_);
lean_dec(v_stop_2514_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v_as_2512_, v_i_boxed_2515_, v_stop_boxed_2516_);
lean_dec_ref(v_as_2512_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object* v_attrs_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = l_Lean_Syntax_getArg(v_attrs_2519_, v___x_2520_);
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = l_Lean_Syntax_getArg(v___x_2521_, v___x_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = l_Lean_Syntax_getSepArgs(v___x_2523_);
lean_dec(v___x_2523_);
v___x_2525_ = lean_array_get_size(v___x_2524_);
v___x_2526_ = lean_nat_dec_lt(v___x_2520_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_dec_ref(v___x_2524_);
return v___x_2526_;
}
else
{
if (v___x_2526_ == 0)
{
lean_dec_ref(v___x_2524_);
return v___x_2526_;
}
else
{
size_t v___x_2527_; size_t v___x_2528_; uint8_t v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2525_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v___x_2524_, v___x_2527_, v___x_2528_);
lean_dec_ref(v___x_2524_);
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object* v_attrs_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2530_);
lean_dec(v_attrs_2530_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(lean_object* v_as_2539_, size_t v_i_2540_, size_t v_stop_2541_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_usize_dec_eq(v_i_2540_, v_stop_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_array_uget_borrowed(v_as_2539_, v_i_2540_);
v___x_2545_ = l_Lean_Syntax_getArg(v___x_2544_, v___x_2543_);
v___x_2546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1));
v___x_2547_ = l_Lean_Syntax_isOfKind(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
size_t v___x_2548_; size_t v___x_2549_; 
v___x_2548_ = ((size_t)1ULL);
v___x_2549_ = lean_usize_add(v_i_2540_, v___x_2548_);
v_i_2540_ = v___x_2549_;
goto _start;
}
else
{
return v___x_2547_;
}
}
else
{
uint8_t v___x_2551_; 
v___x_2551_ = 0;
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___boxed(lean_object* v_as_2552_, lean_object* v_i_2553_, lean_object* v_stop_2554_){
_start:
{
size_t v_i_boxed_2555_; size_t v_stop_boxed_2556_; uint8_t v_res_2557_; lean_object* v_r_2558_; 
v_i_boxed_2555_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_stop_boxed_2556_ = lean_unbox_usize(v_stop_2554_);
lean_dec(v_stop_2554_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v_as_2552_, v_i_boxed_2555_, v_stop_boxed_2556_);
lean_dec_ref(v_as_2552_);
v_r_2558_ = lean_box(v_res_2557_);
return v_r_2558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasTacticAlt(lean_object* v_attrs_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = l_Lean_Syntax_getArg(v_attrs_2559_, v___x_2560_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = l_Lean_Syntax_getArg(v___x_2561_, v___x_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = l_Lean_Syntax_getSepArgs(v___x_2563_);
lean_dec(v___x_2563_);
v___x_2565_ = lean_array_get_size(v___x_2564_);
v___x_2566_ = lean_nat_dec_lt(v___x_2560_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_dec_ref(v___x_2564_);
return v___x_2566_;
}
else
{
if (v___x_2566_ == 0)
{
lean_dec_ref(v___x_2564_);
return v___x_2566_;
}
else
{
size_t v___x_2567_; size_t v___x_2568_; uint8_t v___x_2569_; 
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = lean_usize_of_nat(v___x_2565_);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v___x_2564_, v___x_2567_, v___x_2568_);
lean_dec_ref(v___x_2564_);
return v___x_2569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasTacticAlt___boxed(lean_object* v_attrs_2570_){
_start:
{
uint8_t v_res_2571_; lean_object* v_r_2572_; 
v_res_2571_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2570_);
lean_dec(v_attrs_2570_);
v_r_2572_ = lean_box(v_res_2571_);
return v_r_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus(lean_object* v_mods_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_st_ref_get(v_a_2585_);
v___x_2588_ = l_Lean_Elab_Command_getScope___redArg(v_a_2585_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2653_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2653_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2653_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___y_2599_; lean_object* v_env_2642_; lean_object* v___x_2643_; uint8_t v_isModule_2644_; 
v_env_2642_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_ref(v_env_2642_);
lean_dec(v___x_2587_);
v___x_2643_ = l_Lean_Environment_header(v_env_2642_);
lean_dec_ref(v_env_2642_);
v_isModule_2644_ = lean_ctor_get_uint8(v___x_2643_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2643_);
if (v_isModule_2644_ == 0)
{
lean_dec(v_a_2589_);
goto v___jp_2633_;
}
else
{
uint8_t v_isPublic_2645_; 
v_isPublic_2645_ = lean_ctor_get_uint8(v_a_2589_, sizeof(void*)*10 + 1);
lean_dec(v_a_2589_);
if (v_isPublic_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = l_Lean_Syntax_getArg(v_mods_2583_, v___x_2646_);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = l_Lean_Syntax_getArg(v___x_2647_, v___x_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = l_Lean_Syntax_getKind(v___x_2649_);
v___x_2651_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1));
v___x_2652_ = lean_name_eq(v___x_2650_, v___x_2651_);
lean_dec(v___x_2650_);
if (v___x_2652_ == 0)
{
goto v___jp_2593_;
}
else
{
v___y_2599_ = v_isModule_2644_;
goto v___jp_2598_;
}
}
else
{
goto v___jp_2633_;
}
}
v___jp_2593_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = l_Lean_Syntax_getArg(v_mods_2583_, v___x_2600_);
v___x_2602_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v___x_2601_);
lean_dec(v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
lean_del_object(v___x_2591_);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = l_Lean_Syntax_getArg(v_mods_2583_, v___x_2603_);
v___x_2605_ = l_Lean_Syntax_isNone(v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_2604_, v_a_2584_, v_a_2585_);
lean_dec(v___x_2604_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2621_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2612_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2616_ = lean_box(v___y_2599_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2617_);
v___x_2619_ = v___x_2609_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2606_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2606_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v___x_2604_);
v___x_2630_ = lean_box(v___x_2602_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
else
{
goto v___jp_2593_;
}
}
v___jp_2633_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2634_ = lean_unsigned_to_nat(2u);
v___x_2635_ = l_Lean_Syntax_getArg(v_mods_2583_, v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = l_Lean_Syntax_getArg(v___x_2635_, v___x_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = l_Lean_Syntax_getKind(v___x_2637_);
v___x_2639_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_2640_ = lean_name_eq(v___x_2638_, v___x_2639_);
lean_dec(v___x_2638_);
if (v___x_2640_ == 0)
{
uint8_t v___x_2641_; 
v___x_2641_ = 1;
v___y_2599_ = v___x_2641_;
goto v___jp_2598_;
}
else
{
goto v___jp_2593_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v___x_2587_);
v_a_2654_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2588_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2588_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___boxed(lean_object* v_mods_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_mods_2662_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object* v_mods_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2667_, v_a_2668_, v_a_2669_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2686_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 0)
{
uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2676_ = 0;
v___x_2677_ = lean_box(v___x_2676_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2677_);
v___x_2679_ = v___x_2674_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
else
{
uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec_ref_known(v_a_2672_, 1);
v___x_2681_ = 1;
v___x_2682_ = lean_box(v___x_2681_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2682_);
v___x_2684_ = v___x_2674_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2671_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2671_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object* v_mods_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(v_mods_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_mods_2695_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(uint8_t v_isEmpty_2700_, lean_object* v_stx_2701_, lean_object* v_msg_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
if (v_isEmpty_2700_ == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_Linter_MissingDocs_lint(v_stx_2701_, v_msg_2702_, v_a_2703_, v_a_2704_);
return v___x_2706_;
}
else
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2701_, v_msg_2702_, v_a_2703_, v_a_2704_);
return v___x_2707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus___boxed(lean_object* v_isEmpty_2708_, lean_object* v_stx_2709_, lean_object* v_msg_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
uint8_t v_isEmpty_boxed_2714_; lean_object* v_res_2715_; 
v_isEmpty_boxed_2714_ = lean_unbox(v_isEmpty_2708_);
v_res_2715_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v_isEmpty_boxed_2714_, v_stx_2709_, v_msg_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(uint8_t v_isEmpty_2716_, lean_object* v_stx_2717_, lean_object* v_msg_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
if (v_isEmpty_2716_ == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2717_, v_msg_2718_, v_a_2719_, v_a_2720_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2717_, v_msg_2718_, v_a_2719_, v_a_2720_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed___boxed(lean_object* v_isEmpty_2724_, lean_object* v_stx_2725_, lean_object* v_msg_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
uint8_t v_isEmpty_boxed_2730_; lean_object* v_res_2731_; 
v_isEmpty_boxed_2730_ = lean_unbox(v_isEmpty_2724_);
v_res_2731_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_boxed_2730_, v_stx_2725_, v_msg_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(uint8_t v_isEmpty_2732_, lean_object* v_parent_2733_, lean_object* v_stx_2734_, lean_object* v_msg_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
if (v_isEmpty_2732_ == 0)
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2733_, v_stx_2734_, v_msg_2735_, v_a_2736_, v_a_2737_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2733_, v_stx_2734_, v_msg_2735_, v_a_2736_, v_a_2737_);
return v___x_2740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField___boxed(lean_object* v_isEmpty_2741_, lean_object* v_parent_2742_, lean_object* v_stx_2743_, lean_object* v_msg_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
uint8_t v_isEmpty_boxed_2748_; lean_object* v_res_2749_; 
v_isEmpty_boxed_2748_ = lean_unbox(v_isEmpty_2741_);
v_res_2749_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_isEmpty_boxed_2748_, v_parent_2742_, v_stx_2743_, v_msg_2744_, v_a_2745_, v_a_2746_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_parent_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object* v_k_2798_, lean_object* v_id_2799_, uint8_t v_isEmpty_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__1));
v___x_2805_ = lean_name_eq(v_k_2798_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__3));
v___x_2807_ = lean_name_eq(v_k_2798_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__5));
v___x_2809_ = lean_name_eq(v_k_2798_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__7));
v___x_2811_ = lean_name_eq(v_k_2798_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_2813_ = lean_name_eq(v_k_2798_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_2815_ = lean_name_eq(v_k_2798_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_2817_ = lean_name_eq(v_k_2798_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v_id_2799_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__14));
v___x_2821_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2820_, v_a_2801_, v_a_2802_);
return v___x_2821_;
}
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2823_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2822_, v_a_2801_, v_a_2802_);
return v___x_2823_;
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2825_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2824_, v_a_2801_, v_a_2802_);
return v___x_2825_;
}
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__16));
v___x_2827_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2826_, v_a_2801_, v_a_2802_);
return v___x_2827_;
}
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__17));
v___x_2829_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2828_, v_a_2801_, v_a_2802_);
return v___x_2829_;
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__18));
v___x_2831_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2830_, v_a_2801_, v_a_2802_);
return v___x_2831_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__19));
v___x_2833_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2800_, v_id_2799_, v___x_2832_, v_a_2801_, v_a_2802_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object* v_k_2834_, lean_object* v_id_2835_, lean_object* v_isEmpty_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
uint8_t v_isEmpty_boxed_2840_; lean_object* v_res_2841_; 
v_isEmpty_boxed_2840_ = lean_unbox(v_isEmpty_2836_);
v_res_2841_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_2834_, v_id_2835_, v_isEmpty_boxed_2840_, v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_k_2834_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(lean_object* v_docOpt_2845_, lean_object* v_attrs_2846_, uint8_t v_checkTacticAlt_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2846_);
if (v___x_2851_ == 0)
{
uint8_t v___y_2853_; 
if (v_checkTacticAlt_2847_ == 0)
{
v___y_2853_ = v___x_2851_;
goto v___jp_2852_;
}
else
{
uint8_t v___x_2883_; 
v___x_2883_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2846_);
v___y_2853_ = v___x_2883_;
goto v___jp_2852_;
}
v___jp_2852_:
{
if (v___y_2853_ == 0)
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Syntax_isNone(v_docOpt_2845_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2845_, v_a_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2869_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_unbox(v_a_2856_);
lean_dec(v_a_2856_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_box(0);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2861_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2865_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0));
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2865_);
v___x_2867_ = v___x_2858_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2855_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2855_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_box(v___y_2853_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___boxed(lean_object* v_docOpt_2886_, lean_object* v_attrs_2887_, lean_object* v_checkTacticAlt_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
uint8_t v_checkTacticAlt_boxed_2892_; lean_object* v_res_2893_; 
v_checkTacticAlt_boxed_2892_ = lean_unbox(v_checkTacticAlt_2888_);
v_res_2893_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v_docOpt_2886_, v_attrs_2887_, v_checkTacticAlt_boxed_2892_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_attrs_2887_);
lean_dec(v_docOpt_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object* v_rest_2895_, lean_object* v_as_2896_, size_t v_sz_2897_, size_t v_i_2898_, lean_object* v_b_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_a_2904_; uint8_t v___x_2908_; 
v___x_2908_ = lean_usize_dec_lt(v_i_2898_, v_sz_2897_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_b_2899_);
return v___x_2909_;
}
else
{
lean_object* v___x_2910_; lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_unsigned_to_nat(0u);
v_a_2911_ = lean_array_uget_borrowed(v_as_2896_, v_i_2898_);
v___x_2912_ = l_Lean_Syntax_getArg(v_a_2911_, v___x_2910_);
v___x_2913_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_2912_, v___y_2900_, v___y_2901_);
lean_dec(v___x_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = lean_box(0);
if (lean_obj_tag(v_a_2914_) == 1)
{
lean_object* v_val_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; 
v_val_2916_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_a_2914_, 1);
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = l_Lean_Syntax_getArg(v_rest_2895_, v___x_2917_);
v___x_2919_ = l_Lean_Syntax_getArg(v___x_2918_, v___x_2910_);
lean_dec(v___x_2918_);
v___x_2920_ = l_Lean_Syntax_getArg(v_a_2911_, v___x_2917_);
v___x_2921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0));
v___x_2922_ = lean_unbox(v_val_2916_);
lean_dec(v_val_2916_);
v___x_2923_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_2922_, v___x_2919_, v___x_2920_, v___x_2921_, v___y_2900_, v___y_2901_);
lean_dec(v___x_2919_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_dec_ref_known(v___x_2923_, 1);
v_a_2904_ = v___x_2915_;
goto v___jp_2903_;
}
else
{
return v___x_2923_;
}
}
else
{
lean_dec(v_a_2914_);
v_a_2904_ = v___x_2915_;
goto v___jp_2903_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v_a_2924_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2913_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2913_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
v___jp_2903_:
{
size_t v___x_2905_; size_t v___x_2906_; 
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_i_2898_, v___x_2905_);
v_i_2898_ = v___x_2906_;
v_b_2899_ = v_a_2904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___boxed(lean_object* v_rest_2932_, lean_object* v_as_2933_, lean_object* v_sz_2934_, lean_object* v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
size_t v_sz_boxed_2940_; size_t v_i_boxed_2941_; lean_object* v_res_2942_; 
v_sz_boxed_2940_ = lean_unbox_usize(v_sz_2934_);
lean_dec(v_sz_2934_);
v_i_boxed_2941_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_2932_, v_as_2933_, v_sz_boxed_2940_, v_i_boxed_2941_, v_b_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v_as_2933_);
lean_dec(v_rest_2932_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
return v_x_2943_;
}
else
{
lean_object* v_key_2945_; lean_object* v_value_2946_; lean_object* v_tail_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2970_; 
v_key_2945_ = lean_ctor_get(v_x_2944_, 0);
v_value_2946_ = lean_ctor_get(v_x_2944_, 1);
v_tail_2947_ = lean_ctor_get(v_x_2944_, 2);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2944_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2949_ = v_x_2944_;
v_isShared_2950_ = v_isSharedCheck_2970_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_tail_2947_);
lean_inc(v_value_2946_);
lean_inc(v_key_2945_);
lean_dec(v_x_2944_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2970_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v_fold_2955_; uint64_t v___x_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; size_t v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2951_ = lean_array_get_size(v_x_2943_);
v___x_2952_ = l_String_instHashableRaw_hash(v_key_2945_);
v___x_2953_ = 32ULL;
v___x_2954_ = lean_uint64_shift_right(v___x_2952_, v___x_2953_);
v_fold_2955_ = lean_uint64_xor(v___x_2952_, v___x_2954_);
v___x_2956_ = 16ULL;
v___x_2957_ = lean_uint64_shift_right(v_fold_2955_, v___x_2956_);
v___x_2958_ = lean_uint64_xor(v_fold_2955_, v___x_2957_);
v___x_2959_ = lean_uint64_to_usize(v___x_2958_);
v___x_2960_ = lean_usize_of_nat(v___x_2951_);
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = lean_usize_sub(v___x_2960_, v___x_2961_);
v___x_2963_ = lean_usize_land(v___x_2959_, v___x_2962_);
v___x_2964_ = lean_array_uget_borrowed(v_x_2943_, v___x_2963_);
lean_inc(v___x_2964_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 2, v___x_2964_);
v___x_2966_ = v___x_2949_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_key_2945_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_value_2946_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_array_uset(v_x_2943_, v___x_2963_, v___x_2966_);
v_x_2943_ = v___x_2967_;
v_x_2944_ = v_tail_2947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(lean_object* v_i_2971_, lean_object* v_source_2972_, lean_object* v_target_2973_){
_start:
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = lean_array_get_size(v_source_2972_);
v___x_2975_ = lean_nat_dec_lt(v_i_2971_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v_source_2972_);
lean_dec(v_i_2971_);
return v_target_2973_;
}
else
{
lean_object* v_es_2976_; lean_object* v___x_2977_; lean_object* v_source_2978_; lean_object* v_target_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_es_2976_ = lean_array_fget(v_source_2972_, v_i_2971_);
v___x_2977_ = lean_box(0);
v_source_2978_ = lean_array_fset(v_source_2972_, v_i_2971_, v___x_2977_);
v_target_2979_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_target_2973_, v_es_2976_);
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_add(v_i_2971_, v___x_2980_);
lean_dec(v_i_2971_);
v_i_2971_ = v___x_2981_;
v_source_2972_ = v_source_2978_;
v_target_2973_ = v_target_2979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(lean_object* v_data_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_nbuckets_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2984_ = lean_array_get_size(v_data_2983_);
v___x_2985_ = lean_unsigned_to_nat(2u);
v_nbuckets_2986_ = lean_nat_mul(v___x_2984_, v___x_2985_);
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = lean_box(0);
v___x_2989_ = lean_mk_array(v_nbuckets_2986_, v___x_2988_);
v___x_2990_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v___x_2987_, v_data_2983_, v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(lean_object* v_a_2991_, lean_object* v_x_2992_){
_start:
{
if (lean_obj_tag(v_x_2992_) == 0)
{
uint8_t v___x_2993_; 
v___x_2993_ = 0;
return v___x_2993_;
}
else
{
lean_object* v_key_2994_; lean_object* v_tail_2995_; uint8_t v_decide_2996_; 
v_key_2994_ = lean_ctor_get(v_x_2992_, 0);
v_tail_2995_ = lean_ctor_get(v_x_2992_, 2);
v_decide_2996_ = lean_nat_dec_eq(v_key_2994_, v_a_2991_);
if (v_decide_2996_ == 0)
{
v_x_2992_ = v_tail_2995_;
goto _start;
}
else
{
return v_decide_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg___boxed(lean_object* v_a_2998_, lean_object* v_x_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_2998_, v_x_2999_);
lean_dec(v_x_2999_);
lean_dec(v_a_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(lean_object* v_m_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_){
_start:
{
lean_object* v_size_3005_; lean_object* v_buckets_3006_; lean_object* v___x_3007_; uint64_t v___x_3008_; uint64_t v___x_3009_; uint64_t v___x_3010_; uint64_t v_fold_3011_; uint64_t v___x_3012_; uint64_t v___x_3013_; uint64_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; size_t v___x_3018_; size_t v___x_3019_; lean_object* v_bkt_3020_; uint8_t v___x_3021_; 
v_size_3005_ = lean_ctor_get(v_m_3002_, 0);
v_buckets_3006_ = lean_ctor_get(v_m_3002_, 1);
v___x_3007_ = lean_array_get_size(v_buckets_3006_);
v___x_3008_ = l_String_instHashableRaw_hash(v_a_3003_);
v___x_3009_ = 32ULL;
v___x_3010_ = lean_uint64_shift_right(v___x_3008_, v___x_3009_);
v_fold_3011_ = lean_uint64_xor(v___x_3008_, v___x_3010_);
v___x_3012_ = 16ULL;
v___x_3013_ = lean_uint64_shift_right(v_fold_3011_, v___x_3012_);
v___x_3014_ = lean_uint64_xor(v_fold_3011_, v___x_3013_);
v___x_3015_ = lean_uint64_to_usize(v___x_3014_);
v___x_3016_ = lean_usize_of_nat(v___x_3007_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_sub(v___x_3016_, v___x_3017_);
v___x_3019_ = lean_usize_land(v___x_3015_, v___x_3018_);
v_bkt_3020_ = lean_array_uget_borrowed(v_buckets_3006_, v___x_3019_);
v___x_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3003_, v_bkt_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3042_; 
lean_inc_ref(v_buckets_3006_);
lean_inc(v_size_3005_);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_m_3002_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; lean_object* v_unused_3044_; 
v_unused_3043_ = lean_ctor_get(v_m_3002_, 1);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v_m_3002_, 0);
lean_dec(v_unused_3044_);
v___x_3023_ = v_m_3002_;
v_isShared_3024_ = v_isSharedCheck_3042_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v_m_3002_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3042_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v_size_x27_3026_; lean_object* v___x_3027_; lean_object* v_buckets_x27_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3025_ = lean_unsigned_to_nat(1u);
v_size_x27_3026_ = lean_nat_add(v_size_3005_, v___x_3025_);
lean_dec(v_size_3005_);
lean_inc(v_bkt_3020_);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3003_);
lean_ctor_set(v___x_3027_, 1, v_b_3004_);
lean_ctor_set(v___x_3027_, 2, v_bkt_3020_);
v_buckets_x27_3028_ = lean_array_uset(v_buckets_3006_, v___x_3019_, v___x_3027_);
v___x_3029_ = lean_unsigned_to_nat(4u);
v___x_3030_ = lean_nat_mul(v_size_x27_3026_, v___x_3029_);
v___x_3031_ = lean_unsigned_to_nat(3u);
v___x_3032_ = lean_nat_div(v___x_3030_, v___x_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_array_get_size(v_buckets_x27_3028_);
v___x_3034_ = lean_nat_dec_le(v___x_3032_, v___x_3033_);
lean_dec(v___x_3032_);
if (v___x_3034_ == 0)
{
lean_object* v_val_3035_; lean_object* v___x_3037_; 
v_val_3035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_buckets_x27_3028_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_val_3035_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3026_);
v___x_3037_ = v___x_3023_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_size_x27_3026_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_val_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
else
{
lean_object* v___x_3040_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_buckets_x27_3028_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3026_);
v___x_3040_ = v___x_3023_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_size_x27_3026_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_buckets_x27_3028_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec(v_b_3004_);
lean_dec(v_a_3003_);
return v_m_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(uint8_t v___x_3045_, lean_object* v_x_3046_, lean_object* v_info_3047_, lean_object* v_s_3048_){
_start:
{
if (lean_obj_tag(v_info_3047_) == 12)
{
lean_object* v_i_3049_; lean_object* v___x_3050_; 
v_i_3049_ = lean_ctor_get(v_info_3047_, 0);
v___x_3050_ = l_Lean_Syntax_getRange_x3f(v_i_3049_, v___x_3045_);
if (lean_obj_tag(v___x_3050_) == 1)
{
lean_object* v_val_3051_; lean_object* v_start_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v_val_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_val_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v_start_3052_ = lean_ctor_get(v_val_3051_, 0);
lean_inc(v_start_3052_);
lean_dec(v_val_3051_);
v___x_3053_ = lean_box(0);
v___x_3054_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_s_3048_, v_start_3052_, v___x_3053_);
return v___x_3054_;
}
else
{
lean_dec(v___x_3050_);
return v_s_3048_;
}
}
else
{
return v_s_3048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed(lean_object* v___x_3055_, lean_object* v_x_3056_, lean_object* v_info_3057_, lean_object* v_s_3058_){
_start:
{
uint8_t v___x_8544__boxed_3059_; lean_object* v_res_3060_; 
v___x_8544__boxed_3059_ = lean_unbox(v___x_3055_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(v___x_8544__boxed_3059_, v_x_3056_, v_info_3057_, v_s_3058_);
lean_dec_ref(v_info_3057_);
lean_dec_ref(v_x_3056_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(uint8_t v___x_3061_, lean_object* v_as_3062_, size_t v_i_3063_, size_t v_stop_3064_, lean_object* v_b_3065_){
_start:
{
uint8_t v___x_3066_; 
v___x_3066_ = lean_usize_dec_eq(v_i_3063_, v_stop_3064_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; size_t v___x_3071_; size_t v___x_3072_; 
v___x_3067_ = lean_box(v___x_3061_);
v___f_3068_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3068_, 0, v___x_3067_);
v___x_3069_ = lean_array_uget_borrowed(v_as_3062_, v_i_3063_);
lean_inc(v___x_3069_);
v___x_3070_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_3068_, v_b_3065_, v___x_3069_);
v___x_3071_ = ((size_t)1ULL);
v___x_3072_ = lean_usize_add(v_i_3063_, v___x_3071_);
v_i_3063_ = v___x_3072_;
v_b_3065_ = v___x_3070_;
goto _start;
}
else
{
return v_b_3065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___boxed(lean_object* v___x_3074_, lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_stop_3077_, lean_object* v_b_3078_){
_start:
{
uint8_t v___x_8560__boxed_3079_; size_t v_i_boxed_3080_; size_t v_stop_boxed_3081_; lean_object* v_res_3082_; 
v___x_8560__boxed_3079_ = lean_unbox(v___x_3074_);
v_i_boxed_3080_ = lean_unbox_usize(v_i_3076_);
lean_dec(v_i_3076_);
v_stop_boxed_3081_ = lean_unbox_usize(v_stop_3077_);
lean_dec(v_stop_3077_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_8560__boxed_3079_, v_as_3075_, v_i_boxed_3080_, v_stop_boxed_3081_, v_b_3078_);
lean_dec_ref(v_as_3075_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(uint8_t v___x_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
lean_object* v_cs_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_cs_3086_ = lean_ctor_get(v_x_3084_, 0);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_array_get_size(v_cs_3086_);
v___x_3089_ = lean_nat_dec_lt(v___x_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
return v_x_3085_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___x_3088_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3083_, v_cs_3086_, v___x_3090_, v___x_3091_, v_x_3085_);
return v___x_3092_;
}
}
else
{
lean_object* v_vs_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_vs_3093_ = lean_ctor_get(v_x_3084_, 0);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_array_get_size(v_vs_3093_);
v___x_3096_ = lean_nat_dec_lt(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
return v_x_3085_;
}
else
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = lean_usize_of_nat(v___x_3095_);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3083_, v_vs_3093_, v___x_3097_, v___x_3098_, v_x_3085_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(uint8_t v___x_3100_, lean_object* v_as_3101_, size_t v_i_3102_, size_t v_stop_3103_, lean_object* v_b_3104_){
_start:
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_usize_dec_eq(v_i_3102_, v_stop_3103_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; size_t v___x_3108_; size_t v___x_3109_; 
v___x_3106_ = lean_array_uget_borrowed(v_as_3101_, v_i_3102_);
v___x_3107_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3100_, v___x_3106_, v_b_3104_);
v___x_3108_ = ((size_t)1ULL);
v___x_3109_ = lean_usize_add(v_i_3102_, v___x_3108_);
v_i_3102_ = v___x_3109_;
v_b_3104_ = v___x_3107_;
goto _start;
}
else
{
return v_b_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7___boxed(lean_object* v___x_3111_, lean_object* v_as_3112_, lean_object* v_i_3113_, lean_object* v_stop_3114_, lean_object* v_b_3115_){
_start:
{
uint8_t v___x_8579__boxed_3116_; size_t v_i_boxed_3117_; size_t v_stop_boxed_3118_; lean_object* v_res_3119_; 
v___x_8579__boxed_3116_ = lean_unbox(v___x_3111_);
v_i_boxed_3117_ = lean_unbox_usize(v_i_3113_);
lean_dec(v_i_3113_);
v_stop_boxed_3118_ = lean_unbox_usize(v_stop_3114_);
lean_dec(v_stop_3114_);
v_res_3119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_8579__boxed_3116_, v_as_3112_, v_i_boxed_3117_, v_stop_boxed_3118_, v_b_3115_);
lean_dec_ref(v_as_3112_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7___boxed(lean_object* v___x_3120_, lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
uint8_t v___x_8586__boxed_3123_; lean_object* v_res_3124_; 
v___x_8586__boxed_3123_ = lean_unbox(v___x_3120_);
v_res_3124_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_8586__boxed_3123_, v_x_3121_, v_x_3122_);
lean_dec_ref(v_x_3121_);
return v_res_3124_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(uint8_t v___x_3126_, lean_object* v_x_3127_, size_t v_x_3128_, size_t v_x_3129_, lean_object* v_x_3130_){
_start:
{
if (lean_obj_tag(v_x_3127_) == 0)
{
lean_object* v_cs_3131_; lean_object* v___x_3132_; size_t v___x_3133_; lean_object* v_j_3134_; lean_object* v___x_3135_; size_t v___x_3136_; size_t v___x_3137_; size_t v___x_3138_; size_t v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v_cs_3131_ = lean_ctor_get(v_x_3127_, 0);
v___x_3132_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0);
v___x_3133_ = lean_usize_shift_right(v_x_3128_, v_x_3129_);
v_j_3134_ = lean_usize_to_nat(v___x_3133_);
v___x_3135_ = lean_array_get_borrowed(v___x_3132_, v_cs_3131_, v_j_3134_);
v___x_3136_ = ((size_t)1ULL);
v___x_3137_ = lean_usize_shift_left(v___x_3136_, v_x_3129_);
v___x_3138_ = lean_usize_sub(v___x_3137_, v___x_3136_);
v___x_3139_ = lean_usize_land(v_x_3128_, v___x_3138_);
v___x_3140_ = ((size_t)5ULL);
v___x_3141_ = lean_usize_sub(v_x_3129_, v___x_3140_);
v___x_3142_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3126_, v___x_3135_, v___x_3139_, v___x_3141_, v_x_3130_);
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = lean_nat_add(v_j_3134_, v___x_3143_);
lean_dec(v_j_3134_);
v___x_3145_ = lean_array_get_size(v_cs_3131_);
v___x_3146_ = lean_nat_dec_lt(v___x_3144_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_dec(v___x_3144_);
return v___x_3142_;
}
else
{
size_t v___x_3147_; size_t v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = lean_usize_of_nat(v___x_3144_);
lean_dec(v___x_3144_);
v___x_3148_ = lean_usize_of_nat(v___x_3145_);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3126_, v_cs_3131_, v___x_3147_, v___x_3148_, v___x_3142_);
return v___x_3149_;
}
}
else
{
lean_object* v_vs_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_vs_3150_ = lean_ctor_get(v_x_3127_, 0);
v___x_3151_ = lean_usize_to_nat(v_x_3128_);
v___x_3152_ = lean_array_get_size(v_vs_3150_);
v___x_3153_ = lean_nat_dec_lt(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v___x_3151_);
return v_x_3130_;
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = lean_usize_of_nat(v___x_3151_);
lean_dec(v___x_3151_);
v___x_3155_ = lean_usize_of_nat(v___x_3152_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3126_, v_vs_3150_, v___x_3154_, v___x_3155_, v_x_3130_);
return v___x_3156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___boxed(lean_object* v___x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_x_3160_, lean_object* v_x_3161_){
_start:
{
uint8_t v___x_8633__boxed_3162_; size_t v_x_8635__boxed_3163_; size_t v_x_8636__boxed_3164_; lean_object* v_res_3165_; 
v___x_8633__boxed_3162_ = lean_unbox(v___x_3157_);
v_x_8635__boxed_3163_ = lean_unbox_usize(v_x_3159_);
lean_dec(v_x_3159_);
v_x_8636__boxed_3164_ = lean_unbox_usize(v_x_3160_);
lean_dec(v_x_3160_);
v_res_3165_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_8633__boxed_3162_, v_x_3158_, v_x_8635__boxed_3163_, v_x_8636__boxed_3164_, v_x_3161_);
lean_dec_ref(v_x_3158_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(uint8_t v___x_3166_, lean_object* v_t_3167_, lean_object* v_init_3168_, lean_object* v_start_3169_){
_start:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = lean_nat_dec_eq(v_start_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v_root_3172_; lean_object* v_tail_3173_; size_t v_shift_3174_; lean_object* v_tailOff_3175_; uint8_t v___x_3176_; 
v_root_3172_ = lean_ctor_get(v_t_3167_, 0);
v_tail_3173_ = lean_ctor_get(v_t_3167_, 1);
v_shift_3174_ = lean_ctor_get_usize(v_t_3167_, 4);
v_tailOff_3175_ = lean_ctor_get(v_t_3167_, 3);
v___x_3176_ = lean_nat_dec_le(v_tailOff_3175_, v_start_3169_);
if (v___x_3176_ == 0)
{
size_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3177_ = lean_usize_of_nat(v_start_3169_);
v___x_3178_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3166_, v_root_3172_, v___x_3177_, v_shift_3174_, v_init_3168_);
v___x_3179_ = lean_array_get_size(v_tail_3173_);
v___x_3180_ = lean_nat_dec_lt(v___x_3170_, v___x_3179_);
if (v___x_3180_ == 0)
{
return v___x_3178_;
}
else
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = lean_usize_of_nat(v___x_3179_);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3166_, v_tail_3173_, v___x_3181_, v___x_3182_, v___x_3178_);
return v___x_3183_;
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3184_ = lean_nat_sub(v_start_3169_, v_tailOff_3175_);
v___x_3185_ = lean_array_get_size(v_tail_3173_);
v___x_3186_ = lean_nat_dec_lt(v___x_3184_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_dec(v___x_3184_);
return v_init_3168_;
}
else
{
size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_usize_of_nat(v___x_3184_);
lean_dec(v___x_3184_);
v___x_3188_ = lean_usize_of_nat(v___x_3185_);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3166_, v_tail_3173_, v___x_3187_, v___x_3188_, v_init_3168_);
return v___x_3189_;
}
}
}
else
{
lean_object* v_root_3190_; lean_object* v_tail_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_root_3190_ = lean_ctor_get(v_t_3167_, 0);
v_tail_3191_ = lean_ctor_get(v_t_3167_, 1);
v___x_3192_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3166_, v_root_3190_, v_init_3168_);
v___x_3193_ = lean_array_get_size(v_tail_3191_);
v___x_3194_ = lean_nat_dec_lt(v___x_3170_, v___x_3193_);
if (v___x_3194_ == 0)
{
return v___x_3192_;
}
else
{
size_t v___x_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = lean_usize_of_nat(v___x_3193_);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3166_, v_tail_3191_, v___x_3195_, v___x_3196_, v___x_3192_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3___boxed(lean_object* v___x_3198_, lean_object* v_t_3199_, lean_object* v_init_3200_, lean_object* v_start_3201_){
_start:
{
uint8_t v___x_8699__boxed_3202_; lean_object* v_res_3203_; 
v___x_8699__boxed_3202_ = lean_unbox(v___x_3198_);
v_res_3203_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_8699__boxed_3202_, v_t_3199_, v_init_3200_, v_start_3201_);
lean_dec(v_start_3201_);
lean_dec_ref(v_t_3199_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object* v_rest_3205_, uint8_t v___x_3206_, uint8_t v___y_3207_, lean_object* v_as_3208_, size_t v_sz_3209_, size_t v_i_3210_, lean_object* v_b_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_a_3216_; uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3210_, v_sz_3209_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_b_3211_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3222_ = lean_unsigned_to_nat(0u);
v_a_3223_ = lean_array_uget_borrowed(v_as_3208_, v_i_3210_);
v___x_3224_ = l_Lean_Syntax_getArg(v_a_3223_, v___x_3222_);
v___x_3225_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3224_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___y_3231_; lean_object* v___x_3238_; uint8_t v___y_3240_; uint8_t v___y_3255_; uint8_t v___x_3257_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_unsigned_to_nat(2u);
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3238_ = l_Lean_Syntax_getArg(v_a_3223_, v___x_3228_);
v___x_3257_ = l_Lean_Syntax_isNone(v___x_3224_);
lean_dec(v___x_3224_);
if (v___x_3257_ == 0)
{
v___y_3255_ = v___y_3207_;
goto v___jp_3254_;
}
else
{
v___y_3255_ = v___x_3206_;
goto v___jp_3254_;
}
v___jp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3232_ = l_Lean_Syntax_getArg(v_rest_3205_, v___x_3229_);
v___x_3233_ = l_Lean_Syntax_getArg(v___x_3232_, v___x_3222_);
lean_dec(v___x_3232_);
v___x_3234_ = lean_unsigned_to_nat(3u);
v___x_3235_ = l_Lean_Syntax_getArg(v_a_3223_, v___x_3234_);
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0));
v___x_3237_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___y_3231_, v___x_3233_, v___x_3235_, v___x_3236_, v___y_3212_, v___y_3213_);
lean_dec(v___x_3233_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_dec_ref_known(v___x_3237_, 1);
v_a_3216_ = v___x_3227_;
goto v___jp_3215_;
}
else
{
return v___x_3237_;
}
}
v___jp_3239_:
{
if (v___y_3240_ == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3238_, v___y_3212_, v___y_3213_);
lean_dec(v___x_3238_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
if (lean_obj_tag(v_a_3242_) == 1)
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_unbox(v_a_3226_);
lean_dec(v_a_3226_);
if (v___x_3243_ == 0)
{
lean_object* v_val_3244_; uint8_t v___x_3245_; 
v_val_3244_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_val_3244_);
lean_dec_ref_known(v_a_3242_, 1);
v___x_3245_ = lean_unbox(v_val_3244_);
lean_dec(v_val_3244_);
v___y_3231_ = v___x_3245_;
goto v___jp_3230_;
}
else
{
lean_dec_ref_known(v_a_3242_, 1);
v___y_3231_ = v___x_3220_;
goto v___jp_3230_;
}
}
else
{
lean_dec(v_a_3242_);
lean_dec(v_a_3226_);
v_a_3216_ = v___x_3227_;
goto v___jp_3215_;
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_a_3226_);
v_a_3246_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3241_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3241_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_dec(v___x_3238_);
lean_dec(v_a_3226_);
v_a_3216_ = v___x_3227_;
goto v___jp_3215_;
}
}
v___jp_3254_:
{
if (v___y_3255_ == 0)
{
v___y_3240_ = v___x_3206_;
goto v___jp_3239_;
}
else
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_unbox(v_a_3226_);
if (v___x_3256_ == 0)
{
lean_dec(v___x_3238_);
lean_dec(v_a_3226_);
v_a_3216_ = v___x_3227_;
goto v___jp_3215_;
}
else
{
v___y_3240_ = v___x_3206_;
goto v___jp_3239_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v___x_3224_);
v_a_3258_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3225_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3225_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
v___jp_3215_:
{
size_t v___x_3217_; size_t v___x_3218_; 
v___x_3217_ = ((size_t)1ULL);
v___x_3218_ = lean_usize_add(v_i_3210_, v___x_3217_);
v_i_3210_ = v___x_3218_;
v_b_3211_ = v_a_3216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object* v_rest_3266_, lean_object* v___x_3267_, lean_object* v___y_3268_, lean_object* v_as_3269_, lean_object* v_sz_3270_, lean_object* v_i_3271_, lean_object* v_b_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v___x_8748__boxed_3276_; uint8_t v___y_8749__boxed_3277_; size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v___x_8748__boxed_3276_ = lean_unbox(v___x_3267_);
v___y_8749__boxed_3277_ = lean_unbox(v___y_3268_);
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3270_);
lean_dec(v_sz_3270_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3271_);
lean_dec(v_i_3271_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3266_, v___x_8748__boxed_3276_, v___y_8749__boxed_3277_, v_as_3269_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v_as_3269_);
lean_dec(v_rest_3266_);
return v_res_3280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(lean_object* v_m_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_buckets_3283_; lean_object* v___x_3284_; uint64_t v___x_3285_; uint64_t v___x_3286_; uint64_t v___x_3287_; uint64_t v_fold_3288_; uint64_t v___x_3289_; uint64_t v___x_3290_; uint64_t v___x_3291_; size_t v___x_3292_; size_t v___x_3293_; size_t v___x_3294_; size_t v___x_3295_; size_t v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v_buckets_3283_ = lean_ctor_get(v_m_3281_, 1);
v___x_3284_ = lean_array_get_size(v_buckets_3283_);
v___x_3285_ = l_String_instHashableRaw_hash(v_a_3282_);
v___x_3286_ = 32ULL;
v___x_3287_ = lean_uint64_shift_right(v___x_3285_, v___x_3286_);
v_fold_3288_ = lean_uint64_xor(v___x_3285_, v___x_3287_);
v___x_3289_ = 16ULL;
v___x_3290_ = lean_uint64_shift_right(v_fold_3288_, v___x_3289_);
v___x_3291_ = lean_uint64_xor(v_fold_3288_, v___x_3290_);
v___x_3292_ = lean_uint64_to_usize(v___x_3291_);
v___x_3293_ = lean_usize_of_nat(v___x_3284_);
v___x_3294_ = ((size_t)1ULL);
v___x_3295_ = lean_usize_sub(v___x_3293_, v___x_3294_);
v___x_3296_ = lean_usize_land(v___x_3292_, v___x_3295_);
v___x_3297_ = lean_array_uget_borrowed(v_buckets_3283_, v___x_3296_);
v___x_3298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3282_, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg___boxed(lean_object* v_m_3299_, lean_object* v_a_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_m_3299_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(uint8_t v_val_3304_, lean_object* v___x_3305_, uint8_t v___x_3306_, lean_object* v___x_3307_, lean_object* v_as_3308_, size_t v_sz_3309_, size_t v_i_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_a_3316_; uint8_t v___x_3320_; 
v___x_3320_ = lean_usize_dec_lt(v_i_3310_, v_sz_3309_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
v___x_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_b_3311_);
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; lean_object* v_a_3323_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___x_3329_; 
v___x_3322_ = lean_box(0);
v_a_3323_ = lean_array_uget_borrowed(v_as_3308_, v_i_3310_);
v___x_3329_ = l_Lean_Syntax_getRange_x3f(v_a_3323_, v___x_3306_);
if (lean_obj_tag(v___x_3329_) == 1)
{
lean_object* v_val_3330_; lean_object* v_start_3331_; uint8_t v___x_3332_; 
v_val_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_start_3331_ = lean_ctor_get(v_val_3330_, 0);
lean_inc(v_start_3331_);
lean_dec(v_val_3330_);
v___x_3332_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3307_, v_start_3331_);
lean_dec(v_start_3331_);
if (v___x_3332_ == 0)
{
v___y_3325_ = v___y_3312_;
v___y_3326_ = v___y_3313_;
goto v___jp_3324_;
}
else
{
v_a_3316_ = v___x_3322_;
goto v___jp_3315_;
}
}
else
{
lean_dec(v___x_3329_);
v___y_3325_ = v___y_3312_;
v___y_3326_ = v___y_3313_;
goto v___jp_3324_;
}
v___jp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3323_);
v___x_3328_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3304_, v___x_3305_, v_a_3323_, v___x_3327_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_dec_ref_known(v___x_3328_, 1);
v_a_3316_ = v___x_3322_;
goto v___jp_3315_;
}
else
{
return v___x_3328_;
}
}
}
v___jp_3315_:
{
size_t v___x_3317_; size_t v___x_3318_; 
v___x_3317_ = ((size_t)1ULL);
v___x_3318_ = lean_usize_add(v_i_3310_, v___x_3317_);
v_i_3310_ = v___x_3318_;
v_b_3311_ = v_a_3316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___boxed(lean_object* v_val_3333_, lean_object* v___x_3334_, lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_as_3337_, lean_object* v_sz_3338_, lean_object* v_i_3339_, lean_object* v_b_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
uint8_t v_val_8899__boxed_3344_; uint8_t v___x_8901__boxed_3345_; size_t v_sz_boxed_3346_; size_t v_i_boxed_3347_; lean_object* v_res_3348_; 
v_val_8899__boxed_3344_ = lean_unbox(v_val_3333_);
v___x_8901__boxed_3345_ = lean_unbox(v___x_3335_);
v_sz_boxed_3346_ = lean_unbox_usize(v_sz_3338_);
lean_dec(v_sz_3338_);
v_i_boxed_3347_ = lean_unbox_usize(v_i_3339_);
lean_dec(v_i_3339_);
v_res_3348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_8899__boxed_3344_, v___x_3334_, v___x_8901__boxed_3345_, v___x_3336_, v_as_3337_, v_sz_boxed_3346_, v_i_boxed_3347_, v_b_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v_as_3337_);
lean_dec_ref(v___x_3336_);
lean_dec(v___x_3334_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(lean_object* v___x_3349_, uint8_t v___x_3350_, lean_object* v___x_3351_, uint8_t v_val_3352_, lean_object* v_as_3353_, size_t v_sz_3354_, size_t v_i_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_a_3361_; uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3355_, v_sz_3354_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3356_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v_a_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___x_3374_; 
v___x_3367_ = lean_box(0);
v_a_3368_ = lean_array_uget_borrowed(v_as_3353_, v_i_3355_);
v___x_3374_ = l_Lean_Syntax_getRange_x3f(v_a_3368_, v___x_3350_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; lean_object* v_start_3376_; uint8_t v___x_3377_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v_start_3376_ = lean_ctor_get(v_val_3375_, 0);
lean_inc(v_start_3376_);
lean_dec(v_val_3375_);
v___x_3377_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3351_, v_start_3376_);
lean_dec(v_start_3376_);
if (v___x_3377_ == 0)
{
v___y_3370_ = v___y_3357_;
v___y_3371_ = v___y_3358_;
goto v___jp_3369_;
}
else
{
v_a_3361_ = v___x_3367_;
goto v___jp_3360_;
}
}
else
{
lean_dec(v___x_3374_);
v___y_3370_ = v___y_3357_;
v___y_3371_ = v___y_3358_;
goto v___jp_3369_;
}
v___jp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3368_);
v___x_3373_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3352_, v___x_3349_, v_a_3368_, v___x_3372_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_dec_ref_known(v___x_3373_, 1);
v_a_3361_ = v___x_3367_;
goto v___jp_3360_;
}
else
{
return v___x_3373_;
}
}
}
v___jp_3360_:
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = ((size_t)1ULL);
v___x_3363_ = lean_usize_add(v_i_3355_, v___x_3362_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_3352_, v___x_3349_, v___x_3350_, v___x_3351_, v_as_3353_, v_sz_3354_, v___x_3363_, v_a_3361_, v___y_3357_, v___y_3358_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5___boxed(lean_object* v___x_3378_, lean_object* v___x_3379_, lean_object* v___x_3380_, lean_object* v_val_3381_, lean_object* v_as_3382_, lean_object* v_sz_3383_, lean_object* v_i_3384_, lean_object* v_b_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v___x_8957__boxed_3389_; uint8_t v_val_8959__boxed_3390_; size_t v_sz_boxed_3391_; size_t v_i_boxed_3392_; lean_object* v_res_3393_; 
v___x_8957__boxed_3389_ = lean_unbox(v___x_3379_);
v_val_8959__boxed_3390_ = lean_unbox(v_val_3381_);
v_sz_boxed_3391_ = lean_unbox_usize(v_sz_3383_);
lean_dec(v_sz_3383_);
v_i_boxed_3392_ = lean_unbox_usize(v_i_3384_);
lean_dec(v_i_3384_);
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3378_, v___x_8957__boxed_3389_, v___x_3380_, v_val_8959__boxed_3390_, v_as_3382_, v_sz_boxed_3391_, v_i_boxed_3392_, v_b_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v_as_3382_);
lean_dec_ref(v___x_3380_);
lean_dec(v___x_3378_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(lean_object* v___x_3400_, uint8_t v___x_3401_, lean_object* v___x_3402_, lean_object* v_as_3403_, size_t v_sz_3404_, size_t v_i_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v_a_3411_; uint8_t v___x_3415_; 
v___x_3415_ = lean_usize_dec_lt(v_i_3405_, v_sz_3404_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_b_3406_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3417_ = lean_unsigned_to_nat(0u);
v_a_3418_ = lean_array_uget_borrowed(v_as_3403_, v_i_3405_);
v___x_3419_ = l_Lean_Syntax_getArg(v_a_3418_, v___x_3417_);
v___x_3420_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3419_, v___y_3407_, v___y_3408_);
lean_dec(v___x_3419_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = lean_box(0);
if (lean_obj_tag(v_a_3421_) == 1)
{
lean_object* v_val_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_val_3423_ = lean_ctor_get(v_a_3421_, 0);
lean_inc(v_val_3423_);
lean_dec_ref_known(v_a_3421_, 1);
lean_inc(v_a_3418_);
v___x_3424_ = l_Lean_Syntax_getKind(v_a_3418_);
v___x_3425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3426_ = lean_name_eq(v___x_3424_, v___x_3425_);
lean_dec(v___x_3424_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; size_t v_sz_3430_; size_t v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3427_ = lean_unsigned_to_nat(2u);
v___x_3428_ = l_Lean_Syntax_getArg(v_a_3418_, v___x_3427_);
v___x_3429_ = l_Lean_Syntax_getArgs(v___x_3428_);
lean_dec(v___x_3428_);
v_sz_3430_ = lean_array_size(v___x_3429_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = lean_unbox(v_val_3423_);
lean_dec(v_val_3423_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3400_, v___x_3401_, v___x_3402_, v___x_3432_, v___x_3429_, v_sz_3430_, v___x_3431_, v___x_3422_, v___y_3407_, v___y_3408_);
lean_dec_ref(v___x_3429_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_dec_ref_known(v___x_3433_, 1);
v_a_3411_ = v___x_3422_;
goto v___jp_3410_;
}
else
{
return v___x_3433_;
}
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___x_3442_; 
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = l_Lean_Syntax_getArg(v_a_3418_, v___x_3434_);
v___x_3442_ = l_Lean_Syntax_getRange_x3f(v___x_3435_, v___x_3401_);
if (lean_obj_tag(v___x_3442_) == 1)
{
lean_object* v_val_3443_; lean_object* v_start_3444_; uint8_t v___x_3445_; 
v_val_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v_start_3444_ = lean_ctor_get(v_val_3443_, 0);
lean_inc(v_start_3444_);
lean_dec(v_val_3443_);
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3402_, v_start_3444_);
lean_dec(v_start_3444_);
if (v___x_3445_ == 0)
{
v___y_3437_ = v___y_3407_;
v___y_3438_ = v___y_3408_;
goto v___jp_3436_;
}
else
{
lean_dec(v___x_3435_);
lean_dec(v_val_3423_);
v_a_3411_ = v___x_3422_;
goto v___jp_3410_;
}
}
else
{
lean_dec(v___x_3442_);
v___y_3437_ = v___y_3407_;
v___y_3438_ = v___y_3408_;
goto v___jp_3436_;
}
v___jp_3436_:
{
lean_object* v___x_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3440_ = lean_unbox(v_val_3423_);
lean_dec(v_val_3423_);
v___x_3441_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3440_, v___x_3400_, v___x_3435_, v___x_3439_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_dec_ref_known(v___x_3441_, 1);
v_a_3411_ = v___x_3422_;
goto v___jp_3410_;
}
else
{
return v___x_3441_;
}
}
}
}
else
{
lean_dec(v_a_3421_);
v_a_3411_ = v___x_3422_;
goto v___jp_3410_;
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3420_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3420_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
v___jp_3410_:
{
size_t v___x_3412_; size_t v___x_3413_; 
v___x_3412_ = ((size_t)1ULL);
v___x_3413_ = lean_usize_add(v_i_3405_, v___x_3412_);
v_i_3405_ = v___x_3413_;
v_b_3406_ = v_a_3411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___boxed(lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v_as_3457_, lean_object* v_sz_3458_, lean_object* v_i_3459_, lean_object* v_b_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
uint8_t v___x_9028__boxed_3464_; size_t v_sz_boxed_3465_; size_t v_i_boxed_3466_; lean_object* v_res_3467_; 
v___x_9028__boxed_3464_ = lean_unbox(v___x_3455_);
v_sz_boxed_3465_ = lean_unbox_usize(v_sz_3458_);
lean_dec(v_sz_3458_);
v_i_boxed_3466_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_res_3467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3454_, v___x_9028__boxed_3464_, v___x_3456_, v_as_3457_, v_sz_boxed_3465_, v_i_boxed_3466_, v_b_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v_as_3457_);
lean_dec_ref(v___x_3456_);
lean_dec(v___x_3454_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(lean_object* v___x_3468_, uint8_t v___x_3469_, lean_object* v___x_3470_, lean_object* v_as_3471_, size_t v_sz_3472_, size_t v_i_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_a_3479_; uint8_t v___x_3483_; 
v___x_3483_ = lean_usize_dec_lt(v_i_3473_, v_sz_3472_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_b_3474_);
return v___x_3484_;
}
else
{
lean_object* v___x_3485_; lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v_a_3486_ = lean_array_uget_borrowed(v_as_3471_, v_i_3473_);
v___x_3487_ = l_Lean_Syntax_getArg(v_a_3486_, v___x_3485_);
v___x_3488_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3487_, v___y_3475_, v___y_3476_);
lean_dec(v___x_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = lean_box(0);
if (lean_obj_tag(v_a_3489_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_val_3491_ = lean_ctor_get(v_a_3489_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v_a_3489_, 1);
lean_inc(v_a_3486_);
v___x_3492_ = l_Lean_Syntax_getKind(v_a_3486_);
v___x_3493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3494_ = lean_name_eq(v___x_3492_, v___x_3493_);
lean_dec(v___x_3492_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; size_t v_sz_3498_; size_t v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3495_ = lean_unsigned_to_nat(2u);
v___x_3496_ = l_Lean_Syntax_getArg(v_a_3486_, v___x_3495_);
v___x_3497_ = l_Lean_Syntax_getArgs(v___x_3496_);
lean_dec(v___x_3496_);
v_sz_3498_ = lean_array_size(v___x_3497_);
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_unbox(v_val_3491_);
lean_dec(v_val_3491_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3468_, v___x_3469_, v___x_3470_, v___x_3500_, v___x_3497_, v_sz_3498_, v___x_3499_, v___x_3490_, v___y_3475_, v___y_3476_);
lean_dec_ref(v___x_3497_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec_ref_known(v___x_3501_, 1);
v_a_3479_ = v___x_3490_;
goto v___jp_3478_;
}
else
{
return v___x_3501_;
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___x_3510_; 
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = l_Lean_Syntax_getArg(v_a_3486_, v___x_3502_);
v___x_3510_ = l_Lean_Syntax_getRange_x3f(v___x_3503_, v___x_3469_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v_start_3512_; uint8_t v___x_3513_; 
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v_start_3512_ = lean_ctor_get(v_val_3511_, 0);
lean_inc(v_start_3512_);
lean_dec(v_val_3511_);
v___x_3513_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3470_, v_start_3512_);
lean_dec(v_start_3512_);
if (v___x_3513_ == 0)
{
v___y_3505_ = v___y_3475_;
v___y_3506_ = v___y_3476_;
goto v___jp_3504_;
}
else
{
lean_dec(v___x_3503_);
lean_dec(v_val_3491_);
v_a_3479_ = v___x_3490_;
goto v___jp_3478_;
}
}
else
{
lean_dec(v___x_3510_);
v___y_3505_ = v___y_3475_;
v___y_3506_ = v___y_3476_;
goto v___jp_3504_;
}
v___jp_3504_:
{
lean_object* v___x_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3508_ = lean_unbox(v_val_3491_);
lean_dec(v_val_3491_);
v___x_3509_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3508_, v___x_3468_, v___x_3503_, v___x_3507_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_dec_ref_known(v___x_3509_, 1);
v_a_3479_ = v___x_3490_;
goto v___jp_3478_;
}
else
{
return v___x_3509_;
}
}
}
}
else
{
lean_dec(v_a_3489_);
v_a_3479_ = v___x_3490_;
goto v___jp_3478_;
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
v_a_3514_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3488_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3488_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
v___jp_3478_:
{
size_t v___x_3480_; size_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((size_t)1ULL);
v___x_3481_ = lean_usize_add(v_i_3473_, v___x_3480_);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3468_, v___x_3469_, v___x_3470_, v_as_3471_, v_sz_3472_, v___x_3481_, v_a_3479_, v___y_3475_, v___y_3476_);
return v___x_3482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6___boxed(lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
uint8_t v___x_9148__boxed_3532_; size_t v_sz_boxed_3533_; size_t v_i_boxed_3534_; lean_object* v_res_3535_; 
v___x_9148__boxed_3532_ = lean_unbox(v___x_3523_);
v_sz_boxed_3533_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3534_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3522_, v___x_9148__boxed_3532_, v___x_3524_, v_as_3525_, v_sz_boxed_3533_, v_i_boxed_3534_, v_b_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
lean_dec_ref(v___x_3524_);
lean_dec(v___x_3522_);
return v_res_3535_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_unsigned_to_nat(16u);
v___x_3538_ = lean_mk_array(v___x_3537_, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__0, &l_Lean_Linter_MissingDocs_checkDecl___closed__0_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object* v_stx_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___x_3546_; lean_object* v_head_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3546_ = lean_unsigned_to_nat(0u);
v_head_3547_ = l_Lean_Syntax_getArg(v_stx_3542_, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(2u);
v___x_3549_ = l_Lean_Syntax_getArg(v_head_3547_, v___x_3548_);
v___x_3550_ = l_Lean_Syntax_getArg(v___x_3549_, v___x_3546_);
lean_dec(v___x_3549_);
v___x_3551_ = l_Lean_Syntax_getKind(v___x_3550_);
v___x_3552_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_3553_ = lean_name_eq(v___x_3551_, v___x_3552_);
lean_dec(v___x_3551_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_head_3547_, v_a_3543_, v_a_3544_);
lean_dec(v_head_3547_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3645_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3645_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3645_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v_rest_3560_; lean_object* v___y_3562_; lean_object* v___y_3563_; uint8_t v___y_3564_; uint8_t v___x_3596_; lean_object* v_k_3597_; lean_object* v___y_3599_; lean_object* v___y_3600_; 
v___x_3559_ = lean_unsigned_to_nat(1u);
v_rest_3560_ = l_Lean_Syntax_getArg(v_stx_3542_, v___x_3559_);
v___x_3596_ = 1;
lean_inc(v_rest_3560_);
v_k_3597_ = l_Lean_Syntax_getKind(v_rest_3560_);
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_val_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; 
v_val_3640_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_val_3640_);
lean_dec_ref_known(v_a_3555_, 1);
v___x_3641_ = l_Lean_Syntax_getArg(v_rest_3560_, v___x_3559_);
v___x_3642_ = l_Lean_Syntax_getArg(v___x_3641_, v___x_3546_);
lean_dec(v___x_3641_);
v___x_3643_ = lean_unbox(v_val_3640_);
lean_dec(v_val_3640_);
v___x_3644_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_3597_, v___x_3642_, v___x_3643_, v_a_3543_, v_a_3544_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_dec_ref_known(v___x_3644_, 1);
v___y_3599_ = v_a_3543_;
v___y_3600_ = v_a_3544_;
goto v___jp_3598_;
}
else
{
lean_dec(v_k_3597_);
lean_dec(v_rest_3560_);
lean_del_object(v___x_3557_);
return v___x_3644_;
}
}
else
{
lean_dec(v_a_3555_);
v___y_3599_ = v_a_3543_;
v___y_3600_ = v_a_3544_;
goto v___jp_3598_;
}
v___jp_3561_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; size_t v_sz_3569_; size_t v___x_3570_; lean_object* v___x_3571_; 
v___x_3565_ = lean_unsigned_to_nat(4u);
v___x_3566_ = l_Lean_Syntax_getArg(v_rest_3560_, v___x_3565_);
v___x_3567_ = l_Lean_Syntax_getArgs(v___x_3566_);
lean_dec(v___x_3566_);
v___x_3568_ = lean_box(0);
v_sz_3569_ = lean_array_size(v___x_3567_);
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3560_, v___x_3553_, v___y_3564_, v___x_3567_, v_sz_3569_, v___x_3570_, v___x_3568_, v___y_3562_, v___y_3563_);
lean_dec_ref(v___x_3567_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3594_; 
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v___x_3571_, 0);
lean_dec(v_unused_3595_);
v___x_3573_ = v___x_3571_;
v_isShared_3574_ = v_isSharedCheck_3594_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v___x_3571_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3594_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3575_ = lean_unsigned_to_nat(5u);
v___x_3576_ = l_Lean_Syntax_getArg(v_rest_3560_, v___x_3575_);
v___x_3577_ = l_Lean_Syntax_isNone(v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; size_t v_sz_3581_; lean_object* v___x_3582_; 
lean_del_object(v___x_3573_);
v___x_3578_ = l_Lean_Syntax_getArg(v___x_3576_, v___x_3546_);
lean_dec(v___x_3576_);
v___x_3579_ = l_Lean_Syntax_getArg(v___x_3578_, v___x_3559_);
lean_dec(v___x_3578_);
v___x_3580_ = l_Lean_Syntax_getArgs(v___x_3579_);
lean_dec(v___x_3579_);
v_sz_3581_ = lean_array_size(v___x_3580_);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_3560_, v___x_3580_, v_sz_3581_, v___x_3570_, v___x_3568_, v___y_3562_, v___y_3563_);
lean_dec_ref(v___x_3580_);
lean_dec(v_rest_3560_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v___x_3582_, 0);
lean_dec(v_unused_3590_);
v___x_3584_ = v___x_3582_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v___x_3582_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3568_);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3568_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
else
{
return v___x_3582_;
}
}
else
{
lean_object* v___x_3592_; 
lean_dec(v___x_3576_);
lean_dec(v_rest_3560_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3568_);
v___x_3592_ = v___x_3573_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3568_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_dec(v_rest_3560_);
return v___x_3571_;
}
}
v___jp_3598_:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_3602_ = lean_name_eq(v_k_3597_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_3604_ = lean_name_eq(v_k_3597_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_3606_ = lean_name_eq(v_k_3597_, v___x_3605_);
lean_dec(v_k_3597_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_dec(v_rest_3560_);
v___x_3607_ = lean_box(0);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3607_);
v___x_3609_ = v___x_3557_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3611_ = lean_unsigned_to_nat(4u);
v___x_3612_ = l_Lean_Syntax_getArg(v_rest_3560_, v___x_3611_);
v___x_3613_ = l_Lean_Syntax_getArg(v___x_3612_, v___x_3548_);
lean_dec(v___x_3612_);
v___x_3614_ = l_Lean_Syntax_isNone(v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v_infoState_3616_; lean_object* v_trees_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; size_t v_sz_3625_; size_t v___x_3626_; lean_object* v___x_3627_; 
lean_del_object(v___x_3557_);
v___x_3615_ = lean_st_ref_get(v___y_3600_);
v_infoState_3616_ = lean_ctor_get(v___x_3615_, 8);
lean_inc_ref(v_infoState_3616_);
lean_dec(v___x_3615_);
v_trees_3617_ = lean_ctor_get(v_infoState_3616_, 2);
lean_inc_ref(v_trees_3617_);
lean_dec_ref(v_infoState_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__1, &l_Lean_Linter_MissingDocs_checkDecl___closed__1_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1);
v___x_3619_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_3614_, v_trees_3617_, v___x_3618_, v___x_3546_);
lean_dec_ref(v_trees_3617_);
v___x_3620_ = l_Lean_Syntax_getArg(v_rest_3560_, v___x_3559_);
lean_dec(v_rest_3560_);
v___x_3621_ = l_Lean_Syntax_getArg(v___x_3620_, v___x_3546_);
lean_dec(v___x_3620_);
v___x_3622_ = l_Lean_Syntax_getArg(v___x_3613_, v___x_3546_);
lean_dec(v___x_3613_);
v___x_3623_ = l_Lean_Syntax_getArgs(v___x_3622_);
lean_dec(v___x_3622_);
v___x_3624_ = lean_box(0);
v_sz_3625_ = lean_array_size(v___x_3623_);
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3621_, v___x_3614_, v___x_3619_, v___x_3623_, v_sz_3625_, v___x_3626_, v___x_3624_, v___y_3599_, v___y_3600_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3619_);
lean_dec(v___x_3621_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v___x_3627_, 0);
lean_dec(v_unused_3635_);
v___x_3629_ = v___x_3627_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_dec(v___x_3627_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3624_);
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3624_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
else
{
return v___x_3627_;
}
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_dec(v___x_3613_);
lean_dec(v_rest_3560_);
v___x_3636_ = lean_box(0);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3636_);
v___x_3638_ = v___x_3557_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_dec(v_k_3597_);
lean_del_object(v___x_3557_);
v___y_3562_ = v___y_3599_;
v___y_3563_ = v___y_3600_;
v___y_3564_ = v___x_3604_;
goto v___jp_3561_;
}
}
else
{
lean_dec(v_k_3597_);
lean_del_object(v___x_3557_);
v___y_3562_ = v___y_3599_;
v___y_3563_ = v___y_3600_;
v___y_3564_ = v___x_3596_;
goto v___jp_3561_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
v_a_3646_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3554_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3554_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_head_3547_);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object* v_stx_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_Linter_MissingDocs_checkDecl(v_stx_3656_, v_a_3657_, v_a_3658_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_stx_3656_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2(lean_object* v_00_u03b2_3661_, lean_object* v_m_3662_, lean_object* v_a_3663_, lean_object* v_b_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_m_3662_, v_a_3663_, v_b_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object* v_00_u03b2_3666_, lean_object* v_m_3667_, lean_object* v_a_3668_){
_start:
{
uint8_t v___x_3669_; 
v___x_3669_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3667_, v_a_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object* v_00_u03b2_3670_, lean_object* v_m_3671_, lean_object* v_a_3672_){
_start:
{
uint8_t v_res_3673_; lean_object* v_r_3674_; 
v_res_3673_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(v_00_u03b2_3670_, v_m_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_m_3671_);
v_r_3674_ = lean_box(v_res_3673_);
return v_r_3674_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(lean_object* v_00_u03b2_3675_, lean_object* v_a_3676_, lean_object* v_x_3677_){
_start:
{
uint8_t v___x_3678_; 
v___x_3678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3676_, v_x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3679_, lean_object* v_a_3680_, lean_object* v_x_3681_){
_start:
{
uint8_t v_res_3682_; lean_object* v_r_3683_; 
v_res_3682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(v_00_u03b2_3679_, v_a_3680_, v_x_3681_);
lean_dec(v_x_3681_);
lean_dec(v_a_3680_);
v_r_3683_ = lean_box(v_res_3682_);
return v_r_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3(lean_object* v_00_u03b2_3684_, lean_object* v_data_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_data_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3687_, lean_object* v_i_3688_, lean_object* v_source_3689_, lean_object* v_target_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v_i_3688_, v_source_3689_, v_target_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_x_3693_, v_x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkDecl___boxed), 4, 0);
v___x_3703_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1));
v___x_3706_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2);
v___x_3707_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3705_, v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___boxed(lean_object* v_a_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object* v_stx_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = lean_unsigned_to_nat(2u);
v___x_3716_ = l_Lean_Syntax_getArg(v_stx_3711_, v___x_3715_);
v___x_3717_ = l_Lean_Syntax_isNone(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = l_Lean_Syntax_getArg(v_stx_3711_, v___x_3718_);
v___x_3720_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3719_, v_a_3712_, v_a_3713_);
lean_dec(v___x_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3734_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3734_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3734_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
if (lean_obj_tag(v_a_3721_) == 1)
{
lean_object* v_val_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; 
lean_del_object(v___x_3723_);
v_val_3725_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v_a_3721_, 1);
v___x_3726_ = l_Lean_Syntax_getArg(v___x_3716_, v___x_3718_);
lean_dec(v___x_3716_);
v___x_3727_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkInit___closed__0));
v___x_3728_ = lean_unbox(v_val_3725_);
lean_dec(v_val_3725_);
v___x_3729_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3728_, v___x_3726_, v___x_3727_, v_a_3712_, v_a_3713_);
return v___x_3729_;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3732_; 
lean_dec(v_a_3721_);
lean_dec(v___x_3716_);
v___x_3730_ = lean_box(0);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3730_);
v___x_3732_ = v___x_3723_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v___x_3716_);
v_a_3735_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3720_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3720_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec(v___x_3716_);
v___x_3743_ = lean_box(0);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object* v_stx_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Linter_MissingDocs_checkInit(v_stx_3745_, v_a_3746_, v_a_3747_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_stx_3745_);
return v_res_3749_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkInit___boxed), 4, 0);
v___x_3757_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3757_, 0, v___x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1));
v___x_3760_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2);
v___x_3761_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3759_, v___x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___boxed(lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object* v_stx_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3775_ = lean_unsigned_to_nat(2u);
v___x_3776_ = l_Lean_Syntax_getArg(v_stx_3771_, v___x_3775_);
v___x_3777_ = lean_unsigned_to_nat(0u);
v___x_3778_ = l_Lean_Syntax_getArg(v___x_3776_, v___x_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = l_Lean_Syntax_getArg(v___x_3778_, v___x_3777_);
lean_dec(v___x_3778_);
v___x_3780_ = l_Lean_Syntax_getKind(v___x_3779_);
v___x_3781_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3782_ = lean_name_eq(v___x_3780_, v___x_3781_);
lean_dec(v___x_3780_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3783_ = l_Lean_Syntax_getArg(v_stx_3771_, v___x_3777_);
v___x_3784_ = lean_unsigned_to_nat(1u);
v___x_3785_ = l_Lean_Syntax_getArg(v_stx_3771_, v___x_3784_);
v___x_3786_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3783_, v___x_3785_, v___x_3782_, v_a_3772_, v_a_3773_);
lean_dec(v___x_3785_);
lean_dec(v___x_3783_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3810_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3810_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3810_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_a_3787_) == 1)
{
lean_object* v_val_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
lean_del_object(v___x_3789_);
v_val_3791_ = lean_ctor_get(v_a_3787_, 0);
lean_inc(v_val_3791_);
lean_dec_ref_known(v_a_3787_, 1);
v___x_3792_ = lean_unsigned_to_nat(5u);
v___x_3793_ = l_Lean_Syntax_getArg(v_stx_3771_, v___x_3792_);
v___x_3794_ = l_Lean_Syntax_isNone(v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3795_ = l_Lean_Syntax_getArg(v___x_3793_, v___x_3777_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_unsigned_to_nat(3u);
v___x_3797_ = l_Lean_Syntax_getArg(v___x_3795_, v___x_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3799_ = lean_unbox(v_val_3791_);
lean_dec(v_val_3791_);
v___x_3800_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3799_, v___x_3797_, v___x_3798_, v_a_3772_, v_a_3773_);
return v___x_3800_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; lean_object* v___x_3805_; 
lean_dec(v___x_3793_);
v___x_3801_ = lean_unsigned_to_nat(3u);
v___x_3802_ = l_Lean_Syntax_getArg(v_stx_3771_, v___x_3801_);
v___x_3803_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3804_ = lean_unbox(v_val_3791_);
lean_dec(v_val_3791_);
v___x_3805_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3804_, v___x_3802_, v___x_3803_, v_a_3772_, v_a_3773_);
return v___x_3805_;
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3808_; 
lean_dec(v_a_3787_);
v___x_3806_ = lean_box(0);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3806_);
v___x_3808_ = v___x_3789_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3786_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3786_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_box(0);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
return v___x_3820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object* v_stx_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_Linter_MissingDocs_checkNotation(v_stx_3821_, v_a_3822_, v_a_3823_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec(v_stx_3821_);
return v_res_3825_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkNotation___boxed), 4, 0);
v___x_3832_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0));
v___x_3835_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1);
v___x_3836_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3834_, v___x_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___boxed(lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object* v_stx_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v___x_3843_ = lean_unsigned_to_nat(2u);
v___x_3844_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3843_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = l_Lean_Syntax_getArg(v___x_3846_, v___x_3845_);
lean_dec(v___x_3846_);
v___x_3848_ = l_Lean_Syntax_getKind(v___x_3847_);
v___x_3849_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3850_ = lean_name_eq(v___x_3848_, v___x_3849_);
lean_dec(v___x_3848_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3851_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3845_);
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3852_);
v___x_3854_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3851_, v___x_3853_, v___x_3850_, v_a_3840_, v_a_3841_);
lean_dec(v___x_3853_);
lean_dec(v___x_3851_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3881_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3881_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3881_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
if (lean_obj_tag(v_a_3855_) == 1)
{
lean_object* v_val_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
lean_del_object(v___x_3857_);
v_val_3859_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_val_3859_);
lean_dec_ref_known(v_a_3855_, 1);
v___x_3860_ = lean_unsigned_to_nat(5u);
v___x_3861_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3860_);
v___x_3862_ = l_Lean_Syntax_isNone(v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3863_ = l_Lean_Syntax_getArg(v___x_3861_, v___x_3845_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_unsigned_to_nat(3u);
v___x_3865_ = l_Lean_Syntax_getArg(v___x_3863_, v___x_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3864_);
v___x_3867_ = l_Lean_Syntax_getArg(v___x_3866_, v___x_3845_);
lean_dec(v___x_3866_);
v___x_3868_ = l_Lean_Syntax_getAtomVal(v___x_3867_);
lean_dec(v___x_3867_);
v___x_3869_ = lean_unbox(v_val_3859_);
lean_dec(v_val_3859_);
v___x_3870_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3869_, v___x_3865_, v___x_3868_, v_a_3840_, v_a_3841_);
return v___x_3870_;
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v___x_3861_);
v___x_3871_ = lean_unsigned_to_nat(3u);
v___x_3872_ = l_Lean_Syntax_getArg(v_stx_3839_, v___x_3871_);
v___x_3873_ = l_Lean_Syntax_getArg(v___x_3872_, v___x_3845_);
v___x_3874_ = l_Lean_Syntax_getAtomVal(v___x_3873_);
lean_dec(v___x_3873_);
v___x_3875_ = lean_unbox(v_val_3859_);
lean_dec(v_val_3859_);
v___x_3876_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3875_, v___x_3872_, v___x_3874_, v_a_3840_, v_a_3841_);
return v___x_3876_;
}
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_dec(v_a_3855_);
v___x_3877_ = lean_box(0);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3877_);
v___x_3879_ = v___x_3857_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3854_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3854_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_box(0);
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
return v___x_3891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object* v_stx_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Linter_MissingDocs_checkMixfix(v_stx_3892_, v_a_3893_, v_a_3894_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_stx_3892_);
return v_res_3896_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMixfix___boxed), 4, 0);
v___x_3904_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3906_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1));
v___x_3907_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2);
v___x_3908_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3906_, v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___boxed(lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object* v_stx_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3916_ = lean_unsigned_to_nat(2u);
v___x_3917_ = l_Lean_Syntax_getArg(v_stx_3912_, v___x_3916_);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = l_Lean_Syntax_getArg(v___x_3917_, v___x_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = l_Lean_Syntax_getArg(v___x_3919_, v___x_3918_);
lean_dec(v___x_3919_);
v___x_3921_ = l_Lean_Syntax_getKind(v___x_3920_);
v___x_3922_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3923_ = lean_name_eq(v___x_3921_, v___x_3922_);
lean_dec(v___x_3921_);
if (v___x_3923_ == 0)
{
uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3924_ = 1;
v___x_3925_ = l_Lean_Syntax_getArg(v_stx_3912_, v___x_3918_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = l_Lean_Syntax_getArg(v_stx_3912_, v___x_3926_);
v___x_3928_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3925_, v___x_3927_, v___x_3924_, v_a_3913_, v_a_3914_);
lean_dec(v___x_3927_);
lean_dec(v___x_3925_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3952_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3952_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3952_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
if (lean_obj_tag(v_a_3929_) == 1)
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
lean_del_object(v___x_3931_);
v_val_3933_ = lean_ctor_get(v_a_3929_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v_a_3929_, 1);
v___x_3934_ = lean_unsigned_to_nat(5u);
v___x_3935_ = l_Lean_Syntax_getArg(v_stx_3912_, v___x_3934_);
v___x_3936_ = l_Lean_Syntax_isNone(v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; 
v___x_3937_ = l_Lean_Syntax_getArg(v___x_3935_, v___x_3918_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_unsigned_to_nat(3u);
v___x_3939_ = l_Lean_Syntax_getArg(v___x_3937_, v___x_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3941_ = lean_unbox(v_val_3933_);
lean_dec(v_val_3933_);
v___x_3942_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3941_, v___x_3939_, v___x_3940_, v_a_3913_, v_a_3914_);
return v___x_3942_;
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; lean_object* v___x_3947_; 
lean_dec(v___x_3935_);
v___x_3943_ = lean_unsigned_to_nat(3u);
v___x_3944_ = l_Lean_Syntax_getArg(v_stx_3912_, v___x_3943_);
v___x_3945_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3946_ = lean_unbox(v_val_3933_);
lean_dec(v_val_3933_);
v___x_3947_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3946_, v___x_3944_, v___x_3945_, v_a_3913_, v_a_3914_);
return v___x_3947_;
}
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3950_; 
lean_dec(v_a_3929_);
v___x_3948_ = lean_box(0);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3948_);
v___x_3950_ = v___x_3931_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
v_a_3953_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3928_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3928_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object* v_stx_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Linter_MissingDocs_checkSyntax(v_stx_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_stx_3963_);
return v_res_3967_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntax___boxed), 4, 0);
v___x_3974_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0));
v___x_3977_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1);
v___x_3978_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3976_, v___x_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___boxed(lean_object* v_a_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object* v_name_3981_, lean_object* v_declNameStxIdx_3982_, lean_object* v_stx_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = l_Lean_Syntax_getArg(v_stx_3983_, v___x_3987_);
v___x_3989_ = l_Lean_Linter_MissingDocs_isMissingDoc(v___x_3988_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4014_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3992_ = v___x_3989_;
v_isShared_3993_ = v_isSharedCheck_4014_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4014_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_unbox(v_a_3990_);
lean_dec(v_a_3990_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec(v___x_3988_);
lean_dec_ref(v_name_3981_);
v___x_3995_ = lean_box(0);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3995_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_object* v___x_3999_; 
lean_del_object(v___x_3992_);
v___x_3999_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3988_, v_a_3984_, v_a_3985_);
lean_dec(v___x_3988_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; uint8_t v___x_4001_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v___x_4001_ = lean_unbox(v_a_4000_);
lean_dec(v_a_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = l_Lean_Syntax_getArg(v_stx_3983_, v_declNameStxIdx_3982_);
v___x_4003_ = l_Lean_Linter_MissingDocs_lintNamed(v___x_4002_, v_name_3981_, v_a_3984_, v_a_3985_);
return v___x_4003_;
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = l_Lean_Syntax_getArg(v_stx_3983_, v_declNameStxIdx_3982_);
v___x_4005_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v___x_4004_, v_name_3981_, v_a_3984_, v_a_3985_);
return v___x_4005_;
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec_ref(v_name_3981_);
v_a_4006_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3999_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3999_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v___x_3988_);
lean_dec_ref(v_name_3981_);
v_a_4015_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3989_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3989_);
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
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object* v_name_4023_, lean_object* v_declNameStxIdx_4024_, lean_object* v_stx_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v_name_4023_, v_declNameStxIdx_4024_, v_stx_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_declNameStxIdx_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_4035_ = lean_unsigned_to_nat(2u);
v___x_4036_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4034_, v___x_4035_, v_a_4030_, v_a_4031_, v_a_4032_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(v_a_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
return v_res_4041_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed), 4, 0);
v___x_4049_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1));
v___x_4052_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2);
v___x_4053_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4051_, v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___boxed(lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0));
v___x_4062_ = lean_unsigned_to_nat(2u);
v___x_4063_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4061_, v___x_4062_, v_a_4057_, v_a_4058_, v_a_4059_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_Linter_MissingDocs_checkSyntaxCat(v_a_4064_, v_a_4065_, v_a_4066_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
return v_res_4068_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed), 4, 0);
v___x_4076_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1));
v___x_4079_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2);
v___x_4080_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4078_, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___boxed(lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object* v_stx_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4088_ = lean_unsigned_to_nat(2u);
v___x_4089_ = l_Lean_Syntax_getArg(v_stx_4084_, v___x_4088_);
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = l_Lean_Syntax_getArg(v___x_4089_, v___x_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = l_Lean_Syntax_getArg(v___x_4091_, v___x_4090_);
lean_dec(v___x_4091_);
v___x_4093_ = l_Lean_Syntax_getKind(v___x_4092_);
v___x_4094_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4095_ = lean_name_eq(v___x_4093_, v___x_4094_);
lean_dec(v___x_4093_);
if (v___x_4095_ == 0)
{
uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4096_ = 1;
v___x_4097_ = l_Lean_Syntax_getArg(v_stx_4084_, v___x_4090_);
v___x_4098_ = lean_unsigned_to_nat(1u);
v___x_4099_ = l_Lean_Syntax_getArg(v_stx_4084_, v___x_4098_);
v___x_4100_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4097_, v___x_4099_, v___x_4096_, v_a_4085_, v_a_4086_);
lean_dec(v___x_4099_);
lean_dec(v___x_4097_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4124_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4124_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4124_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
if (lean_obj_tag(v_a_4101_) == 1)
{
lean_object* v_val_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
lean_del_object(v___x_4103_);
v_val_4105_ = lean_ctor_get(v_a_4101_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v_a_4101_, 1);
v___x_4106_ = lean_unsigned_to_nat(5u);
v___x_4107_ = l_Lean_Syntax_getArg(v_stx_4084_, v___x_4106_);
v___x_4108_ = l_Lean_Syntax_isNone(v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; 
v___x_4109_ = l_Lean_Syntax_getArg(v___x_4107_, v___x_4090_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_unsigned_to_nat(3u);
v___x_4111_ = l_Lean_Syntax_getArg(v___x_4109_, v___x_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4113_ = lean_unbox(v_val_4105_);
lean_dec(v_val_4105_);
v___x_4114_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4113_, v___x_4111_, v___x_4112_, v_a_4085_, v_a_4086_);
return v___x_4114_;
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; lean_object* v___x_4119_; 
lean_dec(v___x_4107_);
v___x_4115_ = lean_unsigned_to_nat(3u);
v___x_4116_ = l_Lean_Syntax_getArg(v_stx_4084_, v___x_4115_);
v___x_4117_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4118_ = lean_unbox(v_val_4105_);
lean_dec(v_val_4105_);
v___x_4119_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4118_, v___x_4116_, v___x_4117_, v_a_4085_, v_a_4086_);
return v___x_4119_;
}
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
lean_dec(v_a_4101_);
v___x_4120_ = lean_box(0);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4120_);
v___x_4122_ = v___x_4103_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
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
v_a_4125_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4100_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4100_);
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
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object* v_stx_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Linter_MissingDocs_checkMacro(v_stx_4135_, v_a_4136_, v_a_4137_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_stx_4135_);
return v_res_4139_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMacro___boxed), 4, 0);
v___x_4146_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0));
v___x_4149_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1);
v___x_4150_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4148_, v___x_4149_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___boxed(lean_object* v_a_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object* v_stx_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4158_ = lean_unsigned_to_nat(2u);
v___x_4159_ = l_Lean_Syntax_getArg(v_stx_4154_, v___x_4158_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = l_Lean_Syntax_getArg(v___x_4159_, v___x_4160_);
lean_dec(v___x_4159_);
v___x_4162_ = l_Lean_Syntax_getArg(v___x_4161_, v___x_4160_);
lean_dec(v___x_4161_);
v___x_4163_ = l_Lean_Syntax_getKind(v___x_4162_);
v___x_4164_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4165_ = lean_name_eq(v___x_4163_, v___x_4164_);
lean_dec(v___x_4163_);
if (v___x_4165_ == 0)
{
uint8_t v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4166_ = 1;
v___x_4167_ = l_Lean_Syntax_getArg(v_stx_4154_, v___x_4160_);
v___x_4168_ = lean_unsigned_to_nat(1u);
v___x_4169_ = l_Lean_Syntax_getArg(v_stx_4154_, v___x_4168_);
v___x_4170_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4167_, v___x_4169_, v___x_4166_, v_a_4155_, v_a_4156_);
lean_dec(v___x_4169_);
lean_dec(v___x_4167_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4194_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4194_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4194_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
if (lean_obj_tag(v_a_4171_) == 1)
{
lean_object* v_val_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
lean_del_object(v___x_4173_);
v_val_4175_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_val_4175_);
lean_dec_ref_known(v_a_4171_, 1);
v___x_4176_ = lean_unsigned_to_nat(5u);
v___x_4177_ = l_Lean_Syntax_getArg(v_stx_4154_, v___x_4176_);
v___x_4178_ = l_Lean_Syntax_isNone(v___x_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; 
v___x_4179_ = l_Lean_Syntax_getArg(v___x_4177_, v___x_4160_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_unsigned_to_nat(3u);
v___x_4181_ = l_Lean_Syntax_getArg(v___x_4179_, v___x_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4183_ = lean_unbox(v_val_4175_);
lean_dec(v_val_4175_);
v___x_4184_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4183_, v___x_4181_, v___x_4182_, v_a_4155_, v_a_4156_);
return v___x_4184_;
}
else
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; lean_object* v___x_4189_; 
lean_dec(v___x_4177_);
v___x_4185_ = lean_unsigned_to_nat(3u);
v___x_4186_ = l_Lean_Syntax_getArg(v_stx_4154_, v___x_4185_);
v___x_4187_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4188_ = lean_unbox(v_val_4175_);
lean_dec(v_val_4175_);
v___x_4189_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4188_, v___x_4186_, v___x_4187_, v_a_4155_, v_a_4156_);
return v___x_4189_;
}
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
lean_dec(v_a_4171_);
v___x_4190_ = lean_box(0);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4190_);
v___x_4192_ = v___x_4173_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
v_a_4195_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4170_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4170_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_box(0);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object* v_stx_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_Linter_MissingDocs_checkElab(v_stx_4205_, v_a_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_stx_4205_);
return v_res_4209_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkElab___boxed), 4, 0);
v___x_4216_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0));
v___x_4219_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1);
v___x_4220_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4218_, v___x_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___boxed(lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object* v_stx_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = l_Lean_Syntax_getArg(v_stx_4224_, v___x_4228_);
v___x_4230_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4229_, v_a_4225_, v_a_4226_);
lean_dec(v___x_4229_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4245_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4233_ = v___x_4230_;
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
if (lean_obj_tag(v_a_4231_) == 1)
{
lean_object* v_val_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; 
lean_del_object(v___x_4233_);
v_val_4235_ = lean_ctor_get(v_a_4231_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v_a_4231_, 1);
v___x_4236_ = lean_unsigned_to_nat(3u);
v___x_4237_ = l_Lean_Syntax_getArg(v_stx_4224_, v___x_4236_);
v___x_4238_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0));
v___x_4239_ = lean_unbox(v_val_4235_);
lean_dec(v_val_4235_);
v___x_4240_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4239_, v___x_4237_, v___x_4238_, v_a_4225_, v_a_4226_);
return v___x_4240_;
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
lean_dec(v_a_4231_);
v___x_4241_ = lean_box(0);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4241_);
v___x_4243_ = v___x_4233_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4230_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4230_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object* v_stx_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_Linter_MissingDocs_checkClassAbbrev(v_stx_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_stx_4254_);
return v_res_4258_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed), 4, 0);
v___x_4266_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4266_, 0, v___x_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4268_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1));
v___x_4269_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2);
v___x_4270_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4268_, v___x_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___boxed(lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSimpLike___closed__0));
v___x_4279_ = lean_unsigned_to_nat(2u);
v___x_4280_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4278_, v___x_4279_, v_a_4274_, v_a_4275_, v_a_4276_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Linter_MissingDocs_checkSimpLike(v_a_4281_, v_a_4282_, v_a_4283_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
return v_res_4285_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSimpLike___boxed), 4, 0);
v___x_4294_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4294_, 0, v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2));
v___x_4297_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3);
v___x_4298_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4296_, v___x_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___boxed(lean_object* v_a_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4307_ = lean_unsigned_to_nat(3u);
v___x_4308_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4306_, v___x_4307_, v_a_4302_, v_a_4303_, v_a_4304_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(v_a_4309_, v_a_4310_, v_a_4311_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
return v_res_4313_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3(void){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed), 4, 0);
v___x_4321_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4323_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2));
v___x_4324_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3);
v___x_4325_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4323_, v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___boxed(lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object* v_stx_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = l_Lean_Syntax_getArg(v_stx_4328_, v___x_4332_);
v___x_4334_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4333_, v_a_4329_, v_a_4330_);
lean_dec(v___x_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4349_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4349_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4349_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
if (lean_obj_tag(v_a_4335_) == 1)
{
lean_object* v_val_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; lean_object* v___x_4344_; 
lean_del_object(v___x_4337_);
v_val_4339_ = lean_ctor_get(v_a_4335_, 0);
lean_inc(v_val_4339_);
lean_dec_ref_known(v_a_4335_, 1);
v___x_4340_ = lean_unsigned_to_nat(2u);
v___x_4341_ = l_Lean_Syntax_getArg(v_stx_4328_, v___x_4340_);
v___x_4342_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4343_ = lean_unbox(v_val_4339_);
lean_dec(v_val_4339_);
v___x_4344_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4343_, v___x_4341_, v___x_4342_, v_a_4329_, v_a_4330_);
return v___x_4344_;
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4347_; 
lean_dec(v_a_4335_);
v___x_4345_ = lean_box(0);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v___x_4345_);
v___x_4347_ = v___x_4337_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_a_4350_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4334_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4334_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object* v_stx_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Lean_Linter_MissingDocs_checkRegisterOption(v_stx_4358_, v_a_4359_, v_a_4360_);
lean_dec(v_a_4360_);
lean_dec_ref(v_a_4359_);
lean_dec(v_stx_4358_);
return v_res_4362_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterOption___boxed), 4, 0);
v___x_4369_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1));
v___x_4372_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2);
v___x_4373_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4371_, v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___boxed(lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4381_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0));
v___x_4382_ = lean_unsigned_to_nat(2u);
v___x_4383_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4381_, v___x_4382_, v_a_4377_, v_a_4378_, v_a_4379_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
return v_res_4388_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed), 4, 0);
v___x_4396_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1));
v___x_4399_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2);
v___x_4400_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4398_, v___x_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___boxed(lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(lean_object* v_t_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; lean_object* v_infoState_4407_; uint8_t v_enabled_4408_; 
v___x_4406_ = lean_st_ref_get(v___y_4404_);
v_infoState_4407_ = lean_ctor_get(v___x_4406_, 8);
lean_inc_ref(v_infoState_4407_);
lean_dec(v___x_4406_);
v_enabled_4408_ = lean_ctor_get_uint8(v_infoState_4407_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4407_);
if (v_enabled_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
lean_dec_ref(v_t_4403_);
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
return v___x_4410_;
}
else
{
lean_object* v___x_4411_; lean_object* v_infoState_4412_; lean_object* v_env_4413_; lean_object* v_messages_4414_; lean_object* v_scopes_4415_; lean_object* v_usedQuotCtxts_4416_; lean_object* v_nextMacroScope_4417_; lean_object* v_maxRecDepth_4418_; lean_object* v_ngen_4419_; lean_object* v_auxDeclNGen_4420_; lean_object* v_traceState_4421_; lean_object* v_snapshotTasks_4422_; lean_object* v_prevLinterStates_4423_; lean_object* v_codeQualityEntryTasks_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4446_; 
v___x_4411_ = lean_st_ref_take(v___y_4404_);
v_infoState_4412_ = lean_ctor_get(v___x_4411_, 8);
v_env_4413_ = lean_ctor_get(v___x_4411_, 0);
v_messages_4414_ = lean_ctor_get(v___x_4411_, 1);
v_scopes_4415_ = lean_ctor_get(v___x_4411_, 2);
v_usedQuotCtxts_4416_ = lean_ctor_get(v___x_4411_, 3);
v_nextMacroScope_4417_ = lean_ctor_get(v___x_4411_, 4);
v_maxRecDepth_4418_ = lean_ctor_get(v___x_4411_, 5);
v_ngen_4419_ = lean_ctor_get(v___x_4411_, 6);
v_auxDeclNGen_4420_ = lean_ctor_get(v___x_4411_, 7);
v_traceState_4421_ = lean_ctor_get(v___x_4411_, 9);
v_snapshotTasks_4422_ = lean_ctor_get(v___x_4411_, 10);
v_prevLinterStates_4423_ = lean_ctor_get(v___x_4411_, 11);
v_codeQualityEntryTasks_4424_ = lean_ctor_get(v___x_4411_, 12);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4426_ = v___x_4411_;
v_isShared_4427_ = v_isSharedCheck_4446_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4424_);
lean_inc(v_prevLinterStates_4423_);
lean_inc(v_snapshotTasks_4422_);
lean_inc(v_traceState_4421_);
lean_inc(v_infoState_4412_);
lean_inc(v_auxDeclNGen_4420_);
lean_inc(v_ngen_4419_);
lean_inc(v_maxRecDepth_4418_);
lean_inc(v_nextMacroScope_4417_);
lean_inc(v_usedQuotCtxts_4416_);
lean_inc(v_scopes_4415_);
lean_inc(v_messages_4414_);
lean_inc(v_env_4413_);
lean_dec(v___x_4411_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4446_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
uint8_t v_enabled_4428_; lean_object* v_assignment_4429_; lean_object* v_lazyAssignment_4430_; lean_object* v_trees_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4445_; 
v_enabled_4428_ = lean_ctor_get_uint8(v_infoState_4412_, sizeof(void*)*3);
v_assignment_4429_ = lean_ctor_get(v_infoState_4412_, 0);
v_lazyAssignment_4430_ = lean_ctor_get(v_infoState_4412_, 1);
v_trees_4431_ = lean_ctor_get(v_infoState_4412_, 2);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_infoState_4412_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4433_ = v_infoState_4412_;
v_isShared_4434_ = v_isSharedCheck_4445_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_trees_4431_);
lean_inc(v_lazyAssignment_4430_);
lean_inc(v_assignment_4429_);
lean_dec(v_infoState_4412_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4445_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = l_Lean_PersistentArray_push___redArg(v_trees_4431_, v_t_4403_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 2, v___x_4435_);
v___x_4437_ = v___x_4433_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_assignment_4429_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_lazyAssignment_4430_);
lean_ctor_set(v_reuseFailAlloc_4444_, 2, v___x_4435_);
lean_ctor_set_uint8(v_reuseFailAlloc_4444_, sizeof(void*)*3, v_enabled_4428_);
v___x_4437_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4439_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 8, v___x_4437_);
v___x_4439_ = v___x_4426_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_env_4413_);
lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_messages_4414_);
lean_ctor_set(v_reuseFailAlloc_4443_, 2, v_scopes_4415_);
lean_ctor_set(v_reuseFailAlloc_4443_, 3, v_usedQuotCtxts_4416_);
lean_ctor_set(v_reuseFailAlloc_4443_, 4, v_nextMacroScope_4417_);
lean_ctor_set(v_reuseFailAlloc_4443_, 5, v_maxRecDepth_4418_);
lean_ctor_set(v_reuseFailAlloc_4443_, 6, v_ngen_4419_);
lean_ctor_set(v_reuseFailAlloc_4443_, 7, v_auxDeclNGen_4420_);
lean_ctor_set(v_reuseFailAlloc_4443_, 8, v___x_4437_);
lean_ctor_set(v_reuseFailAlloc_4443_, 9, v_traceState_4421_);
lean_ctor_set(v_reuseFailAlloc_4443_, 10, v_snapshotTasks_4422_);
lean_ctor_set(v_reuseFailAlloc_4443_, 11, v_prevLinterStates_4423_);
lean_ctor_set(v_reuseFailAlloc_4443_, 12, v_codeQualityEntryTasks_4424_);
v___x_4439_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = lean_st_ref_put(v___y_4404_, v___x_4439_);
v___x_4441_ = lean_box(0);
v___x_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
return v___x_4442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_t_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_4447_, v___y_4448_);
lean_dec(v___y_4448_);
return v_res_4450_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = lean_unsigned_to_nat(32u);
v___x_4452_ = lean_mk_empty_array_with_capacity(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4454_ = ((size_t)5ULL);
v___x_4455_ = lean_unsigned_to_nat(0u);
v___x_4456_ = lean_unsigned_to_nat(32u);
v___x_4457_ = lean_mk_empty_array_with_capacity(v___x_4456_);
v___x_4458_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0);
v___x_4459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
lean_ctor_set(v___x_4459_, 1, v___x_4457_);
lean_ctor_set(v___x_4459_, 2, v___x_4455_);
lean_ctor_set(v___x_4459_, 3, v___x_4455_);
lean_ctor_set_usize(v___x_4459_, 4, v___x_4454_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(lean_object* v_t_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v_infoState_4465_; uint8_t v_enabled_4466_; 
v___x_4464_ = lean_st_ref_get(v___y_4462_);
v_infoState_4465_ = lean_ctor_get(v___x_4464_, 8);
lean_inc_ref(v_infoState_4465_);
lean_dec(v___x_4464_);
v_enabled_4466_ = lean_ctor_get_uint8(v_infoState_4465_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4465_);
if (v_enabled_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_t_4460_);
v___x_4467_ = lean_box(0);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1);
v___x_4470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_t_4460_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v___x_4470_, v___y_4462_);
return v___x_4471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___boxed(lean_object* v_t_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v_t_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(lean_object* v_info_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_4481_, 0, v_info_4477_);
v___x_4482_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4481_, v___y_4478_, v___y_4479_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0___boxed(lean_object* v_info_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v_info_4483_, v___y_4484_, v___y_4485_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
return v_res_4487_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0));
v___x_4490_ = l_Lean_stringToMessageData(v___x_4489_);
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(lean_object* v_optionName_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4498_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1);
v___x_4499_ = l_Lean_MessageData_ofName(v_optionName_4494_);
v___x_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4498_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
v___x_4501_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4502_, v___y_4495_, v___y_4496_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___boxed(lean_object* v_optionName_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(lean_object* v_o_4509_, lean_object* v_k_4510_, lean_object* v_v_4511_){
_start:
{
lean_object* v_map_4512_; uint8_t v_hasTrace_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4526_; 
v_map_4512_ = lean_ctor_get(v_o_4509_, 0);
v_hasTrace_4513_ = lean_ctor_get_uint8(v_o_4509_, sizeof(void*)*1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_o_4509_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4515_ = v_o_4509_;
v_isShared_4516_ = v_isSharedCheck_4526_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_map_4512_);
lean_dec(v_o_4509_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4526_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; 
lean_inc(v_k_4510_);
v___x_4517_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4510_, v_v_4511_, v_map_4512_);
if (v_hasTrace_4513_ == 0)
{
lean_object* v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4521_; 
v___x_4518_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_4519_ = l_Lean_Name_isPrefixOf(v___x_4518_, v_k_4510_);
lean_dec(v_k_4510_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4517_);
v___x_4521_ = v___x_4515_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4517_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_ctor_set_uint8(v___x_4521_, sizeof(void*)*1, v___x_4519_);
return v___x_4521_;
}
}
else
{
lean_object* v___x_4524_; 
lean_dec(v_k_4510_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4517_);
v___x_4524_ = v___x_4515_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4517_);
lean_ctor_set_uint8(v_reuseFailAlloc_4525_, sizeof(void*)*1, v_hasTrace_4513_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_msg_4527_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = l_Lean_instInhabitedExpr;
v___x_4529_ = lean_panic_fn_borrowed(v___x_4528_, v_msg_4527_);
return v___x_4529_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_4532_ = l_Lean_stringToMessageData(v___x_4531_);
return v___x_4532_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_4535_ = l_Lean_stringToMessageData(v___x_4534_);
return v___x_4535_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4));
v___x_4538_ = l_Lean_stringToMessageData(v___x_4537_);
return v___x_4538_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6));
v___x_4541_ = l_Lean_stringToMessageData(v___x_4540_);
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16(void){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4553_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15));
v___x_4554_ = lean_unsigned_to_nat(14u);
v___x_4555_ = lean_unsigned_to_nat(22u);
v___x_4556_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14));
v___x_4557_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13));
v___x_4558_ = l_mkPanicMessageWithDecl(v___x_4557_, v___x_4556_, v___x_4555_, v___x_4554_, v___x_4553_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(lean_object* v_optionName_4559_, lean_object* v_found_4560_, lean_object* v_defVal_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_4561_);
if (lean_obj_tag(v___x_4565_) == 1)
{
lean_object* v_val_4566_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4589_; lean_object* v___x_4637_; 
v_val_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_val_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4637_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_4560_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16);
v___x_4639_ = l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(v___x_4638_);
v___y_4589_ = v___x_4639_;
goto v___jp_4588_;
}
else
{
lean_object* v_val_4640_; 
v_val_4640_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_val_4640_);
lean_dec_ref_known(v___x_4637_, 1);
v___y_4589_ = v_val_4640_;
goto v___jp_4588_;
}
v___jp_4567_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4571_ = l_Lean_MessageData_ofFormat(v___y_4570_);
v___x_4572_ = l_Lean_indentD(v___x_4571_);
lean_inc_ref(v___y_4569_);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___y_4569_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1);
v___x_4575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4573_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = l_Lean_MessageData_ofExpr(v___y_4568_);
v___x_4577_ = l_Lean_indentD(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4575_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4578_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
v___x_4581_ = l_Lean_MessageData_ofName(v_optionName_4559_);
v___x_4582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4580_);
lean_ctor_set(v___x_4582_, 1, v___x_4581_);
v___x_4583_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5);
v___x_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = l_Lean_indentExpr(v_val_4566_);
v___x_4586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4584_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
v___x_4587_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4586_, v___y_4562_, v___y_4563_);
return v___x_4587_;
}
v___jp_4588_:
{
lean_object* v___x_4590_; 
v___x_4590_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7);
switch(lean_obj_tag(v_found_4560_))
{
case 0:
{
lean_object* v_v_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4599_; 
v_v_4591_ = lean_ctor_get(v_found_4560_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_found_4560_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4593_ = v_found_4560_;
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_v_4591_);
lean_dec(v_found_4560_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4595_ = l_String_quote(v_v_4591_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 3);
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
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4597_;
goto v___jp_4567_;
}
}
}
case 1:
{
uint8_t v_v_4600_; 
v_v_4600_ = lean_ctor_get_uint8(v_found_4560_, 0);
lean_dec_ref_known(v_found_4560_, 0);
if (v_v_4600_ == 0)
{
lean_object* v___x_4601_; 
v___x_4601_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9));
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4601_;
goto v___jp_4567_;
}
else
{
lean_object* v___x_4602_; 
v___x_4602_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11));
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4602_;
goto v___jp_4567_;
}
}
case 2:
{
lean_object* v_v_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4614_; 
v_v_4603_ = lean_ctor_get(v_found_4560_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_found_4560_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4605_ = v_found_4560_;
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_v_4603_);
lean_dec(v_found_4560_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; uint8_t v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4607_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12));
v___x_4608_ = 1;
v___x_4609_ = l_Lean_Name_toString(v_v_4603_, v___x_4608_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set_tag(v___x_4605_, 3);
lean_ctor_set(v___x_4605_, 0, v___x_4609_);
v___x_4611_ = v___x_4605_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; 
v___x_4612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4607_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4612_;
goto v___jp_4567_;
}
}
}
case 3:
{
lean_object* v_v_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4623_; 
v_v_4615_ = lean_ctor_get(v_found_4560_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v_found_4560_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4617_ = v_found_4560_;
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_v_4615_);
lean_dec(v_found_4560_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = l_Nat_reprFast(v_v_4615_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4621_;
goto v___jp_4567_;
}
}
}
case 4:
{
lean_object* v_v_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4632_; 
v_v_4624_ = lean_ctor_get(v_found_4560_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v_found_4560_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4626_ = v_found_4560_;
v_isShared_4627_ = v_isSharedCheck_4632_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_v_4624_);
lean_dec(v_found_4560_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4632_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4630_; 
v___x_4628_ = l_Int_repr(v_v_4624_);
lean_dec(v_v_4624_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set_tag(v___x_4626_, 3);
lean_ctor_set(v___x_4626_, 0, v___x_4628_);
v___x_4630_ = v___x_4626_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4630_;
goto v___jp_4567_;
}
}
}
default: 
{
lean_object* v_v_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; lean_object* v___x_4636_; 
v_v_4633_ = lean_ctor_get(v_found_4560_, 0);
lean_inc(v_v_4633_);
lean_dec_ref_known(v_found_4560_, 1);
v___x_4634_ = lean_box(0);
v___x_4635_ = 0;
v___x_4636_ = l_Lean_Syntax_formatStx(v_v_4633_, v___x_4634_, v___x_4635_);
v___y_4568_ = v___y_4589_;
v___y_4569_ = v___x_4590_;
v___y_4570_ = v___x_4636_;
goto v___jp_4567_;
}
}
}
}
else
{
lean_object* v___x_4641_; 
lean_dec(v___x_4565_);
lean_dec_ref(v_found_4560_);
v___x_4641_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4559_, v___y_4562_, v___y_4563_);
return v___x_4641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_optionName_4642_, lean_object* v_found_4643_, lean_object* v_defVal_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4642_, v_found_4643_, v_defVal_4644_, v___y_4645_, v___y_4646_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec_ref(v_defVal_4644_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(lean_object* v_optionName_4649_, lean_object* v_decl_4650_, lean_object* v_val_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_defValue_4655_; uint8_t v___x_4656_; 
v_defValue_4655_ = lean_ctor_get(v_decl_4650_, 2);
v___x_4656_ = l_Lean_DataValue_sameCtor(v_defValue_4655_, v_val_4651_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4649_, v_val_4651_, v_defValue_4655_, v___y_4652_, v___y_4653_);
return v___x_4657_;
}
else
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
lean_dec_ref(v_val_4651_);
lean_dec(v_optionName_4649_);
v___x_4658_ = lean_box(0);
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
return v___x_4659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5___boxed(lean_object* v_optionName_4660_, lean_object* v_decl_4661_, lean_object* v_val_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4660_, v_decl_4661_, v_val_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec_ref(v_decl_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(lean_object* v_optionName_4667_, lean_object* v_decl_4668_, lean_object* v_val_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; 
lean_inc_ref(v_val_4669_);
lean_inc(v_optionName_4667_);
v___x_4673_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4667_, v_decl_4668_, v_val_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4687_; 
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v___x_4673_, 0);
lean_dec(v_unused_4688_);
v___x_4675_ = v___x_4673_;
v_isShared_4676_ = v_isSharedCheck_4687_;
goto v_resetjp_4674_;
}
else
{
lean_dec(v___x_4673_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4687_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v_scopes_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v_opts_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4685_; 
v___x_4677_ = lean_st_ref_get(v___y_4671_);
v_scopes_4678_ = lean_ctor_get(v___x_4677_, 2);
lean_inc(v_scopes_4678_);
lean_dec(v___x_4677_);
v___x_4679_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4680_ = l_List_head_x21___redArg(v___x_4679_, v_scopes_4678_);
lean_dec(v_scopes_4678_);
v_opts_4681_ = lean_ctor_get(v___x_4680_, 1);
lean_inc_ref(v_opts_4681_);
lean_dec(v___x_4680_);
v___x_4682_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(v_opts_4681_, v_optionName_4667_, v_val_4669_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v_decl_4668_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4683_);
v___x_4685_ = v___x_4675_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref(v_val_4669_);
lean_dec_ref(v_decl_4668_);
lean_dec(v_optionName_4667_);
v_a_4689_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4673_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4673_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3___boxed(lean_object* v_optionName_4697_, lean_object* v_decl_4698_, lean_object* v_val_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4697_, v_decl_4698_, v_val_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
return v_res_4703_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4705_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0));
v___x_4706_ = l_Lean_stringToMessageData(v___x_4705_);
return v___x_4706_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2));
v___x_4709_ = l_Lean_stringToMessageData(v___x_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(lean_object* v_id_4710_, lean_object* v_val_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l_Lean_Elab_Command_getRef___redArg(v___y_4712_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4796_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc_n(v_a_4716_, 2);
lean_dec_ref_known(v___x_4715_, 1);
v___x_4717_ = l_Lean_Syntax_getArgs(v_a_4716_);
v___x_4718_ = lean_unsigned_to_nat(3u);
v___x_4719_ = lean_unsigned_to_nat(0u);
v___x_4720_ = l_Array_toSubarray___redArg(v___x_4717_, v___x_4719_, v___x_4718_);
v___x_4721_ = l_Subarray_copy___redArg(v___x_4720_);
v___x_4722_ = l_Lean_Syntax_setArgs(v_a_4716_, v___x_4721_);
v___x_4723_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
v___x_4724_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v___x_4723_, v___y_4712_, v___y_4713_);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v___x_4724_, 0);
lean_dec(v_unused_4797_);
v___x_4726_ = v___x_4724_;
v_isShared_4727_ = v_isSharedCheck_4796_;
goto v_resetjp_4725_;
}
else
{
lean_dec(v___x_4724_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4796_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4728_; lean_object* v_optionName_4729_; lean_object* v___x_4730_; 
v___x_4728_ = l_Lean_Syntax_getId(v_id_4710_);
v_optionName_4729_ = l_Lean_Name_eraseMacroScopes(v___x_4728_);
lean_dec(v___x_4728_);
lean_inc(v_optionName_4729_);
v___x_4730_ = l_Lean_getOptionDecl(v_optionName_4729_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v_declName_4732_; lean_object* v_defValue_4733_; lean_object* v___x_4734_; lean_object* v___x_4736_; 
lean_dec(v_a_4716_);
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v_declName_4732_ = lean_ctor_get(v_a_4731_, 1);
v_defValue_4733_ = lean_ctor_get(v_a_4731_, 2);
lean_inc(v_declName_4732_);
lean_inc(v_optionName_4729_);
v___x_4734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4734_, 0, v_id_4710_);
lean_ctor_set(v___x_4734_, 1, v_optionName_4729_);
lean_ctor_set(v___x_4734_, 2, v_declName_4732_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set_tag(v___x_4726_, 5);
lean_ctor_set(v___x_4726_, 0, v___x_4734_);
v___x_4736_ = v___x_4726_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4752_; 
v___x_4737_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4736_, v___y_4712_, v___y_4713_);
lean_dec_ref(v___x_4737_);
v___x_4752_ = l_Lean_Syntax_isStrLit_x3f(v_val_4711_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v___x_4753_; 
v___x_4753_ = l_Lean_Syntax_isNatLit_x3f(v_val_4711_);
if (lean_obj_tag(v___x_4753_) == 0)
{
if (lean_obj_tag(v_val_4711_) == 2)
{
lean_object* v_val_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v_val_4754_ = lean_ctor_get(v_val_4711_, 1);
v___x_4755_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10));
v___x_4756_ = lean_string_dec_eq(v_val_4754_, v___x_4755_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4757_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8));
v___x_4758_ = lean_string_dec_eq(v_val_4754_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_inc_ref(v_defValue_4733_);
lean_dec(v_a_4731_);
goto v___jp_4738_;
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec_ref_known(v_val_4711_, 2);
v___x_4759_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4759_, 0, v___x_4756_);
v___x_4760_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4729_, v_a_4731_, v___x_4759_, v___y_4712_, v___y_4713_);
return v___x_4760_;
}
}
else
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec_ref_known(v_val_4711_, 2);
v___x_4761_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4761_, 0, v___x_4756_);
v___x_4762_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4729_, v_a_4731_, v___x_4761_, v___y_4712_, v___y_4713_);
return v___x_4762_;
}
}
else
{
lean_inc_ref(v_defValue_4733_);
lean_dec(v_a_4731_);
goto v___jp_4738_;
}
}
else
{
lean_object* v_val_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_val_4711_);
v_val_4763_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4765_ = v___x_4753_;
v_isShared_4766_ = v_isSharedCheck_4771_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_val_4763_);
lean_dec(v___x_4753_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4771_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
lean_ctor_set_tag(v___x_4765_, 3);
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_val_4763_);
v___x_4768_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; 
v___x_4769_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4729_, v_a_4731_, v___x_4768_, v___y_4712_, v___y_4713_);
return v___x_4769_;
}
}
}
}
else
{
lean_object* v_val_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4780_; 
lean_dec(v_val_4711_);
v_val_4772_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4774_ = v___x_4752_;
v_isShared_4775_ = v_isSharedCheck_4780_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_val_4772_);
lean_dec(v___x_4752_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4780_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
lean_ctor_set_tag(v___x_4774_, 0);
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_val_4772_);
v___x_4777_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4729_, v_a_4731_, v___x_4777_, v___y_4712_, v___y_4713_);
return v___x_4778_;
}
}
}
v___jp_4738_:
{
lean_object* v___x_4739_; 
v___x_4739_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_4733_);
lean_dec_ref(v_defValue_4733_);
if (lean_obj_tag(v___x_4739_) == 1)
{
lean_object* v_val_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_dec(v_optionName_4729_);
v_val_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_val_4740_);
lean_dec_ref_known(v___x_4739_, 1);
v___x_4741_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1);
v___x_4742_ = l_Lean_MessageData_ofSyntax(v_val_4711_);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3);
v___x_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v___x_4744_);
v___x_4746_ = l_Lean_MessageData_ofExpr(v_val_4740_);
v___x_4747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
v___x_4748_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4747_);
lean_ctor_set(v___x_4749_, 1, v___x_4748_);
v___x_4750_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4749_, v___y_4712_, v___y_4713_);
return v___x_4750_;
}
else
{
lean_object* v___x_4751_; 
lean_dec(v___x_4739_);
lean_dec(v_val_4711_);
v___x_4751_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4729_, v___y_4712_, v___y_4713_);
return v___x_4751_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4795_; 
lean_dec(v_optionName_4729_);
lean_dec(v_val_4711_);
lean_dec(v_id_4710_);
v_a_4782_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4784_ = v___x_4730_;
v_isShared_4785_ = v_isSharedCheck_4795_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4730_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4795_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4786_ = lean_io_error_to_string(v_a_4782_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set_tag(v___x_4726_, 3);
lean_ctor_set(v___x_4726_, 0, v___x_4786_);
v___x_4788_ = v___x_4726_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4789_ = l_Lean_MessageData_ofFormat(v___x_4788_);
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_a_4716_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v___x_4790_);
v___x_4792_ = v___x_4784_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec(v_val_4711_);
lean_dec(v_id_4710_);
v_a_4798_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4715_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4715_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___boxed(lean_object* v_id_4806_, lean_object* v_val_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v_id_4806_, v_val_4807_, v___y_4808_, v___y_4809_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object* v___x_4812_, lean_object* v___x_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v___x_4812_, v___x_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4826_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v_fst_4822_; lean_object* v___x_4824_; 
v_fst_4822_ = lean_ctor_get(v_a_4818_, 0);
lean_inc(v_fst_4822_);
lean_dec(v_a_4818_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v_fst_4822_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_fst_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4843_; 
v_a_4827_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4829_ = v___x_4817_;
v_isShared_4830_ = v_isSharedCheck_4843_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4817_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4843_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
uint8_t v___x_4831_; 
v___x_4831_ = l_Lean_Exception_isInterrupt(v_a_4827_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; lean_object* v_scopes_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v_opts_4836_; lean_object* v___x_4838_; 
lean_dec(v_a_4827_);
v___x_4832_ = lean_st_ref_get(v___y_4815_);
v_scopes_4833_ = lean_ctor_get(v___x_4832_, 2);
lean_inc(v_scopes_4833_);
lean_dec(v___x_4832_);
v___x_4834_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4835_ = l_List_head_x21___redArg(v___x_4834_, v_scopes_4833_);
lean_dec(v_scopes_4833_);
v_opts_4836_ = lean_ctor_get(v___x_4835_, 1);
lean_inc_ref(v_opts_4836_);
lean_dec(v___x_4835_);
if (v_isShared_4830_ == 0)
{
lean_ctor_set_tag(v___x_4829_, 0);
lean_ctor_set(v___x_4829_, 0, v_opts_4836_);
v___x_4838_ = v___x_4829_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_opts_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
else
{
lean_object* v___x_4841_; 
if (v_isShared_4830_ == 0)
{
v___x_4841_ = v___x_4829_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4827_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object* v___x_4844_, lean_object* v___x_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(v___x_4844_, v___x_4845_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1(lean_object* v_a_4850_, lean_object* v_x_4851_){
_start:
{
lean_object* v_header_4852_; lean_object* v_currNamespace_4853_; lean_object* v_openDecls_4854_; lean_object* v_levelNames_4855_; lean_object* v_varDecls_4856_; lean_object* v_varUIds_4857_; lean_object* v_includedVars_4858_; lean_object* v_omittedVars_4859_; uint8_t v_isNoncomputable_4860_; uint8_t v_isPublic_4861_; uint8_t v_isMeta_4862_; lean_object* v_attrs_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
v_header_4852_ = lean_ctor_get(v_x_4851_, 0);
v_currNamespace_4853_ = lean_ctor_get(v_x_4851_, 2);
v_openDecls_4854_ = lean_ctor_get(v_x_4851_, 3);
v_levelNames_4855_ = lean_ctor_get(v_x_4851_, 4);
v_varDecls_4856_ = lean_ctor_get(v_x_4851_, 5);
v_varUIds_4857_ = lean_ctor_get(v_x_4851_, 6);
v_includedVars_4858_ = lean_ctor_get(v_x_4851_, 7);
v_omittedVars_4859_ = lean_ctor_get(v_x_4851_, 8);
v_isNoncomputable_4860_ = lean_ctor_get_uint8(v_x_4851_, sizeof(void*)*10);
v_isPublic_4861_ = lean_ctor_get_uint8(v_x_4851_, sizeof(void*)*10 + 1);
v_isMeta_4862_ = lean_ctor_get_uint8(v_x_4851_, sizeof(void*)*10 + 2);
v_attrs_4863_ = lean_ctor_get(v_x_4851_, 9);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_x_4851_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; 
v_unused_4871_ = lean_ctor_get(v_x_4851_, 1);
lean_dec(v_unused_4871_);
v___x_4865_ = v_x_4851_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_attrs_4863_);
lean_inc(v_omittedVars_4859_);
lean_inc(v_includedVars_4858_);
lean_inc(v_varUIds_4857_);
lean_inc(v_varDecls_4856_);
lean_inc(v_levelNames_4855_);
lean_inc(v_openDecls_4854_);
lean_inc(v_currNamespace_4853_);
lean_inc(v_header_4852_);
lean_dec(v_x_4851_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 1, v_a_4850_);
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_header_4852_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_a_4850_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_currNamespace_4853_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_openDecls_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_levelNames_4855_);
lean_ctor_set(v_reuseFailAlloc_4869_, 5, v_varDecls_4856_);
lean_ctor_set(v_reuseFailAlloc_4869_, 6, v_varUIds_4857_);
lean_ctor_set(v_reuseFailAlloc_4869_, 7, v_includedVars_4858_);
lean_ctor_set(v_reuseFailAlloc_4869_, 8, v_omittedVars_4859_);
lean_ctor_set(v_reuseFailAlloc_4869_, 9, v_attrs_4863_);
lean_ctor_set_uint8(v_reuseFailAlloc_4869_, sizeof(void*)*10, v_isNoncomputable_4860_);
lean_ctor_set_uint8(v_reuseFailAlloc_4869_, sizeof(void*)*10 + 1, v_isPublic_4861_);
lean_ctor_set_uint8(v_reuseFailAlloc_4869_, sizeof(void*)*10 + 2, v_isMeta_4862_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(uint8_t v_flag_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v___x_4875_; lean_object* v_infoState_4876_; lean_object* v_env_4877_; lean_object* v_messages_4878_; lean_object* v_scopes_4879_; lean_object* v_usedQuotCtxts_4880_; lean_object* v_nextMacroScope_4881_; lean_object* v_maxRecDepth_4882_; lean_object* v_ngen_4883_; lean_object* v_auxDeclNGen_4884_; lean_object* v_traceState_4885_; lean_object* v_snapshotTasks_4886_; lean_object* v_prevLinterStates_4887_; lean_object* v_codeQualityEntryTasks_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4908_; 
v___x_4875_ = lean_st_ref_take(v___y_4873_);
v_infoState_4876_ = lean_ctor_get(v___x_4875_, 8);
v_env_4877_ = lean_ctor_get(v___x_4875_, 0);
v_messages_4878_ = lean_ctor_get(v___x_4875_, 1);
v_scopes_4879_ = lean_ctor_get(v___x_4875_, 2);
v_usedQuotCtxts_4880_ = lean_ctor_get(v___x_4875_, 3);
v_nextMacroScope_4881_ = lean_ctor_get(v___x_4875_, 4);
v_maxRecDepth_4882_ = lean_ctor_get(v___x_4875_, 5);
v_ngen_4883_ = lean_ctor_get(v___x_4875_, 6);
v_auxDeclNGen_4884_ = lean_ctor_get(v___x_4875_, 7);
v_traceState_4885_ = lean_ctor_get(v___x_4875_, 9);
v_snapshotTasks_4886_ = lean_ctor_get(v___x_4875_, 10);
v_prevLinterStates_4887_ = lean_ctor_get(v___x_4875_, 11);
v_codeQualityEntryTasks_4888_ = lean_ctor_get(v___x_4875_, 12);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4890_ = v___x_4875_;
v_isShared_4891_ = v_isSharedCheck_4908_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4888_);
lean_inc(v_prevLinterStates_4887_);
lean_inc(v_snapshotTasks_4886_);
lean_inc(v_traceState_4885_);
lean_inc(v_infoState_4876_);
lean_inc(v_auxDeclNGen_4884_);
lean_inc(v_ngen_4883_);
lean_inc(v_maxRecDepth_4882_);
lean_inc(v_nextMacroScope_4881_);
lean_inc(v_usedQuotCtxts_4880_);
lean_inc(v_scopes_4879_);
lean_inc(v_messages_4878_);
lean_inc(v_env_4877_);
lean_dec(v___x_4875_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4908_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v_assignment_4892_; lean_object* v_lazyAssignment_4893_; lean_object* v_trees_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4907_; 
v_assignment_4892_ = lean_ctor_get(v_infoState_4876_, 0);
v_lazyAssignment_4893_ = lean_ctor_get(v_infoState_4876_, 1);
v_trees_4894_ = lean_ctor_get(v_infoState_4876_, 2);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_infoState_4876_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4896_ = v_infoState_4876_;
v_isShared_4897_ = v_isSharedCheck_4907_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_trees_4894_);
lean_inc(v_lazyAssignment_4893_);
lean_inc(v_assignment_4892_);
lean_dec(v_infoState_4876_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4907_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_assignment_4892_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v_lazyAssignment_4893_);
lean_ctor_set(v_reuseFailAlloc_4906_, 2, v_trees_4894_);
v___x_4899_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4901_; 
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*3, v_flag_4872_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 8, v___x_4899_);
v___x_4901_ = v___x_4890_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_env_4877_);
lean_ctor_set(v_reuseFailAlloc_4905_, 1, v_messages_4878_);
lean_ctor_set(v_reuseFailAlloc_4905_, 2, v_scopes_4879_);
lean_ctor_set(v_reuseFailAlloc_4905_, 3, v_usedQuotCtxts_4880_);
lean_ctor_set(v_reuseFailAlloc_4905_, 4, v_nextMacroScope_4881_);
lean_ctor_set(v_reuseFailAlloc_4905_, 5, v_maxRecDepth_4882_);
lean_ctor_set(v_reuseFailAlloc_4905_, 6, v_ngen_4883_);
lean_ctor_set(v_reuseFailAlloc_4905_, 7, v_auxDeclNGen_4884_);
lean_ctor_set(v_reuseFailAlloc_4905_, 8, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4905_, 9, v_traceState_4885_);
lean_ctor_set(v_reuseFailAlloc_4905_, 10, v_snapshotTasks_4886_);
lean_ctor_set(v_reuseFailAlloc_4905_, 11, v_prevLinterStates_4887_);
lean_ctor_set(v_reuseFailAlloc_4905_, 12, v_codeQualityEntryTasks_4888_);
v___x_4901_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4902_ = lean_st_ref_put(v___y_4873_, v___x_4901_);
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg___boxed(lean_object* v_flag_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
uint8_t v_flag_boxed_4912_; lean_object* v_res_4913_; 
v_flag_boxed_4912_ = lean_unbox(v_flag_4909_);
v_res_4913_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_boxed_4912_, v___y_4910_);
lean_dec(v___y_4910_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(uint8_t v_flag_4914_, lean_object* v_x_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_){
_start:
{
lean_object* v___x_4919_; lean_object* v_infoState_4920_; uint8_t v_enabled_4921_; lean_object* v_a_4923_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4919_ = lean_st_ref_get(v___y_4917_);
v_infoState_4920_ = lean_ctor_get(v___x_4919_, 8);
lean_inc_ref(v_infoState_4920_);
lean_dec(v___x_4919_);
v_enabled_4921_ = lean_ctor_get_uint8(v_infoState_4920_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4920_);
v___x_4933_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_4914_, v___y_4917_);
lean_dec_ref(v___x_4933_);
lean_inc(v___y_4917_);
lean_inc_ref(v___y_4916_);
v___x_4934_ = lean_apply_3(v_x_4915_, v___y_4916_, v___y_4917_, lean_box(0));
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4934_, 1);
v___x_4936_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4921_, v___y_4917_);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4943_ == 0)
{
lean_object* v_unused_4944_; 
v_unused_4944_ = lean_ctor_get(v___x_4936_, 0);
lean_dec(v_unused_4944_);
v___x_4938_ = v___x_4936_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_dec(v___x_4936_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v_a_4935_);
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4935_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
else
{
lean_object* v_a_4945_; 
v_a_4945_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___x_4934_, 1);
v_a_4923_ = v_a_4945_;
goto v___jp_4922_;
}
v___jp_4922_:
{
lean_object* v___x_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
v___x_4924_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4921_, v___y_4917_);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4931_ == 0)
{
lean_object* v_unused_4932_; 
v_unused_4932_ = lean_ctor_get(v___x_4924_, 0);
lean_dec(v_unused_4932_);
v___x_4926_ = v___x_4924_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_dec(v___x_4924_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set_tag(v___x_4926_, 1);
lean_ctor_set(v___x_4926_, 0, v_a_4923_);
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4923_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg___boxed(lean_object* v_flag_4946_, lean_object* v_x_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
uint8_t v_flag_boxed_4951_; lean_object* v_res_4952_; 
v_flag_boxed_4951_ = lean_unbox(v_flag_4946_);
v_res_4952_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_boxed_4951_, v_x_4947_, v___y_4948_, v___y_4949_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object* v_stx_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; uint8_t v___x_4967_; 
v___x_4963_ = lean_unsigned_to_nat(0u);
v___x_4964_ = l_Lean_Syntax_getArg(v_stx_4959_, v___x_4963_);
lean_inc(v___x_4964_);
v___x_4965_ = l_Lean_Syntax_getKind(v___x_4964_);
v___x_4966_ = ((lean_object*)(l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1));
v___x_4967_ = lean_name_eq(v___x_4965_, v___x_4966_);
lean_dec(v___x_4965_);
if (v___x_4967_ == 0)
{
lean_object* v___x_4968_; lean_object* v_run_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
lean_dec(v___x_4964_);
v___x_4968_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4969_ = lean_ctor_get(v___x_4968_, 0);
v___x_4970_ = lean_unsigned_to_nat(2u);
v___x_4971_ = l_Lean_Syntax_getArg(v_stx_4959_, v___x_4970_);
lean_inc_ref(v_run_4969_);
lean_inc(v_a_4961_);
lean_inc_ref(v_a_4960_);
v___x_4972_ = lean_apply_4(v_run_4969_, v___x_4971_, v_a_4960_, v_a_4961_, lean_box(0));
return v___x_4972_;
}
else
{
uint8_t v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___f_4978_; lean_object* v___x_4979_; 
v___x_4973_ = 0;
v___x_4974_ = lean_unsigned_to_nat(1u);
v___x_4975_ = l_Lean_Syntax_getArg(v___x_4964_, v___x_4974_);
v___x_4976_ = lean_unsigned_to_nat(3u);
v___x_4977_ = l_Lean_Syntax_getArg(v___x_4964_, v___x_4976_);
lean_dec(v___x_4964_);
v___f_4978_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_4978_, 0, v___x_4975_);
lean_closure_set(v___f_4978_, 1, v___x_4977_);
v___x_4979_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v___x_4973_, v___f_4978_, v_a_4960_, v_a_4961_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4981_; lean_object* v_run_4982_; lean_object* v___f_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4979_, 1);
v___x_4981_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4982_ = lean_ctor_get(v___x_4981_, 0);
v___f_4983_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4983_, 0, v_a_4980_);
v___x_4984_ = lean_unsigned_to_nat(2u);
v___x_4985_ = l_Lean_Syntax_getArg(v_stx_4959_, v___x_4984_);
lean_inc_ref(v_run_4982_);
v___x_4986_ = lean_apply_1(v_run_4982_, v___x_4985_);
v___x_4987_ = l_Lean_Elab_Command_withScope___redArg(v___f_4983_, v___x_4986_, v_a_4960_, v_a_4961_);
return v___x_4987_;
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
v_a_4988_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4979_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4979_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object* v_stx_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_4996_, v_a_4997_, v_a_4998_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_stx_4996_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t v_x_5001_, lean_object* v_stx_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_){
_start:
{
lean_object* v___x_5006_; 
v___x_5006_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_5002_, v_a_5003_, v_a_5004_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object* v_x_5007_, lean_object* v_stx_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
uint8_t v_x_4360__boxed_5012_; lean_object* v_res_5013_; 
v_x_4360__boxed_5012_ = lean_unbox(v_x_5007_);
v_res_5013_ = l_Lean_Linter_MissingDocs_handleIn(v_x_4360__boxed_5012_, v_stx_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_stx_5008_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(uint8_t v_flag_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_5014_, v___y_5016_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___boxed(lean_object* v_flag_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
uint8_t v_flag_boxed_5023_; lean_object* v_res_5024_; 
v_flag_boxed_5023_ = lean_unbox(v_flag_5019_);
v_res_5024_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(v_flag_boxed_5023_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(lean_object* v_00_u03b1_5025_, uint8_t v_flag_5026_, lean_object* v_x_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_5026_, v_x_5027_, v___y_5028_, v___y_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___boxed(lean_object* v_00_u03b1_5032_, lean_object* v_flag_5033_, lean_object* v_x_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
uint8_t v_flag_boxed_5038_; lean_object* v_res_5039_; 
v_flag_boxed_5038_ = lean_unbox(v_flag_5033_);
v_res_5039_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(v_00_u03b1_5032_, v_flag_boxed_5038_, v_x_5034_, v___y_5035_, v___y_5036_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(lean_object* v_t_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v___x_5044_; 
v___x_5044_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_5040_, v___y_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___boxed(lean_object* v_t_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(v_t_5045_, v___y_5046_, v___y_5047_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(lean_object* v_00_u03b1_5050_, lean_object* v_optionName_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_5051_, v___y_5052_, v___y_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___boxed(lean_object* v_00_u03b1_5056_, lean_object* v_optionName_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(v_00_u03b1_5056_, v_optionName_5057_, v___y_5058_, v___y_5059_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5069_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1));
v___x_5070_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___boxed), 5, 0);
v___x_5071_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5069_, v___x_5070_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___boxed(lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object* v_as_5074_, size_t v_i_5075_, size_t v_stop_5076_, lean_object* v_b_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v___x_5081_; lean_object* v_run_5082_; uint8_t v___x_5083_; 
v___x_5081_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_5082_ = lean_ctor_get(v___x_5081_, 0);
v___x_5083_ = lean_usize_dec_eq(v_i_5075_, v_stop_5076_);
if (v___x_5083_ == 0)
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_array_uget_borrowed(v_as_5074_, v_i_5075_);
lean_inc_ref(v_run_5082_);
lean_inc(v___y_5079_);
lean_inc_ref(v___y_5078_);
lean_inc(v___x_5084_);
v___x_5085_ = lean_apply_4(v_run_5082_, v___x_5084_, v___y_5078_, v___y_5079_, lean_box(0));
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; size_t v___x_5087_; size_t v___x_5088_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
v___x_5087_ = ((size_t)1ULL);
v___x_5088_ = lean_usize_add(v_i_5075_, v___x_5087_);
v_i_5075_ = v___x_5088_;
v_b_5077_ = v_a_5086_;
goto _start;
}
else
{
return v___x_5085_;
}
}
else
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v_b_5077_);
return v___x_5090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object* v_as_5091_, lean_object* v_i_5092_, lean_object* v_stop_5093_, lean_object* v_b_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
size_t v_i_boxed_5098_; size_t v_stop_boxed_5099_; lean_object* v_res_5100_; 
v_i_boxed_5098_ = lean_unbox_usize(v_i_5092_);
lean_dec(v_i_5092_);
v_stop_boxed_5099_ = lean_unbox_usize(v_stop_5093_);
lean_dec(v_stop_5093_);
v_res_5100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v_as_5091_, v_i_boxed_5098_, v_stop_boxed_5099_, v_b_5094_, v___y_5095_, v___y_5096_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec_ref(v_as_5091_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object* v_stx_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v___x_5105_ = lean_unsigned_to_nat(1u);
v___x_5106_ = l_Lean_Syntax_getArg(v_stx_5101_, v___x_5105_);
v___x_5107_ = l_Lean_Syntax_getArgs(v___x_5106_);
lean_dec(v___x_5106_);
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = lean_array_get_size(v___x_5107_);
v___x_5110_ = lean_box(0);
v___x_5111_ = lean_nat_dec_lt(v___x_5108_, v___x_5109_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
lean_dec_ref(v___x_5107_);
v___x_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5110_);
return v___x_5112_;
}
else
{
uint8_t v___x_5113_; 
v___x_5113_ = lean_nat_dec_le(v___x_5109_, v___x_5109_);
if (v___x_5113_ == 0)
{
if (v___x_5111_ == 0)
{
lean_object* v___x_5114_; 
lean_dec_ref(v___x_5107_);
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5110_);
return v___x_5114_;
}
else
{
size_t v___x_5115_; size_t v___x_5116_; lean_object* v___x_5117_; 
v___x_5115_ = ((size_t)0ULL);
v___x_5116_ = lean_usize_of_nat(v___x_5109_);
v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5107_, v___x_5115_, v___x_5116_, v___x_5110_, v_a_5102_, v_a_5103_);
lean_dec_ref(v___x_5107_);
return v___x_5117_;
}
}
else
{
size_t v___x_5118_; size_t v___x_5119_; lean_object* v___x_5120_; 
v___x_5118_ = ((size_t)0ULL);
v___x_5119_ = lean_usize_of_nat(v___x_5109_);
v___x_5120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5107_, v___x_5118_, v___x_5119_, v___x_5110_, v_a_5102_, v_a_5103_);
lean_dec_ref(v___x_5107_);
return v___x_5120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object* v_stx_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5121_, v_a_5122_, v_a_5123_);
lean_dec(v_a_5123_);
lean_dec_ref(v_a_5122_);
lean_dec(v_stx_5121_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t v_x_5126_, lean_object* v_stx_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5127_, v_a_5128_, v_a_5129_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object* v_x_5132_, lean_object* v_stx_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_){
_start:
{
uint8_t v_x_402__boxed_5137_; lean_object* v_res_5138_; 
v_x_402__boxed_5137_ = lean_unbox(v_x_5132_);
v_res_5138_ = l_Lean_Linter_MissingDocs_handleMutual(v_x_402__boxed_5137_, v_stx_5133_, v_a_5134_, v_a_5135_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
lean_dec(v_stx_5133_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(){
_start:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5146_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1));
v___x_5147_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleMutual___boxed), 5, 0);
v___x_5148_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5146_, v___x_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___boxed(lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
return v_res_5150_;
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
