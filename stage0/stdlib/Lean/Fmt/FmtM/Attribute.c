// Lean compiler output
// Module: Lean.Fmt.FmtM.Attribute
// Imports: public import Lean.KeyedDeclsAttribute public import Lean.Util.ShareCommon public import Lean.Fmt.FmtM.LineInfo import Lean.Compiler.InitAttr import Lean.ExtraModUses import Lean.Fmt.Util.Module public import Lean.Fmt.Core.Formatter public import Lean.Elab.InfoTree.Types import Lean.Elab.InfoTree.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_headerKind;
extern lean_object* l_Lean_Fmt_cmdsKind;
extern lean_object* l_Lean_Fmt_moduleKind;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* l___private_Init_ShareCommon_0__ShareCommon_Internal_mkStateImpl(lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "formattedLeadingRanges"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "formattedTrailingRanges"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprFormattedWhitespace = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_findChoiceResolution_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedRangeKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedRangeKind;
static lean_once_cell_t l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedBacktrackableState;
static lean_once_cell_t l_Lean_Fmt_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value;
static const lean_closure_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value),((lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "FmtProvider"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 236, 229, 98, 188, 250, 110, 22)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 65, 253, 3, 148, 106, 71, 75)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "FmtM"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 159, 213, 161, 201, 106, 171, 95)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Attribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 135, 163, 172, 195, 71, 93, 157)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(131, 255, 197, 156, 51, 230, 211, 19)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 200, 25, 73, 146, 5, 187, 87)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 242, 105, 235, 81, 147, 109, 184)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtProvidersExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(150, 4, 9, 207, 82, 17, 215, 63)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
static lean_once_cell_t l_Lean_Fmt_getFmtProviders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getFmtProviders___closed__0;
static lean_once_cell_t l_Lean_Fmt_getFmtProviders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getFmtProviders___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 104, 40, 163, 160, 76, 5, 191)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 38, 40, 124, 97, 131, 29, 71)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 56, 150, 150, 115, 144, 165, 34)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(163, 132, 47, 152, 194, 11, 103, 179)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 138, 188, 185, 189, 39, 135, 78)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 230, 191, 161, 252, 34, 33, 68)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)(((size_t)(960770660) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(156, 85, 209, 235, 224, 100, 209, 148)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 236, 80, 239, 142, 237, 17, 65)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 54, 35, 52, 231, 246, 44, 129)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(182, 146, 182, 119, 104, 72, 83, 120)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmt_provider"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 19, 28, 15, 34, 20, 237, 134)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 131, .m_capacity = 131, .m_length = 130, .m_data = "Registers a function of type `Lean.Fmt.FmtProvider` that determines the formatters of the syntax node kinds it is responsible for."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedWhitespace_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedWhitespace;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqWhitespace_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instBEqWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instBEqWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instBEqWhitespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instBEqWhitespace = (const lean_object*)&l_Lean_Fmt_Comment_instBEqWhitespace___closed__0_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Fmt.Comment.Whitespace.leading"};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Fmt.Comment.Whitespace.trailing"};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4;
static lean_once_cell_t l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprWhitespace = (const lean_object*)&l_Lean_Fmt_Comment_instReprWhitespace___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedPlacement_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedPlacement;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instBEqPlacement___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instBEqPlacement = (const lean_object*)&l_Lean_Fmt_Comment_instBEqPlacement___closed__0_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Fmt.Comment.Placement.afterToken"};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Fmt.Comment.Placement.onLineBeforeToken"};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprPlacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprPlacement_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprPlacement___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprPlacement = (const lean_object*)&l_Lean_Fmt_Comment_instReprPlacement___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instInhabitedKind;
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instBEqKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instBEqKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instBEqKind___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instBEqKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instBEqKind = (const lean_object*)&l_Lean_Fmt_Comment_instBEqKind___closed__0_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Fmt.Comment.Kind.lineComment"};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__1 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__1_value;
static const lean_string_object l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Fmt.Comment.Kind.blockComment"};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__2 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_Comment_instReprKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Fmt_Comment_instReprKind_repr___closed__3 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Comment_instReprKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Comment_instReprKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Comment_instReprKind___closed__0 = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Comment_instReprKind = (const lean_object*)&l_Lean_Fmt_Comment_instReprKind___closed__0_value;
static const lean_array_object l_Lean_Fmt_instInhabitedComment_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedComment_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedComment_default___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_instInhabitedComment_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedComment_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedComment_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedComment;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqComment_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqComment_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqComment_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqComment___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqComment___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqComment = (const lean_object*)&l_Lean_Fmt_instBEqComment___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__4;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "placement"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "originalTokenRange"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__10;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "originalWhitespaceRange"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__12_value;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "originalWhitespaceKind"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__17;
static const lean_string_object l_Lean_Fmt_instReprComment_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "emptyLineBefore"};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Fmt_instReprComment_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Fmt_instReprComment_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Fmt_instReprComment_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprComment_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprComment_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprComment___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprComment___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprComment = (const lean_object*)&l_Lean_Fmt_instReprComment___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CommentCollector"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 98, 240, 240, 45, 63, 154, 195)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "commentCollectorsExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 72, 174, 54, 199, 47, 215)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "comment_collector"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 41, 124, 214, 140, 65, 138, 12)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 172, .m_capacity = 172, .m_length = 171, .m_data = "Registers a function of type `Lean.Fmt.CommentCollector` that determines the syntax ranges that the comments of the syntax nodes it is responsible for are associated with."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Invalid `["};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "]` argument: Unknown syntax kind `"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "builtin_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 186, 149, 11, 110, 160, 246, 101)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 91, 59, 249, 145, 13, 225, 114)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Register an Fmt formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 227, 253, 29, 132, 51, 110, 142)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttribute;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "StickyTermFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 18, 157, 57, 152, 236, 157, 39)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "stickyTermFnsExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 174, 81, 16, 95, 89, 87, 244)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "addBuiltinStickyTermFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1916596973) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(179, 4, 9, 36, 218, 22, 47, 250)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 254, 143, 77, 65, 149, 80, 160)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 217, 72, 220, 27, 233, 198, 218)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(21, 161, 79, 54, 3, 163, 193, 91)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "Marks a function of type `Lean.Fmt.StickyTermFn` that determines whether a term propagates the stickiness of its right-hand side in applications."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "builtin_fmt_sticky_term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 108, 12, 189, 11, 163, 111, 169)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmt_sticky_term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 43, 182, 158, 218, 203, 52, 123)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInfixOperationAssociativity;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs_default = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedInfixOperation;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperation___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperation = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperation___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "builtin_infix_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 74, 181, 48, 150, 42, 120, 103)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "infix_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 144, 112, 96, 178, 9, 77, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Register an Fmt infix operation formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InfixOperation"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 213, 114, 139, 57, 44, 99, 238)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "infixFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 47, 14, 153, 195, 148, 187, 112)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_infixFmtAttribute;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "builtin_conditional_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 131, 96, 141, 216, 83, 24, 142)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "conditional_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 10, 147, 54, 4, 250, 52, 122)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Register an Fmt conditional formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ConditionalFmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 202, 187, 174, 192, 20, 94, 223)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "conditionalFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 12, 148, 18, 60, 64, 119, 220)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_conditionalFmtAttribute;
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_quantifier_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 115, 38, 255, 188, 195, 138, 161)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "quantifier_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 134, 102, 113, 68, 22, 10, 145)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Register an Fmt quantifier formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "QuantifierFmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 231, 199, 190, 204, 67, 157, 147)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "quantifierFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 217, 228, 48, 55, 215, 108, 194)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_quantifierFmtAttribute;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_dec(v_x_3_);
return v_x_4_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_17_; 
v_head_6_ = lean_ctor_get(v_x_5_, 0);
v_tail_7_ = lean_ctor_get(v_x_5_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v_x_5_);
if (v_isSharedCheck_17_ == 0)
{
v___x_9_ = v_x_5_;
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_tail_7_);
lean_inc(v_head_6_);
lean_dec(v_x_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
lean_inc(v_x_3_);
if (v_isShared_10_ == 0)
{
lean_ctor_set_tag(v___x_9_, 5);
lean_ctor_set(v___x_9_, 1, v_x_3_);
lean_ctor_set(v___x_9_, 0, v_x_4_);
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_x_4_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_x_3_);
v___x_12_ = v_reuseFailAlloc_16_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_6_);
v___x_14_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v_x_4_ = v___x_14_;
v_x_5_ = v_tail_7_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_dec(v_x_18_);
return v_x_19_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_head_21_ = lean_ctor_get(v_x_20_, 0);
v_tail_22_ = lean_ctor_get(v_x_20_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v_x_20_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_head_21_);
lean_dec(v_x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
lean_inc(v_x_18_);
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 5);
lean_ctor_set(v___x_24_, 1, v_x_18_);
lean_ctor_set(v___x_24_, 0, v_x_19_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_x_19_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_x_18_);
v___x_27_ = v_reuseFailAlloc_31_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_21_);
v___x_29_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(v_x_18_, v___x_29_, v_tail_22_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_35_; 
lean_dec(v_x_34_);
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
lean_object* v_tail_36_; 
v_tail_36_ = lean_ctor_get(v_x_33_, 1);
if (lean_obj_tag(v_tail_36_) == 0)
{
lean_object* v_head_37_; lean_object* v___x_38_; 
lean_dec(v_x_34_);
v_head_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_head_37_);
lean_dec_ref_known(v_x_33_, 2);
v___x_38_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc(v_tail_36_);
v_head_39_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_head_39_);
lean_dec_ref_known(v_x_33_, 2);
v___x_40_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_39_);
v___x_41_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(v_x_34_, v___x_40_, v_tail_36_);
return v___x_41_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0));
v___x_51_ = lean_string_length(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(lean_object* v_xs_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_array_get_size(v_xs_61_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_nat_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_65_ = lean_array_to_list(v_xs_61_);
v___x_66_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_67_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(v___x_65_, v___x_66_);
v___x_68_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_69_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_67_);
v___x_71_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = l_Std_Format_fill(v___x_73_);
return v___x_74_;
}
else
{
lean_object* v___x_75_; 
lean_dec_ref(v_xs_61_);
v___x_75_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_75_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(26u);
v___x_90_ = lean_nat_to_int(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(27u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0));
v___x_98_ = lean_string_length(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12);
v___x_100_ = lean_nat_to_int(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(lean_object* v_x_105_){
_start:
{
lean_object* v_formattedLeadingRanges_106_; lean_object* v_formattedTrailingRanges_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_140_; 
v_formattedLeadingRanges_106_ = lean_ctor_get(v_x_105_, 0);
v_formattedTrailingRanges_107_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_140_ == 0)
{
v___x_109_ = v_x_105_;
v_isShared_110_ = v_isSharedCheck_140_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_formattedTrailingRanges_107_);
lean_inc(v_formattedLeadingRanges_106_);
lean_dec(v_x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_140_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_112_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6));
v___x_113_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_114_ = l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(v_formattedLeadingRanges_106_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 4);
lean_ctor_set(v___x_109_, 1, v___x_114_);
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_139_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_112_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_box(1);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9));
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_111_);
v___x_127_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_128_ = l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(v_formattedTrailingRanges_107_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_117_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_126_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_133_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_131_);
v___x_135_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_117_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr(lean_object* v_x_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(v_x_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Fmt_instReprFormattedWhitespace_repr(v_x_144_, v_prec_145_);
lean_dec(v_prec_145_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 1;
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
else
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v_val_155_; uint8_t v___x_156_; 
v_val_154_ = lean_ctor_get(v_x_149_, 0);
v_val_155_ = lean_ctor_get(v_x_150_, 0);
v___x_156_ = l_Lean_Syntax_instBEqRange_beq(v_val_154_, v_val_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v_x_157_, v_x_158_);
lean_dec(v_x_158_);
lean_dec(v_x_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_findChoiceResolution_x3f___lam__0(lean_object* v_range_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 15)
{
lean_object* v_i_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_174_; 
v_i_163_ = lean_ctor_get(v_x_162_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_174_ == 0)
{
v___x_165_ = v_x_162_;
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_i_163_);
lean_dec(v_x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_stx_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v_stx_167_ = lean_ctor_get(v_i_163_, 0);
lean_inc(v_stx_167_);
lean_dec_ref(v_i_163_);
v___x_168_ = 0;
v___x_169_ = l_Lean_Syntax_getRange_x3f(v_stx_167_, v___x_168_);
lean_dec(v_stx_167_);
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 1);
lean_ctor_set(v___x_165_, 0, v_range_161_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_range_161_);
v___x_171_ = v_reuseFailAlloc_173_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
uint8_t v___x_172_; 
v___x_172_ = l_instBEqOption_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v___x_169_, v___x_171_);
lean_dec_ref(v___x_171_);
lean_dec(v___x_169_);
return v___x_172_;
}
}
}
else
{
uint8_t v___x_175_; 
lean_dec_ref(v_x_162_);
lean_dec_ref(v_range_161_);
v___x_175_ = 0;
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed(lean_object* v_range_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lean_Fmt_findChoiceResolution_x3f___lam__0(v_range_176_, v_x_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object* v_infoTree_180_, lean_object* v_range_181_){
_start:
{
lean_object* v___f_182_; lean_object* v___x_183_; 
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_182_, 0, v_range_181_);
v___x_183_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_182_, v_infoTree_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_194_; 
v_val_185_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_194_ == 0)
{
v___x_187_ = v___x_183_;
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_val_185_);
lean_dec(v___x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
if (lean_obj_tag(v_val_185_) == 15)
{
lean_object* v_i_189_; lean_object* v___x_191_; 
v_i_189_ = lean_ctor_get(v_val_185_, 0);
lean_inc_ref(v_i_189_);
lean_dec_ref_known(v_val_185_, 1);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_i_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_i_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_193_; 
lean_del_object(v___x_187_);
lean_dec(v_val_185_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___impl(uint8_t v_x_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_box(v_x_195_);
v___x_197_ = lean_obj_tag_nat(v___x_196_);
lean_dec(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___impl___boxed(lean_object* v_x_198_){
_start:
{
uint8_t v_x_4__boxed_199_; lean_object* v_res_200_; 
v_x_4__boxed_199_ = lean_unbox(v_x_198_);
v_res_200_ = l_Lean_Fmt_RangeKind_ctorIdx___impl(v_x_4__boxed_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg(lean_object* v_k_201_){
_start:
{
lean_inc(v_k_201_);
return v_k_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg___boxed(lean_object* v_k_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Fmt_RangeKind_ctorElim___redArg(v_k_202_);
lean_dec(v_k_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim(lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, uint8_t v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_inc(v_k_208_);
return v_k_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___boxed(lean_object* v_motive_209_, lean_object* v_ctorIdx_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_k_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lean_Fmt_RangeKind_ctorElim(v_motive_209_, v_ctorIdx_210_, v_t_boxed_214_, v_h_212_, v_k_213_);
lean_dec(v_k_213_);
lean_dec(v_ctorIdx_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg(lean_object* v_whitespace_216_){
_start:
{
lean_inc(v_whitespace_216_);
return v_whitespace_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg___boxed(lean_object* v_whitespace_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Fmt_RangeKind_whitespace_elim___redArg(v_whitespace_217_);
lean_dec(v_whitespace_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_whitespace_222_){
_start:
{
lean_inc(v_whitespace_222_);
return v_whitespace_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_whitespace_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_Fmt_RangeKind_whitespace_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_whitespace_226_);
lean_dec(v_whitespace_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg(lean_object* v_node_229_){
_start:
{
lean_inc(v_node_229_);
return v_node_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg___boxed(lean_object* v_node_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Fmt_RangeKind_node_elim___redArg(v_node_230_);
lean_dec(v_node_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_node_235_){
_start:
{
lean_inc(v_node_235_);
return v_node_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_node_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_Fmt_RangeKind_node_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_node_239_);
lean_dec(v_node_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg(lean_object* v_text_242_){
_start:
{
lean_inc(v_text_242_);
return v_text_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg___boxed(lean_object* v_text_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Fmt_RangeKind_text_elim___redArg(v_text_243_);
lean_dec(v_text_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_text_248_){
_start:
{
lean_inc(v_text_248_);
return v_text_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_text_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_Fmt_RangeKind_text_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_text_252_);
lean_dec(v_text_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___redArg(lean_object* v_raw_255_){
_start:
{
lean_inc(v_raw_255_);
return v_raw_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___redArg___boxed(lean_object* v_raw_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Fmt_RangeKind_raw_elim___redArg(v_raw_256_);
lean_dec(v_raw_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_raw_261_){
_start:
{
lean_inc(v_raw_261_);
return v_raw_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_raw_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_raw_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_Fmt_RangeKind_raw_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_raw_265_);
lean_dec(v_raw_265_);
return v_res_267_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind_default(void){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = 0;
return v___x_268_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind(void){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = 0;
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_unsigned_to_nat(16u);
v___x_272_ = lean_mk_array(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default(void){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Lean_ShareCommon_objectFactory;
v___x_279_ = l___private_Init_ShareCommon_0__ShareCommon_Internal_mkStateImpl(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__0, &l_Lean_Fmt_instInhabitedState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__0);
v___x_283_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
v___x_284_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
lean_ctor_set(v___x_284_, 2, v___x_281_);
lean_ctor_set(v___x_284_, 3, v___x_280_);
lean_ctor_set(v___x_284_, 4, v___x_280_);
lean_ctor_set(v___x_284_, 5, v___x_280_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__1, &l_Lean_Fmt_instInhabitedState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__1);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Fmt_instInhabitedState_default;
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object* v_s_287_){
_start:
{
lean_object* v_toBacktrackableState_288_; 
v_toBacktrackableState_288_ = lean_ctor_get(v_s_287_, 0);
lean_inc_ref(v_toBacktrackableState_288_);
return v_toBacktrackableState_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object* v_s_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(v_s_289_);
lean_dec_ref(v_s_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object* v_s_291_, lean_object* v_d_292_){
_start:
{
lean_object* v_shareCommonState_293_; lean_object* v_freshTagId_294_; lean_object* v_missingFormatters_295_; lean_object* v_partialFormatters_296_; lean_object* v_missingChoiceResolutions_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_shareCommonState_293_ = lean_ctor_get(v_s_291_, 1);
v_freshTagId_294_ = lean_ctor_get(v_s_291_, 2);
v_missingFormatters_295_ = lean_ctor_get(v_s_291_, 3);
v_partialFormatters_296_ = lean_ctor_get(v_s_291_, 4);
v_missingChoiceResolutions_297_ = lean_ctor_get(v_s_291_, 5);
v_isSharedCheck_304_ = !lean_is_exclusive(v_s_291_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_s_291_, 0);
lean_dec(v_unused_305_);
v___x_299_ = v_s_291_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_missingChoiceResolutions_297_);
lean_inc(v_partialFormatters_296_);
lean_inc(v_missingFormatters_295_);
lean_inc(v_freshTagId_294_);
lean_inc(v_shareCommonState_293_);
lean_dec(v_s_291_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v_d_292_);
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_d_292_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_shareCommonState_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_freshTagId_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_missingFormatters_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_partialFormatters_296_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_missingChoiceResolutions_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object* v_entry_317_, lean_object* v_as_318_, lean_object* v_j_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_array_get_size(v_as_318_);
v___x_321_ = lean_nat_dec_lt(v_j_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_j_319_);
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v_priority_324_; lean_object* v_priority_325_; uint8_t v___x_326_; 
v___x_323_ = lean_array_fget_borrowed(v_as_318_, v_j_319_);
v_priority_324_ = lean_ctor_get(v___x_323_, 0);
v_priority_325_ = lean_ctor_get(v_entry_317_, 0);
v___x_326_ = lean_nat_dec_lt(v_priority_324_, v_priority_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_j_319_, v___x_327_);
lean_dec(v_j_319_);
v_j_319_ = v___x_328_;
goto _start;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_j_319_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object* v_entry_331_, lean_object* v_as_332_, lean_object* v_j_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_331_, v_as_332_, v_j_333_);
lean_dec_ref(v_as_332_);
lean_dec_ref(v_entry_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object* v_providers_335_, lean_object* v_entry_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_336_, v_providers_335_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_array_get_size(v_providers_335_);
v___x_340_ = l_Array_insertIdx_x21___redArg(v_providers_335_, v___x_339_, v_entry_336_);
return v___x_340_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_342_; 
v_val_341_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_338_, 1);
v___x_342_ = l_Array_insertIdx_x21___redArg(v_providers_335_, v_val_341_, v_entry_336_);
lean_dec(v_val_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_));
v___x_347_ = lean_st_mk_ref(v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object* v_priority_351_, lean_object* v_provider_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_354_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_355_ = lean_st_ref_take(v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v_priority_351_);
lean_ctor_set(v___x_356_, 1, v_provider_352_);
v___x_357_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v___x_355_, v___x_356_);
v___x_358_ = lean_st_ref_put(v___x_354_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object* v_priority_360_, lean_object* v_provider_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Fmt_addBuiltinFmtProvider(v_priority_360_, v_provider_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object* v_constName_371_, lean_object* v_env_372_, lean_object* v_opts_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
v___x_375_ = l_Lean_Environment_evalConstCheck___redArg(v_env_372_, v_opts_373_, v___x_374_, v_constName_371_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object* v_constName_376_, lean_object* v_env_377_, lean_object* v_opts_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(v_constName_376_, v_env_377_, v_opts_378_);
lean_dec_ref(v_opts_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object* v_e_380_){
_start:
{
if (lean_obj_tag(v_e_380_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v_e_380_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_e_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v_e_380_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v_e_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_mk_io_user_error(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 1);
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v_e_380_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_e_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v_e_380_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v_e_380_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 0);
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object* v_e_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object* v_00_u03b1_402_, lean_object* v_e_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object* v_00_u03b1_406_, lean_object* v_e_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(v_00_u03b1_406_, v_e_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object* v_constName_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_env_413_; lean_object* v_opts_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_env_413_ = lean_ctor_get(v_a_411_, 0);
v_opts_414_ = lean_ctor_get(v_a_411_, 1);
v___x_415_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
lean_inc_ref(v_env_413_);
v___x_416_ = l_Lean_Environment_evalConstCheck___redArg(v_env_413_, v_opts_414_, v___x_415_, v_constName_410_);
v___x_417_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object* v_constName_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_constName_418_, v_a_419_);
lean_dec_ref(v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_422_){
_start:
{
lean_object* v_fst_423_; 
v_fst_423_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_fst_423_);
return v_fst_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_424_);
lean_dec_ref(v_x_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_428_);
lean_dec_ref(v_x_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_430_, lean_object* v_s_431_){
_start:
{
lean_object* v_fst_432_; lean_object* v___x_433_; 
v_fst_432_ = lean_ctor_get(v_s_431_, 0);
lean_inc_n(v_fst_432_, 3);
v___x_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_433_, 0, v_fst_432_);
lean_ctor_set(v___x_433_, 1, v_fst_432_);
lean_ctor_set(v___x_433_, 2, v_fst_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_434_, lean_object* v_s_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_434_, v_s_435_);
lean_dec_ref(v_s_435_);
lean_dec_ref(v_x_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_snd_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_460_; 
v_snd_439_ = lean_ctor_get(v_x_438_, 1);
lean_inc(v_snd_439_);
v_fst_440_ = lean_ctor_get(v_x_437_, 0);
v_snd_441_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_460_ == 0)
{
v___x_443_ = v_x_437_;
v_isShared_444_ = v_isSharedCheck_460_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_inc(v_fst_440_);
lean_dec(v_x_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_460_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_fst_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_458_; 
v_fst_445_ = lean_ctor_get(v_x_438_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v_x_438_, 1);
lean_dec(v_unused_459_);
v___x_447_ = v_x_438_;
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_fst_445_);
lean_dec(v_x_438_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_priority_449_; lean_object* v___x_451_; 
v_priority_449_ = lean_ctor_get(v_snd_439_, 0);
lean_inc(v_priority_449_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_priority_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_priority_449_);
v___x_451_ = v_reuseFailAlloc_457_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_array_push(v_fst_440_, v___x_451_);
v___x_453_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_snd_441_, v_snd_439_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_453_);
lean_ctor_set(v___x_443_, 0, v___x_452_);
v___x_455_ = v___x_443_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_461_, lean_object* v___x_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_st_ref_get(v___x_461_);
v___x_465_ = lean_mk_empty_array_with_capacity(v___x_462_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_468_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(lean_object* v_as_472_, size_t v_i_473_, size_t v_stop_474_, lean_object* v_b_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_eq(v_i_473_, v_stop_474_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_502_; 
v___x_479_ = lean_array_uget(v_as_472_, v_i_473_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
v_snd_481_ = lean_ctor_get(v___x_479_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_502_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_502_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_inc(v_fst_480_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_502_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_fst_480_, v___y_476_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_a_486_);
lean_ctor_set(v___x_483_, 0, v_snd_481_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_snd_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_486_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; 
v___x_489_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_b_475_, v___x_488_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_473_, v___x_490_);
v_i_473_ = v___x_491_;
v_b_475_ = v___x_489_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_483_);
lean_dec(v_snd_481_);
lean_dec_ref(v_b_475_);
v_a_494_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_485_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_485_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v_b_475_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
size_t v_i_boxed_510_; size_t v_stop_boxed_511_; lean_object* v_res_512_; 
v_i_boxed_510_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_511_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v_as_504_, v_i_boxed_510_, v_stop_boxed_511_, v_b_507_, v___y_508_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_as_504_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(lean_object* v_as_513_, size_t v_i_514_, size_t v_stop_515_, lean_object* v_b_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_a_520_; uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_514_, v_stop_515_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_array_uget_borrowed(v_as_513_, v_i_514_);
v___x_527_ = lean_array_get_size(v___x_526_);
v___x_528_ = lean_nat_dec_lt(v___x_525_, v___x_527_);
if (v___x_528_ == 0)
{
v_a_520_ = v_b_516_;
goto v___jp_519_;
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v___x_526_, v___x_529_, v___x_530_, v_b_516_, v___y_517_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v_a_520_ = v_a_532_;
goto v___jp_519_;
}
else
{
return v___x_531_;
}
}
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_b_516_);
return v___x_533_;
}
v___jp_519_:
{
size_t v___x_521_; size_t v___x_522_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_514_, v___x_521_);
v_i_514_ = v___x_522_;
v_b_516_ = v_a_520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_534_, lean_object* v_i_535_, lean_object* v_stop_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
size_t v_i_boxed_540_; size_t v_stop_boxed_541_; lean_object* v_res_542_; 
v_i_boxed_540_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_stop_boxed_541_ = lean_unbox_usize(v_stop_536_);
lean_dec(v_stop_536_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_534_, v_i_boxed_540_, v_stop_boxed_541_, v_b_537_, v___y_538_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_as_534_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_as_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_a_549_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_st_ref_get(v___x_544_);
v___x_554_ = lean_array_get_size(v_as_545_);
v___x_555_ = lean_nat_dec_lt(v___x_543_, v___x_554_);
if (v___x_555_ == 0)
{
v_a_549_ = v___x_553_;
goto v___jp_548_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_545_, v___x_556_, v___x_557_, v___x_553_, v___y_546_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v_a_549_ = v_a_559_;
goto v___jp_548_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_558_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_558_);
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
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_mk_empty_array_with_capacity(v___x_543_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_549_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_as_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_568_, v___x_569_, v_as_570_, v___y_571_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_570_);
lean_dec(v___x_569_);
lean_dec(v___x_568_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___f_611_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___f_611_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_611_, 0, v___x_610_);
lean_closure_set(v___f_611_, 1, v___x_609_);
return v___f_611_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___f_614_; 
v___x_612_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_613_ = lean_unsigned_to_nat(0u);
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_614_, 0, v___x_613_);
lean_closure_set(v___f_614_, 1, v___x_612_);
return v___f_614_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_615_ = 0;
v___x_616_ = lean_box(0);
v___x_617_ = lean_box(2);
v___f_618_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_619_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_620_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_621_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___f_622_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_623_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_624_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___f_622_);
lean_ctor_set(v___x_624_, 2, v___f_621_);
lean_ctor_set(v___x_624_, 3, v___f_620_);
lean_ctor_set(v___x_624_, 4, v___f_619_);
lean_ctor_set(v___x_624_, 5, v___f_618_);
lean_ctor_set(v___x_624_, 6, v___x_617_);
lean_ctor_set(v___x_624_, 7, v___x_616_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*8, v___x_615_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*8 + 1, v___x_615_);
return v___x_624_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___f_625_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_626_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___f_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_630_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_();
return v_res_632_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__0(void){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Array_instInhabited___redArg();
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__1(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__0, &l_Lean_Fmt_getFmtProviders___closed__0_once, _init_l_Lean_Fmt_getFmtProviders___closed__0);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object* v_env_636_){
_start:
{
lean_object* v___x_637_; lean_object* v_toEnvExtension_638_; lean_object* v_asyncMode_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; 
v___x_637_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_638_ = lean_ctor_get(v___x_637_, 0);
v_asyncMode_639_ = lean_ctor_get(v_toEnvExtension_638_, 2);
v___x_640_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_641_ = lean_box(0);
v___x_642_ = 0;
v___x_643_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_640_, v___x_637_, v_env_636_, v_asyncMode_639_, v___x_641_, v___x_642_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_644_);
lean_dec(v___x_643_);
return v_snd_644_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_645_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v_nextMacroScope_654_; lean_object* v_ngen_655_; lean_object* v_auxDeclNGen_656_; lean_object* v_traceState_657_; lean_object* v_recordedDeps_658_; lean_object* v_messages_659_; lean_object* v_infoState_660_; lean_object* v_snapshotTasks_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v___x_653_ = lean_st_ref_take(v___y_651_);
v_nextMacroScope_654_ = lean_ctor_get(v___x_653_, 1);
v_ngen_655_ = lean_ctor_get(v___x_653_, 2);
v_auxDeclNGen_656_ = lean_ctor_get(v___x_653_, 3);
v_traceState_657_ = lean_ctor_get(v___x_653_, 4);
v_recordedDeps_658_ = lean_ctor_get(v___x_653_, 6);
v_messages_659_ = lean_ctor_get(v___x_653_, 7);
v_infoState_660_ = lean_ctor_get(v___x_653_, 8);
v_snapshotTasks_661_ = lean_ctor_get(v___x_653_, 9);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_673_ = lean_ctor_get(v___x_653_, 5);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v___x_653_, 0);
lean_dec(v_unused_674_);
v___x_663_ = v___x_653_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snapshotTasks_661_);
lean_inc(v_infoState_660_);
lean_inc(v_messages_659_);
lean_inc(v_recordedDeps_658_);
lean_inc(v_traceState_657_);
lean_inc(v_auxDeclNGen_656_);
lean_inc(v_ngen_655_);
lean_inc(v_nextMacroScope_654_);
lean_dec(v___x_653_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_box(0);
v___x_666_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 5, v___x_666_);
lean_ctor_set(v___x_663_, 0, v_env_650_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_env_650_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_nextMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_ngen_655_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_auxDeclNGen_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_traceState_657_);
lean_ctor_set(v_reuseFailAlloc_671_, 5, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_671_, 6, v_recordedDeps_658_);
lean_ctor_set(v_reuseFailAlloc_671_, 7, v_messages_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 8, v_infoState_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 9, v_snapshotTasks_661_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_st_ref_put(v___y_651_, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_665_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_675_, v___y_676_);
lean_dec(v___y_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(lean_object* v_env_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_679_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(v_env_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v_addEntryFn_689_, lean_object* v___x_690_, lean_object* v_s_691_){
_start:
{
lean_object* v_importedEntries_692_; lean_object* v_state_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_importedEntries_692_ = lean_ctor_get(v_s_691_, 0);
v_state_693_ = lean_ctor_get(v_s_691_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_s_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_s_691_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_state_693_);
lean_inc(v_importedEntries_692_);
lean_dec(v_s_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_state_697_; lean_object* v___x_699_; 
v_state_697_ = lean_apply_2(v_addEntryFn_689_, v_state_693_, v___x_690_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_state_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_importedEntries_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_state_697_);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set(v___x_706_, 3, v___x_705_);
lean_ctor_set(v___x_706_, 4, v___x_704_);
lean_ctor_set(v___x_706_, 5, v___x_704_);
lean_ctor_set(v___x_706_, 6, v___x_704_);
lean_ctor_set(v___x_706_, 7, v___x_704_);
lean_ctor_set(v___x_706_, 8, v___x_704_);
lean_ctor_set(v___x_706_, 9, v___x_704_);
lean_ctor_set(v___x_706_, 10, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_unsigned_to_nat(32u);
v___x_708_ = lean_mk_empty_array_with_capacity(v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_710_ = ((size_t)5ULL);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_unsigned_to_nat(32u);
v___x_713_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_714_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_715_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_711_);
lean_ctor_set(v___x_715_, 3, v___x_711_);
lean_ctor_set_usize(v___x_715_, 4, v___x_710_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_box(1);
v___x_717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_718_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_toCold_725_; lean_object* v_env_726_; lean_object* v_options_727_; uint8_t v___x_728_; lean_object* v_env_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_toCold_725_ = lean_ctor_get(v___y_721_, 0);
v_env_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_724_);
v_options_727_ = lean_ctor_get(v_toCold_725_, 2);
v___x_728_ = 0;
v_env_729_ = l_Lean_Environment_setRecordingDeps(v_env_726_, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_731_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_727_);
v___x_732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_732_, 0, v_env_729_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
lean_ctor_set(v___x_732_, 3, v_options_727_);
v___x_733_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_msgData_720_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msgData_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_ref_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_ref_744_ = lean_ctor_get(v___y_741_, 2);
v___x_745_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_740_, v___y_741_, v___y_742_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
lean_inc(v_ref_744_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_ref_744_);
lean_ctor_set(v___x_750_, 1, v_a_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 1);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_toCold_765_; lean_object* v_currRecDepth_766_; lean_object* v_ref_767_; uint16_t v_optionFlags_768_; uint8_t v_suppressElabErrors_769_; uint8_t v_checkDeprecated_770_; uint8_t v_isRecordingDeps_771_; lean_object* v_ref_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_toCold_765_ = lean_ctor_get(v___y_762_, 0);
v_currRecDepth_766_ = lean_ctor_get(v___y_762_, 1);
v_ref_767_ = lean_ctor_get(v___y_762_, 2);
v_optionFlags_768_ = lean_ctor_get_uint16(v___y_762_, sizeof(void*)*3);
v_suppressElabErrors_769_ = lean_ctor_get_uint8(v___y_762_, sizeof(void*)*3 + 2);
v_checkDeprecated_770_ = lean_ctor_get_uint8(v___y_762_, sizeof(void*)*3 + 3);
v_isRecordingDeps_771_ = lean_ctor_get_uint8(v___y_762_, sizeof(void*)*3 + 4);
v_ref_772_ = l_Lean_replaceRef(v_ref_760_, v_ref_767_);
lean_inc(v_currRecDepth_766_);
lean_inc_ref(v_toCold_765_);
v___x_773_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_773_, 0, v_toCold_765_);
lean_ctor_set(v___x_773_, 1, v_currRecDepth_766_);
lean_ctor_set(v___x_773_, 2, v_ref_772_);
lean_ctor_set_uint16(v___x_773_, sizeof(void*)*3, v_optionFlags_768_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 2, v_suppressElabErrors_769_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 3, v_checkDeprecated_770_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 4, v_isRecordingDeps_771_);
v___x_774_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_761_, v___x_773_, v___y_763_);
lean_dec_ref_known(v___x_773_, 3);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_775_, lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_775_, v_msg_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v_ref_775_);
return v_res_780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_814_, lean_object* v_declHint_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_env_820_; uint8_t v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_st_ref_get(v___y_816_);
v_env_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_env_820_);
lean_dec(v___x_819_);
v___x_821_ = l_Lean_Name_isAnonymous(v_declHint_815_);
if (v___x_821_ == 0)
{
uint8_t v_isExporting_822_; 
v_isExporting_822_ = lean_ctor_get_uint8(v_env_820_, sizeof(void*)*13);
if (v_isExporting_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v_msg_814_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
lean_inc_ref(v_env_820_);
v___x_824_ = l_Lean_Environment_setExporting(v_env_820_, v___x_821_);
lean_inc(v_declHint_815_);
lean_inc_ref(v___x_824_);
v___x_825_ = l_Lean_Environment_contains(v___x_824_, v_declHint_815_, v_isExporting_822_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v___x_824_);
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_msg_814_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_c_832_; lean_object* v___x_833_; 
v___x_827_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_828_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_829_ = l_Lean_Options_empty;
lean_inc_ref(v___x_824_);
v___x_830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_830_, 0, v___x_824_);
lean_ctor_set(v___x_830_, 1, v___x_827_);
lean_ctor_set(v___x_830_, 2, v___x_828_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_inc(v_declHint_815_);
v___x_831_ = l_Lean_MessageData_ofConstName(v_declHint_815_, v___x_821_);
v_c_832_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_832_, 0, v___x_830_);
lean_ctor_set(v_c_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_824_, v_declHint_815_);
lean_dec_ref(v___x_824_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_c_832_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_MessageData_note(v___x_837_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v_msg_814_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_894_; 
v_val_841_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_894_ == 0)
{
v___x_843_ = v___x_833_;
v_isShared_844_ = v_isSharedCheck_894_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_val_841_);
lean_dec(v___x_833_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_894_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_modules_846_; lean_object* v_moduleNames_847_; lean_object* v_mod_848_; uint8_t v___x_863_; 
v___x_845_ = l_Lean_Environment_header(v_env_820_);
lean_dec_ref(v_env_820_);
v_modules_846_ = lean_ctor_get(v___x_845_, 3);
lean_inc_ref(v_modules_846_);
v_moduleNames_847_ = lean_ctor_get(v___x_845_, 4);
lean_inc_ref(v_moduleNames_847_);
lean_dec_ref(v___x_845_);
v_mod_848_ = lean_array_get(v___x_818_, v_moduleNames_847_, v_val_841_);
lean_dec_ref(v_moduleNames_847_);
v___x_863_ = l_Lean_isPrivateName(v_declHint_815_);
lean_dec(v_declHint_815_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_array_get_size(v_modules_846_);
v___x_865_ = lean_nat_dec_lt(v_val_841_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_modules_846_);
lean_dec(v_val_841_);
goto v___jp_849_;
}
else
{
lean_object* v___x_866_; lean_object* v_toImport_867_; uint8_t v_isExported_868_; 
v___x_866_ = lean_array_fget(v_modules_846_, v_val_841_);
lean_dec(v_val_841_);
lean_dec_ref(v_modules_846_);
v_toImport_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_toImport_867_);
lean_dec(v___x_866_);
v_isExported_868_ = lean_ctor_get_uint8(v_toImport_867_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_867_);
if (v_isExported_868_ == 0)
{
goto v___jp_849_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_del_object(v___x_843_);
v___x_869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_c_832_);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MessageData_ofName(v_mod_848_);
lean_inc_ref(v___x_873_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_873_);
v___x_878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_MessageData_note(v___x_879_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v_msg_814_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_modules_846_);
lean_del_object(v___x_843_);
lean_dec(v_val_841_);
v___x_883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_c_832_);
v___x_885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_MessageData_ofName(v_mod_848_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_MessageData_note(v___x_890_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v_msg_814_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
v___jp_849_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_c_832_);
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_MessageData_ofName(v_mod_848_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_note(v___x_857_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v_msg_814_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_859_);
v___x_861_ = v___x_843_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec_ref(v_env_820_);
lean_dec(v_declHint_815_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_msg_814_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_896_, lean_object* v_declHint_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_896_, v_declHint_897_, v___y_898_);
lean_dec(v___y_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_901_, lean_object* v_declHint_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_916_; 
v___x_906_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_901_, v_declHint_902_, v___y_904_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_916_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = l_Lean_unknownIdentifierMessageTag;
v___x_912_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_a_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_917_, lean_object* v_declHint_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_917_, v_declHint_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_923_, lean_object* v_msg_924_, lean_object* v_declHint_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_931_; 
v___x_929_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_924_, v_declHint_925_, v___y_926_, v___y_927_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v___x_931_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_923_, v_a_930_, v___y_926_, v___y_927_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_932_, lean_object* v_msg_933_, lean_object* v_declHint_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_932_, v_msg_933_, v_declHint_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v_ref_932_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_945_, lean_object* v_constName_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_950_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_951_ = 0;
lean_inc(v_constName_946_);
v___x_952_ = l_Lean_MessageData_ofConstName(v_constName_946_, v___x_951_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_945_, v___x_955_, v_constName_946_, v___y_947_, v___y_948_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_957_, lean_object* v_constName_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_957_, v_constName_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v_ref_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_ref_967_; lean_object* v___x_968_; 
v_ref_967_ = lean_ctor_get(v___y_964_, 2);
v___x_968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_967_, v_constName_963_, v___y_964_, v___y_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(lean_object* v_constName_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v___x_980_ = 0;
lean_inc(v_constName_974_);
v___x_981_ = l_Lean_Environment_find_x3f(v_env_979_, v_constName_974_, v___x_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_974_, v___y_975_, v___y_976_);
return v___x_982_;
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_constName_974_);
v_val_983_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_981_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_val_983_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_constName_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_1005_, uint8_t v_kind_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___y_1016_; 
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_1011_ = l_Lean_MessageData_ofName(v_name_1005_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
switch(v_kind_1006_)
{
case 0:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___y_1016_ = v___x_1023_;
goto v___jp_1015_;
}
case 1:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5));
v___y_1016_ = v___x_1024_;
goto v___jp_1015_;
}
default: 
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_1016_ = v___x_1025_;
goto v___jp_1015_;
}
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc_ref(v___y_1016_);
v___x_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___y_1016_);
v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1014_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1021_, v___y_1007_, v___y_1008_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_1026_, lean_object* v_kind_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_kind_boxed_1031_; lean_object* v_res_1032_; 
v_kind_boxed_1031_ = lean_unbox(v_kind_1027_);
v_res_1032_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_1026_, v_kind_boxed_1031_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1032_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_1048_, lean_object* v_declName_1049_, lean_object* v_givenType_1050_, lean_object* v_expectedType_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1055_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_1056_ = l_Lean_MessageData_ofName(v_attrName_1048_);
lean_inc_ref(v___x_1056_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = 0;
v___x_1061_ = l_Lean_MessageData_ofConstName(v_declName_1049_, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1059_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_indentExpr(v_givenType_1050_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1056_);
v___x_1070_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_indentExpr(v_expectedType_1051_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1073_, v___y_1052_, v___y_1053_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_1075_, lean_object* v_declName_1076_, lean_object* v_givenType_1077_, lean_object* v_expectedType_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1075_, v_declName_1076_, v_givenType_1077_, v_expectedType_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_decl_1087_, lean_object* v_stx_1088_, uint8_t v_kind_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1088_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___x_1153_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
lean_inc(v_decl_1087_);
lean_inc(v___x_1086_);
v___x_1153_ = l_Lean_ensureAttrDeclIsMeta(v___x_1086_, v_decl_1087_, v_kind_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1153_) == 0)
{
uint8_t v___x_1154_; uint8_t v___x_1155_; 
lean_dec_ref_known(v___x_1153_, 1);
v___x_1154_ = 0;
v___x_1155_ = l_Lean_instBEqAttributeKind_beq(v_kind_1089_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v_a_1094_);
lean_dec(v_decl_1087_);
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec(v___x_1083_);
v___x_1156_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_1086_, v_kind_1089_, v___y_1090_, v___y_1091_);
return v___x_1156_;
}
else
{
v___y_1134_ = v___y_1090_;
v___y_1135_ = v___y_1091_;
goto v___jp_1133_;
}
}
else
{
lean_dec(v_a_1094_);
lean_dec(v_decl_1087_);
lean_dec(v___x_1086_);
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec(v___x_1083_);
return v___x_1153_;
}
v___jp_1095_:
{
lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v_ref_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1098_ = lean_st_ref_get(v___y_1097_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v_ref_1100_ = lean_ctor_get(v___y_1096_, 2);
v___x_1101_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1096_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_env_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_inc(v_decl_1087_);
v___x_1103_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_decl_1087_, v___x_1102_);
lean_dec_ref_known(v___x_1102_, 2);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_env_1107_; lean_object* v___x_1108_; lean_object* v_toEnvExtension_1109_; lean_object* v_addEntryFn_1110_; lean_object* v_asyncMode_1111_; uint8_t v_logWrites_1112_; lean_object* v___x_1113_; lean_object* v___f_1114_; uint8_t v___x_1115_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_a_1094_);
lean_ctor_set(v___x_1105_, 1, v_a_1104_);
v___x_1106_ = lean_st_ref_get(v___y_1097_);
v_env_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_env_1107_);
lean_dec(v___x_1106_);
v___x_1108_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_1109_ = lean_ctor_get(v___x_1108_, 0);
v_addEntryFn_1110_ = lean_ctor_get(v___x_1108_, 3);
v_asyncMode_1111_ = lean_ctor_get(v_toEnvExtension_1109_, 2);
v_logWrites_1112_ = lean_ctor_get_uint8(v_toEnvExtension_1109_, sizeof(void*)*6);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_decl_1087_);
lean_ctor_set(v___x_1113_, 1, v___x_1105_);
lean_inc(v_addEntryFn_1110_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1114_, 0, v_addEntryFn_1110_);
lean_closure_set(v___f_1114_, 1, v___x_1113_);
v___x_1115_ = 1;
if (v_logWrites_1112_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_inc_ref(v_toEnvExtension_1109_);
v___x_1116_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1109_, v_env_1107_, v___f_1114_, v_asyncMode_1111_, v___x_1083_, v___x_1115_);
v___x_1117_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1116_, v___y_1097_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_inc_ref_n(v_toEnvExtension_1109_, 2);
v___x_1118_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1109_, v_env_1107_);
lean_dec_ref(v_env_1107_);
v___x_1119_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1109_, v___x_1118_, v___f_1114_, v_asyncMode_1111_, v___x_1083_, v___x_1115_);
v___x_1120_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1119_, v___y_1097_);
return v___x_1120_;
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1094_);
lean_dec(v_decl_1087_);
lean_dec(v___x_1083_);
v_a_1121_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1123_ = v___x_1103_;
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1103_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1125_ = lean_io_error_to_string(v_a_1121_);
v___x_1126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_ofFormat(v___x_1126_);
lean_inc(v_ref_1100_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_ref_1100_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1128_);
v___x_1130_ = v___x_1123_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
v___jp_1133_:
{
lean_object* v___x_1136_; 
lean_inc(v_decl_1087_);
v___x_1136_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_1087_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = l_Lean_ConstantInfo_type(v_a_1137_);
lean_dec(v_a_1137_);
v___x_1139_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2));
v___x_1140_ = l_Lean_Name_mkStr3(v___x_1084_, v___x_1085_, v___x_1139_);
v___x_1141_ = l_Lean_Expr_isConstOf(v___x_1138_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_a_1094_);
lean_dec(v___x_1083_);
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Lean_mkConst(v___x_1140_, v___x_1142_);
v___x_1144_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_1086_, v_decl_1087_, v___x_1138_, v___x_1143_, v___y_1134_, v___y_1135_);
return v___x_1144_;
}
else
{
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1138_);
lean_dec(v___x_1086_);
v___y_1096_ = v___y_1134_;
v___y_1097_ = v___y_1135_;
goto v___jp_1095_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_a_1094_);
lean_dec(v_decl_1087_);
lean_dec(v___x_1086_);
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec(v___x_1083_);
v_a_1145_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1136_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1136_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_decl_1087_);
lean_dec(v___x_1086_);
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec(v___x_1083_);
v_a_1157_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1093_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1093_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_decl_1169_, lean_object* v_stx_1170_, lean_object* v_kind_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_kind_boxed_1175_; lean_object* v_res_1176_; 
v_kind_boxed_1175_ = lean_unbox(v_kind_1171_);
v_res_1176_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1165_, v___x_1166_, v___x_1167_, v___x_1168_, v_decl_1169_, v_stx_1170_, v_kind_boxed_1175_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1176_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1183_, lean_object* v_decl_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1189_ = l_Lean_MessageData_ofName(v___x_1183_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1192_, v___y_1185_, v___y_1186_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1194_, lean_object* v_decl_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1194_, v_decl_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v_decl_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1256_ = l_Lean_registerBuiltinAttribute(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(v_00_u03b1_1265_, v_msg_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1271_, lean_object* v_attrName_1272_, lean_object* v_declName_1273_, lean_object* v_givenType_1274_, lean_object* v_expectedType_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1272_, v_declName_1273_, v_givenType_1274_, v_expectedType_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_attrName_1281_, lean_object* v_declName_1282_, lean_object* v_givenType_1283_, lean_object* v_expectedType_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(v_00_u03b1_1280_, v_attrName_1281_, v_declName_1282_, v_givenType_1283_, v_expectedType_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1289_, lean_object* v_name_1290_, uint8_t v_kind_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_1290_, v_kind_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_name_1297_, lean_object* v_kind_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_kind_boxed_1302_; lean_object* v_res_1303_; 
v_kind_boxed_1302_ = lean_unbox(v_kind_1298_);
v_res_1303_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(v_00_u03b1_1296_, v_name_1297_, v_kind_boxed_1302_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1304_, lean_object* v_constName_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1310_, lean_object* v_constName_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1310_, v_constName_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1316_, lean_object* v_ref_1317_, lean_object* v_constName_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1317_, v_constName_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_ref_1324_, lean_object* v_constName_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1323_, v_ref_1324_, v_constName_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v_ref_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1330_, lean_object* v_ref_1331_, lean_object* v_msg_1332_, lean_object* v_declHint_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1331_, v_msg_1332_, v_declHint_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_ref_1339_, lean_object* v_msg_1340_, lean_object* v_declHint_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1338_, v_ref_1339_, v_msg_1340_, v_declHint_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v_ref_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1346_, lean_object* v_declHint_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1346_, v_declHint_1347_, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1352_, lean_object* v_declHint_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1352_, v_declHint_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1358_, lean_object* v_ref_1359_, lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1359_, v_msg_1360_, v___y_1361_, v___y_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_ref_1366_, lean_object* v_msg_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1365_, v_ref_1366_, v_msg_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v_ref_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(uint8_t v_x_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(v_x_1372_);
v___x_1374_ = lean_obj_tag_nat(v___x_1373_);
lean_dec(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl___boxed(lean_object* v_x_1375_){
_start:
{
uint8_t v_x_4__boxed_1376_; lean_object* v_res_1377_; 
v_x_4__boxed_1376_ = lean_unbox(v_x_1375_);
v_res_1377_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(v_x_4__boxed_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object* v_k_1378_){
_start:
{
lean_inc(v_k_1378_);
return v_k_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object* v_k_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(v_k_1379_);
lean_dec(v_k_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object* v_motive_1381_, lean_object* v_ctorIdx_1382_, uint8_t v_t_1383_, lean_object* v_h_1384_, lean_object* v_k_1385_){
_start:
{
lean_inc(v_k_1385_);
return v_k_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object* v_motive_1386_, lean_object* v_ctorIdx_1387_, lean_object* v_t_1388_, lean_object* v_h_1389_, lean_object* v_k_1390_){
_start:
{
uint8_t v_t_boxed_1391_; lean_object* v_res_1392_; 
v_t_boxed_1391_ = lean_unbox(v_t_1388_);
v_res_1392_ = l_Lean_Fmt_Comment_Whitespace_ctorElim(v_motive_1386_, v_ctorIdx_1387_, v_t_boxed_1391_, v_h_1389_, v_k_1390_);
lean_dec(v_k_1390_);
lean_dec(v_ctorIdx_1387_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object* v_leading_1393_){
_start:
{
lean_inc(v_leading_1393_);
return v_leading_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object* v_leading_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(v_leading_1394_);
lean_dec(v_leading_1394_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object* v_motive_1396_, uint8_t v_t_1397_, lean_object* v_h_1398_, lean_object* v_leading_1399_){
_start:
{
lean_inc(v_leading_1399_);
return v_leading_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object* v_motive_1400_, lean_object* v_t_1401_, lean_object* v_h_1402_, lean_object* v_leading_1403_){
_start:
{
uint8_t v_t_boxed_1404_; lean_object* v_res_1405_; 
v_t_boxed_1404_ = lean_unbox(v_t_1401_);
v_res_1405_ = l_Lean_Fmt_Comment_Whitespace_leading_elim(v_motive_1400_, v_t_boxed_1404_, v_h_1402_, v_leading_1403_);
lean_dec(v_leading_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object* v_trailing_1406_){
_start:
{
lean_inc(v_trailing_1406_);
return v_trailing_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object* v_trailing_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(v_trailing_1407_);
lean_dec(v_trailing_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object* v_motive_1409_, uint8_t v_t_1410_, lean_object* v_h_1411_, lean_object* v_trailing_1412_){
_start:
{
lean_inc(v_trailing_1412_);
return v_trailing_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object* v_motive_1413_, lean_object* v_t_1414_, lean_object* v_h_1415_, lean_object* v_trailing_1416_){
_start:
{
uint8_t v_t_boxed_1417_; lean_object* v_res_1418_; 
v_t_boxed_1417_ = lean_unbox(v_t_1414_);
v_res_1418_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim(v_motive_1413_, v_t_boxed_1417_, v_h_1415_, v_trailing_1416_);
lean_dec(v_trailing_1416_);
return v_res_1418_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default(void){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace(void){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = 0;
return v___x_1420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqWhitespace_beq(uint8_t v_x_1421_, uint8_t v_y_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1423_ = lean_box(v_x_1421_);
v___x_1424_ = lean_obj_tag_nat(v___x_1423_);
lean_dec(v___x_1423_);
v___x_1425_ = lean_box(v_y_1422_);
v___x_1426_ = lean_obj_tag_nat(v___x_1425_);
lean_dec(v___x_1425_);
v___x_1427_ = lean_nat_dec_eq(v___x_1424_, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed(lean_object* v_x_1428_, lean_object* v_y_1429_){
_start:
{
uint8_t v_x_24__boxed_1430_; uint8_t v_y_25__boxed_1431_; uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_x_24__boxed_1430_ = lean_unbox(v_x_1428_);
v_y_25__boxed_1431_ = lean_unbox(v_y_1429_);
v_res_1432_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_x_24__boxed_1430_, v_y_25__boxed_1431_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(2u);
v___x_1443_ = lean_nat_to_int(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_nat_to_int(v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t v_x_1446_, lean_object* v_prec_1447_){
_start:
{
lean_object* v___y_1449_; lean_object* v___y_1456_; 
if (v_x_1446_ == 0)
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(1024u);
v___x_1463_ = lean_nat_dec_le(v___x_1462_, v_prec_1447_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1449_ = v___x_1464_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1449_ = v___x_1465_;
goto v___jp_1448_;
}
}
else
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_unsigned_to_nat(1024u);
v___x_1467_ = lean_nat_dec_le(v___x_1466_, v_prec_1447_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1456_ = v___x_1468_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1456_ = v___x_1469_;
goto v___jp_1455_;
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1450_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1));
lean_inc(v___y_1449_);
v___x_1451_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = 0;
v___x_1453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*1, v___x_1452_);
v___x_1454_ = l_Repr_addAppParen(v___x_1453_, v_prec_1447_);
return v___x_1454_;
}
v___jp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3));
lean_inc(v___y_1456_);
v___x_1458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___y_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = 0;
v___x_1460_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*1, v___x_1459_);
v___x_1461_ = l_Repr_addAppParen(v___x_1460_, v_prec_1447_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object* v_x_1470_, lean_object* v_prec_1471_){
_start:
{
uint8_t v_x_117__boxed_1472_; lean_object* v_res_1473_; 
v_x_117__boxed_1472_ = lean_unbox(v_x_1470_);
v_res_1473_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_x_117__boxed_1472_, v_prec_1471_);
lean_dec(v_prec_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl(uint8_t v_x_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(v_x_1476_);
v___x_1478_ = lean_obj_tag_nat(v___x_1477_);
lean_dec(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl___boxed(lean_object* v_x_1479_){
_start:
{
uint8_t v_x_4__boxed_1480_; lean_object* v_res_1481_; 
v_x_4__boxed_1480_ = lean_unbox(v_x_1479_);
v_res_1481_ = l_Lean_Fmt_Comment_Placement_ctorIdx___impl(v_x_4__boxed_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object* v_k_1482_){
_start:
{
lean_inc(v_k_1482_);
return v_k_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object* v_k_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Fmt_Comment_Placement_ctorElim___redArg(v_k_1483_);
lean_dec(v_k_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object* v_motive_1485_, lean_object* v_ctorIdx_1486_, uint8_t v_t_1487_, lean_object* v_h_1488_, lean_object* v_k_1489_){
_start:
{
lean_inc(v_k_1489_);
return v_k_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object* v_motive_1490_, lean_object* v_ctorIdx_1491_, lean_object* v_t_1492_, lean_object* v_h_1493_, lean_object* v_k_1494_){
_start:
{
uint8_t v_t_boxed_1495_; lean_object* v_res_1496_; 
v_t_boxed_1495_ = lean_unbox(v_t_1492_);
v_res_1496_ = l_Lean_Fmt_Comment_Placement_ctorElim(v_motive_1490_, v_ctorIdx_1491_, v_t_boxed_1495_, v_h_1493_, v_k_1494_);
lean_dec(v_k_1494_);
lean_dec(v_ctorIdx_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object* v_afterToken_1497_){
_start:
{
lean_inc(v_afterToken_1497_);
return v_afterToken_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object* v_afterToken_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(v_afterToken_1498_);
lean_dec(v_afterToken_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object* v_motive_1500_, uint8_t v_t_1501_, lean_object* v_h_1502_, lean_object* v_afterToken_1503_){
_start:
{
lean_inc(v_afterToken_1503_);
return v_afterToken_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object* v_motive_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_afterToken_1507_){
_start:
{
uint8_t v_t_boxed_1508_; lean_object* v_res_1509_; 
v_t_boxed_1508_ = lean_unbox(v_t_1505_);
v_res_1509_ = l_Lean_Fmt_Comment_Placement_afterToken_elim(v_motive_1504_, v_t_boxed_1508_, v_h_1506_, v_afterToken_1507_);
lean_dec(v_afterToken_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object* v_onLineBeforeToken_1510_){
_start:
{
lean_inc(v_onLineBeforeToken_1510_);
return v_onLineBeforeToken_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object* v_onLineBeforeToken_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(v_onLineBeforeToken_1511_);
lean_dec(v_onLineBeforeToken_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object* v_motive_1513_, uint8_t v_t_1514_, lean_object* v_h_1515_, lean_object* v_onLineBeforeToken_1516_){
_start:
{
lean_inc(v_onLineBeforeToken_1516_);
return v_onLineBeforeToken_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object* v_motive_1517_, lean_object* v_t_1518_, lean_object* v_h_1519_, lean_object* v_onLineBeforeToken_1520_){
_start:
{
uint8_t v_t_boxed_1521_; lean_object* v_res_1522_; 
v_t_boxed_1521_ = lean_unbox(v_t_1518_);
v_res_1522_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(v_motive_1517_, v_t_boxed_1521_, v_h_1519_, v_onLineBeforeToken_1520_);
lean_dec(v_onLineBeforeToken_1520_);
return v_res_1522_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default(void){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement(void){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = 0;
return v___x_1524_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t v_x_1525_, uint8_t v_y_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1527_ = lean_box(v_x_1525_);
v___x_1528_ = lean_obj_tag_nat(v___x_1527_);
lean_dec(v___x_1527_);
v___x_1529_ = lean_box(v_y_1526_);
v___x_1530_ = lean_obj_tag_nat(v___x_1529_);
lean_dec(v___x_1529_);
v___x_1531_ = lean_nat_dec_eq(v___x_1528_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object* v_x_1532_, lean_object* v_y_1533_){
_start:
{
uint8_t v_x_24__boxed_1534_; uint8_t v_y_25__boxed_1535_; uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_x_24__boxed_1534_ = lean_unbox(v_x_1532_);
v_y_25__boxed_1535_ = lean_unbox(v_y_1533_);
v_res_1536_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_x_24__boxed_1534_, v_y_25__boxed_1535_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t v_x_1546_, lean_object* v_prec_1547_){
_start:
{
lean_object* v___y_1549_; lean_object* v___y_1556_; 
if (v_x_1546_ == 0)
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(1024u);
v___x_1563_ = lean_nat_dec_le(v___x_1562_, v_prec_1547_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1549_ = v___x_1564_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1549_ = v___x_1565_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_unsigned_to_nat(1024u);
v___x_1567_ = lean_nat_dec_le(v___x_1566_, v_prec_1547_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1556_ = v___x_1568_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1556_ = v___x_1569_;
goto v___jp_1555_;
}
}
v___jp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1550_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1));
lean_inc(v___y_1549_);
v___x_1551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___y_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = 0;
v___x_1553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*1, v___x_1552_);
v___x_1554_ = l_Repr_addAppParen(v___x_1553_, v_prec_1547_);
return v___x_1554_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1557_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3));
lean_inc(v___y_1556_);
v___x_1558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = 0;
v___x_1560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*1, v___x_1559_);
v___x_1561_ = l_Repr_addAppParen(v___x_1560_, v_prec_1547_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object* v_x_1570_, lean_object* v_prec_1571_){
_start:
{
uint8_t v_x_113__boxed_1572_; lean_object* v_res_1573_; 
v_x_113__boxed_1572_ = lean_unbox(v_x_1570_);
v_res_1573_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_x_113__boxed_1572_, v_prec_1571_);
lean_dec(v_prec_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl(uint8_t v_x_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_box(v_x_1576_);
v___x_1578_ = lean_obj_tag_nat(v___x_1577_);
lean_dec(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl___boxed(lean_object* v_x_1579_){
_start:
{
uint8_t v_x_4__boxed_1580_; lean_object* v_res_1581_; 
v_x_4__boxed_1580_ = lean_unbox(v_x_1579_);
v_res_1581_ = l_Lean_Fmt_Comment_Kind_ctorIdx___impl(v_x_4__boxed_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object* v_k_1582_){
_start:
{
lean_inc(v_k_1582_);
return v_k_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object* v_k_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Fmt_Comment_Kind_ctorElim___redArg(v_k_1583_);
lean_dec(v_k_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object* v_motive_1585_, lean_object* v_ctorIdx_1586_, uint8_t v_t_1587_, lean_object* v_h_1588_, lean_object* v_k_1589_){
_start:
{
lean_inc(v_k_1589_);
return v_k_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object* v_motive_1590_, lean_object* v_ctorIdx_1591_, lean_object* v_t_1592_, lean_object* v_h_1593_, lean_object* v_k_1594_){
_start:
{
uint8_t v_t_boxed_1595_; lean_object* v_res_1596_; 
v_t_boxed_1595_ = lean_unbox(v_t_1592_);
v_res_1596_ = l_Lean_Fmt_Comment_Kind_ctorElim(v_motive_1590_, v_ctorIdx_1591_, v_t_boxed_1595_, v_h_1593_, v_k_1594_);
lean_dec(v_k_1594_);
lean_dec(v_ctorIdx_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object* v_lineComment_1597_){
_start:
{
lean_inc(v_lineComment_1597_);
return v_lineComment_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object* v_lineComment_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(v_lineComment_1598_);
lean_dec(v_lineComment_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object* v_motive_1600_, uint8_t v_t_1601_, lean_object* v_h_1602_, lean_object* v_lineComment_1603_){
_start:
{
lean_inc(v_lineComment_1603_);
return v_lineComment_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object* v_motive_1604_, lean_object* v_t_1605_, lean_object* v_h_1606_, lean_object* v_lineComment_1607_){
_start:
{
uint8_t v_t_boxed_1608_; lean_object* v_res_1609_; 
v_t_boxed_1608_ = lean_unbox(v_t_1605_);
v_res_1609_ = l_Lean_Fmt_Comment_Kind_lineComment_elim(v_motive_1604_, v_t_boxed_1608_, v_h_1606_, v_lineComment_1607_);
lean_dec(v_lineComment_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object* v_blockComment_1610_){
_start:
{
lean_inc(v_blockComment_1610_);
return v_blockComment_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object* v_blockComment_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(v_blockComment_1611_);
lean_dec(v_blockComment_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object* v_motive_1613_, uint8_t v_t_1614_, lean_object* v_h_1615_, lean_object* v_blockComment_1616_){
_start:
{
lean_inc(v_blockComment_1616_);
return v_blockComment_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object* v_motive_1617_, lean_object* v_t_1618_, lean_object* v_h_1619_, lean_object* v_blockComment_1620_){
_start:
{
uint8_t v_t_boxed_1621_; lean_object* v_res_1622_; 
v_t_boxed_1621_ = lean_unbox(v_t_1618_);
v_res_1622_ = l_Lean_Fmt_Comment_Kind_blockComment_elim(v_motive_1617_, v_t_boxed_1621_, v_h_1619_, v_blockComment_1620_);
lean_dec(v_blockComment_1620_);
return v_res_1622_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = 0;
return v___x_1623_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind(void){
_start:
{
uint8_t v___x_1624_; 
v___x_1624_ = 0;
return v___x_1624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqKind_beq(uint8_t v_x_1625_, uint8_t v_y_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1627_ = lean_box(v_x_1625_);
v___x_1628_ = lean_obj_tag_nat(v___x_1627_);
lean_dec(v___x_1627_);
v___x_1629_ = lean_box(v_y_1626_);
v___x_1630_ = lean_obj_tag_nat(v___x_1629_);
lean_dec(v___x_1629_);
v___x_1631_ = lean_nat_dec_eq(v___x_1628_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqKind_beq___boxed(lean_object* v_x_1632_, lean_object* v_y_1633_){
_start:
{
uint8_t v_x_24__boxed_1634_; uint8_t v_y_25__boxed_1635_; uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_x_24__boxed_1634_ = lean_unbox(v_x_1632_);
v_y_25__boxed_1635_ = lean_unbox(v_y_1633_);
v_res_1636_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_x_24__boxed_1634_, v_y_25__boxed_1635_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t v_x_1646_, lean_object* v_prec_1647_){
_start:
{
lean_object* v___y_1649_; lean_object* v___y_1656_; 
if (v_x_1646_ == 0)
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_unsigned_to_nat(1024u);
v___x_1663_ = lean_nat_dec_le(v___x_1662_, v_prec_1647_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1649_ = v___x_1664_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1649_ = v___x_1665_;
goto v___jp_1648_;
}
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = lean_unsigned_to_nat(1024u);
v___x_1667_ = lean_nat_dec_le(v___x_1666_, v_prec_1647_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1656_ = v___x_1668_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1656_ = v___x_1669_;
goto v___jp_1655_;
}
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1650_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__1));
lean_inc(v___y_1649_);
v___x_1651_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = 0;
v___x_1653_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*1, v___x_1652_);
v___x_1654_ = l_Repr_addAppParen(v___x_1653_, v_prec_1647_);
return v___x_1654_;
}
v___jp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__3));
lean_inc(v___y_1656_);
v___x_1658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___y_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = 0;
v___x_1660_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set_uint8(v___x_1660_, sizeof(void*)*1, v___x_1659_);
v___x_1661_ = l_Repr_addAppParen(v___x_1660_, v_prec_1647_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object* v_x_1670_, lean_object* v_prec_1671_){
_start:
{
uint8_t v_x_113__boxed_1672_; lean_object* v_res_1673_; 
v_x_113__boxed_1672_ = lean_unbox(v_x_1670_);
v_res_1673_ = l_Lean_Fmt_Comment_instReprKind_repr(v_x_113__boxed_1672_, v_prec_1671_);
lean_dec(v_prec_1671_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default___closed__1(void){
_start:
{
uint8_t v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1678_ = 0;
v___x_1679_ = ((lean_object*)(l_Lean_Fmt_instInhabitedComment_default___closed__0));
v___x_1680_ = 0;
v___x_1681_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_1682_ = 0;
v___x_1683_ = 0;
v___x_1684_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1684_, 0, v___x_1681_);
lean_ctor_set(v___x_1684_, 1, v___x_1681_);
lean_ctor_set(v___x_1684_, 2, v___x_1679_);
lean_ctor_set_uint8(v___x_1684_, sizeof(void*)*3, v___x_1683_);
lean_ctor_set_uint8(v___x_1684_, sizeof(void*)*3 + 1, v___x_1682_);
lean_ctor_set_uint8(v___x_1684_, sizeof(void*)*3 + 2, v___x_1680_);
lean_ctor_set_uint8(v___x_1684_, sizeof(void*)*3 + 3, v___x_1678_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default(void){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l_Lean_Fmt_instInhabitedComment_default___closed__1, &l_Lean_Fmt_instInhabitedComment_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedComment_default___closed__1);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment(void){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Fmt_instInhabitedComment_default;
return v___x_1686_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(lean_object* v_xs_1687_, lean_object* v_ys_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v_zero_1690_; uint8_t v_isZero_1691_; 
v_zero_1690_ = lean_unsigned_to_nat(0u);
v_isZero_1691_ = lean_nat_dec_eq(v_x_1689_, v_zero_1690_);
if (v_isZero_1691_ == 1)
{
lean_dec(v_x_1689_);
return v_isZero_1691_;
}
else
{
lean_object* v_one_1692_; lean_object* v_n_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_one_1692_ = lean_unsigned_to_nat(1u);
v_n_1693_ = lean_nat_sub(v_x_1689_, v_one_1692_);
lean_dec(v_x_1689_);
v___x_1694_ = lean_array_fget_borrowed(v_xs_1687_, v_n_1693_);
v___x_1695_ = lean_array_fget_borrowed(v_ys_1688_, v_n_1693_);
v___x_1696_ = lean_string_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec(v_n_1693_);
return v___x_1696_;
}
else
{
v_x_1689_ = v_n_1693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg___boxed(lean_object* v_xs_1698_, lean_object* v_ys_1699_, lean_object* v_x_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1698_, v_ys_1699_, v_x_1700_);
lean_dec_ref(v_ys_1699_);
lean_dec_ref(v_xs_1698_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqComment_beq(lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
uint8_t v_kind_1705_; uint8_t v_placement_1706_; lean_object* v_originalTokenRange_1707_; lean_object* v_originalWhitespaceRange_1708_; uint8_t v_originalWhitespaceKind_1709_; lean_object* v_content_1710_; uint8_t v_emptyLineBefore_1711_; uint8_t v_kind_1712_; uint8_t v_placement_1713_; lean_object* v_originalTokenRange_1714_; lean_object* v_originalWhitespaceRange_1715_; uint8_t v_originalWhitespaceKind_1716_; lean_object* v_content_1717_; uint8_t v_emptyLineBefore_1718_; uint8_t v___x_1719_; 
v_kind_1705_ = lean_ctor_get_uint8(v_x_1703_, sizeof(void*)*3);
v_placement_1706_ = lean_ctor_get_uint8(v_x_1703_, sizeof(void*)*3 + 1);
v_originalTokenRange_1707_ = lean_ctor_get(v_x_1703_, 0);
v_originalWhitespaceRange_1708_ = lean_ctor_get(v_x_1703_, 1);
v_originalWhitespaceKind_1709_ = lean_ctor_get_uint8(v_x_1703_, sizeof(void*)*3 + 2);
v_content_1710_ = lean_ctor_get(v_x_1703_, 2);
v_emptyLineBefore_1711_ = lean_ctor_get_uint8(v_x_1703_, sizeof(void*)*3 + 3);
v_kind_1712_ = lean_ctor_get_uint8(v_x_1704_, sizeof(void*)*3);
v_placement_1713_ = lean_ctor_get_uint8(v_x_1704_, sizeof(void*)*3 + 1);
v_originalTokenRange_1714_ = lean_ctor_get(v_x_1704_, 0);
v_originalWhitespaceRange_1715_ = lean_ctor_get(v_x_1704_, 1);
v_originalWhitespaceKind_1716_ = lean_ctor_get_uint8(v_x_1704_, sizeof(void*)*3 + 2);
v_content_1717_ = lean_ctor_get(v_x_1704_, 2);
v_emptyLineBefore_1718_ = lean_ctor_get_uint8(v_x_1704_, sizeof(void*)*3 + 3);
v___x_1719_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_kind_1705_, v_kind_1712_);
if (v___x_1719_ == 0)
{
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_placement_1706_, v_placement_1713_);
if (v___x_1720_ == 0)
{
return v___x_1720_;
}
else
{
uint8_t v___x_1721_; 
v___x_1721_ = l_Lean_Syntax_instBEqRange_beq(v_originalTokenRange_1707_, v_originalTokenRange_1714_);
if (v___x_1721_ == 0)
{
return v___x_1721_;
}
else
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Lean_Syntax_instBEqRange_beq(v_originalWhitespaceRange_1708_, v_originalWhitespaceRange_1715_);
if (v___x_1722_ == 0)
{
return v___x_1722_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_originalWhitespaceKind_1709_, v_originalWhitespaceKind_1716_);
if (v___x_1723_ == 0)
{
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = lean_array_get_size(v_content_1710_);
v___x_1725_ = lean_array_get_size(v_content_1717_);
v___x_1726_ = lean_nat_dec_eq(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
return v___x_1726_;
}
else
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_content_1710_, v_content_1717_, v___x_1724_);
if (v___x_1727_ == 0)
{
return v___x_1727_;
}
else
{
if (v_emptyLineBefore_1718_ == 0)
{
if (v_emptyLineBefore_1711_ == 0)
{
return v___x_1727_;
}
else
{
return v_emptyLineBefore_1718_;
}
}
else
{
return v_emptyLineBefore_1711_;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqComment_beq___boxed(lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_res_1730_ = l_Lean_Fmt_instBEqComment_beq(v_x_1728_, v_x_1729_);
lean_dec_ref(v_x_1729_);
lean_dec_ref(v_x_1728_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(lean_object* v_xs_1732_, lean_object* v_ys_1733_, lean_object* v_hsz_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1732_, v_ys_1733_, v_x_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___boxed(lean_object* v_xs_1738_, lean_object* v_ys_1739_, lean_object* v_hsz_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(v_xs_1738_, v_ys_1739_, v_hsz_1740_, v_x_1741_, v_x_1742_);
lean_dec_ref(v_ys_1739_);
lean_dec_ref(v_xs_1738_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 0)
{
lean_dec(v_x_1747_);
return v_x_1748_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1762_; 
v_head_1750_ = lean_ctor_get(v_x_1749_, 0);
v_tail_1751_ = lean_ctor_get(v_x_1749_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1753_ = v_x_1749_;
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_x_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
lean_inc(v_x_1747_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 5);
lean_ctor_set(v___x_1753_, 1, v_x_1747_);
lean_ctor_set(v___x_1753_, 0, v_x_1748_);
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_x_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_x_1747_);
v___x_1756_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = l_String_quote(v_head_1750_);
v___x_1758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1756_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v_x_1748_ = v___x_1759_;
v_x_1749_ = v_tail_1751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
lean_dec(v_x_1763_);
return v_x_1764_;
}
else
{
lean_object* v_head_1766_; lean_object* v_tail_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1778_; 
v_head_1766_ = lean_ctor_get(v_x_1765_, 0);
v_tail_1767_ = lean_ctor_get(v_x_1765_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1765_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1769_ = v_x_1765_;
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_tail_1767_);
lean_inc(v_head_1766_);
lean_dec(v_x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
lean_inc(v_x_1763_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 5);
lean_ctor_set(v___x_1769_, 1, v_x_1763_);
lean_ctor_set(v___x_1769_, 0, v_x_1764_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_x_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_x_1763_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = l_String_quote(v_head_1766_);
v___x_1774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(v_x_1763_, v___x_1775_, v_tail_1767_);
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l_String_quote(v___y_1779_);
v___x_1781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v___x_1784_; 
lean_dec(v_x_1783_);
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
else
{
lean_object* v_tail_1785_; 
v_tail_1785_ = lean_ctor_get(v_x_1782_, 1);
if (lean_obj_tag(v_tail_1785_) == 0)
{
lean_object* v_head_1786_; lean_object* v___x_1787_; 
lean_dec(v_x_1783_);
v_head_1786_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_head_1786_);
lean_dec_ref_known(v_x_1782_, 2);
v___x_1787_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1786_);
return v___x_1787_;
}
else
{
lean_object* v_head_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc(v_tail_1785_);
v_head_1788_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_head_1788_);
lean_dec_ref_known(v_x_1782_, 2);
v___x_1789_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1788_);
v___x_1790_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(v_x_1783_, v___x_1789_, v_tail_1785_);
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object* v_xs_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_array_get_size(v_xs_1791_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1795_ = lean_array_to_list(v_xs_1791_);
v___x_1796_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_1797_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_1799_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1797_);
v___x_1801_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1798_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Std_Format_fill(v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
lean_dec_ref(v_xs_1791_);
v___x_1805_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_1805_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(8u);
v___x_1816_ = lean_nat_to_int(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_unsigned_to_nat(13u);
v___x_1821_ = lean_nat_to_int(v___x_1820_);
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_unsigned_to_nat(22u);
v___x_1826_ = lean_nat_to_int(v___x_1825_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_unsigned_to_nat(11u);
v___x_1837_ = lean_nat_to_int(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_unsigned_to_nat(19u);
v___x_1842_ = lean_nat_to_int(v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object* v_x_1843_){
_start:
{
uint8_t v_kind_1844_; uint8_t v_placement_1845_; lean_object* v_originalTokenRange_1846_; lean_object* v_originalWhitespaceRange_1847_; uint8_t v_originalWhitespaceKind_1848_; lean_object* v_content_1849_; uint8_t v_emptyLineBefore_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_kind_1844_ = lean_ctor_get_uint8(v_x_1843_, sizeof(void*)*3);
v_placement_1845_ = lean_ctor_get_uint8(v_x_1843_, sizeof(void*)*3 + 1);
v_originalTokenRange_1846_ = lean_ctor_get(v_x_1843_, 0);
lean_inc_ref(v_originalTokenRange_1846_);
v_originalWhitespaceRange_1847_ = lean_ctor_get(v_x_1843_, 1);
lean_inc_ref(v_originalWhitespaceRange_1847_);
v_originalWhitespaceKind_1848_ = lean_ctor_get_uint8(v_x_1843_, sizeof(void*)*3 + 2);
v_content_1849_ = lean_ctor_get(v_x_1843_, 2);
lean_inc_ref(v_content_1849_);
v_emptyLineBefore_1850_ = lean_ctor_get_uint8(v_x_1843_, sizeof(void*)*3 + 3);
lean_dec_ref(v_x_1843_);
v___x_1851_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_1852_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__3));
v___x_1853_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__4, &l_Lean_Fmt_instReprComment_repr___redArg___closed__4_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_Lean_Fmt_Comment_instReprKind_repr(v_kind_1844_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = 0;
v___x_1858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set_uint8(v___x_1858_, sizeof(void*)*1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1852_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_box(1);
v___x_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__6));
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1851_);
v___x_1867_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__7, &l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7);
v___x_1868_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_placement_1845_, v___x_1854_);
v___x_1869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set_uint8(v___x_1870_, sizeof(void*)*1, v___x_1857_);
v___x_1871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1866_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1860_);
v___x_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1862_);
v___x_1874_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__9));
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1851_);
v___x_1877_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_1878_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalTokenRange_1846_);
v___x_1879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*1, v___x_1857_);
v___x_1881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1876_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1860_);
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1862_);
v___x_1884_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__12));
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1851_);
v___x_1887_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_1888_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalWhitespaceRange_1847_);
v___x_1889_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*1, v___x_1857_);
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1886_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1860_);
v___x_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1862_);
v___x_1894_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__14));
v___x_1895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1851_);
v___x_1897_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_1898_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_originalWhitespaceKind_1848_, v___x_1854_);
v___x_1899_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*1, v___x_1857_);
v___x_1901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1896_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1860_);
v___x_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1862_);
v___x_1904_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__16));
v___x_1905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1851_);
v___x_1907_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__17, &l_Lean_Fmt_instReprComment_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17);
v___x_1908_ = l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(v_content_1849_);
v___x_1909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*1, v___x_1857_);
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1906_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___x_1860_);
v___x_1913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v___x_1862_);
v___x_1914_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__19));
v___x_1915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1851_);
v___x_1917_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__20, &l_Lean_Fmt_instReprComment_repr___redArg___closed__20_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__20);
v___x_1918_ = l_Bool_repr___redArg(v_emptyLineBefore_1850_);
v___x_1919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*1, v___x_1857_);
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_1923_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1921_);
v___x_1925_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1922_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*1, v___x_1857_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object* v_x_1929_, lean_object* v_prec_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Fmt_instReprComment_repr___redArg(v_x_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object* v_x_1932_, lean_object* v_prec_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Fmt_instReprComment_repr(v_x_1932_, v_prec_1933_);
lean_dec(v_prec_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object* v_entry_1937_, lean_object* v_as_1938_, lean_object* v_j_1939_){
_start:
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_array_get_size(v_as_1938_);
v___x_1941_ = lean_nat_dec_lt(v_j_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec(v_j_1939_);
v___x_1942_ = lean_box(0);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v_priority_1944_; lean_object* v_priority_1945_; uint8_t v___x_1946_; 
v___x_1943_ = lean_array_fget_borrowed(v_as_1938_, v_j_1939_);
v_priority_1944_ = lean_ctor_get(v___x_1943_, 0);
v_priority_1945_ = lean_ctor_get(v_entry_1937_, 0);
v___x_1946_ = lean_nat_dec_lt(v_priority_1944_, v_priority_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_j_1939_, v___x_1947_);
lean_dec(v_j_1939_);
v_j_1939_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_j_1939_);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object* v_entry_1951_, lean_object* v_as_1952_, lean_object* v_j_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1951_, v_as_1952_, v_j_1953_);
lean_dec_ref(v_as_1952_);
lean_dec_ref(v_entry_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object* v_collectors_1955_, lean_object* v_entry_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1956_, v_collectors_1955_, v___x_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_array_get_size(v_collectors_1955_);
v___x_1960_ = l_Array_insertIdx_x21___redArg(v_collectors_1955_, v___x_1959_, v_entry_1956_);
return v___x_1960_;
}
else
{
lean_object* v_val_1961_; lean_object* v___x_1962_; 
v_val_1961_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_val_1961_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1962_ = l_Array_insertIdx_x21___redArg(v_collectors_1955_, v_val_1961_, v_entry_1956_);
lean_dec(v_val_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_));
v___x_1967_ = lean_st_mk_ref(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object* v_priority_1971_, lean_object* v_collector_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1974_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_1975_ = lean_st_ref_take(v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_priority_1971_);
lean_ctor_set(v___x_1976_, 1, v_collector_1972_);
v___x_1977_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v___x_1975_, v___x_1976_);
v___x_1978_ = lean_st_ref_put(v___x_1974_, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object* v_priority_1980_, lean_object* v_collector_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Fmt_addBuiltinCommentCollector(v_priority_1980_, v_collector_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object* v_constName_1989_, lean_object* v_env_1990_, lean_object* v_opts_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
v___x_1993_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1990_, v_opts_1991_, v___x_1992_, v_constName_1989_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object* v_constName_1994_, lean_object* v_env_1995_, lean_object* v_opts_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(v_constName_1994_, v_env_1995_, v_opts_1996_);
lean_dec_ref(v_opts_1996_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object* v_constName_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_env_2001_; lean_object* v_opts_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_env_2001_ = lean_ctor_get(v_a_1999_, 0);
v_opts_2002_ = lean_ctor_get(v_a_1999_, 1);
v___x_2003_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
lean_inc_ref(v_env_2001_);
v___x_2004_ = l_Lean_Environment_evalConstCheck___redArg(v_env_2001_, v_opts_2002_, v___x_2003_, v_constName_1998_);
v___x_2005_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object* v_constName_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_constName_2006_, v_a_2007_);
lean_dec_ref(v_a_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_2010_){
_start:
{
lean_object* v_fst_2011_; 
v_fst_2011_ = lean_ctor_get(v_x_2010_, 0);
lean_inc(v_fst_2011_);
return v_fst_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_2012_);
lean_dec_ref(v_x_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_box(0);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_2016_);
lean_dec_ref(v_x_2016_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_2018_, lean_object* v_s_2019_){
_start:
{
lean_object* v_fst_2020_; lean_object* v___x_2021_; 
v_fst_2020_ = lean_ctor_get(v_s_2019_, 0);
lean_inc_n(v_fst_2020_, 3);
v___x_2021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2021_, 0, v_fst_2020_);
lean_ctor_set(v___x_2021_, 1, v_fst_2020_);
lean_ctor_set(v___x_2021_, 2, v_fst_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_2022_, lean_object* v_s_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_2022_, v_s_2023_);
lean_dec_ref(v_s_2023_);
lean_dec_ref(v_x_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v_snd_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2048_; 
v_snd_2027_ = lean_ctor_get(v_x_2026_, 1);
lean_inc(v_snd_2027_);
v_fst_2028_ = lean_ctor_get(v_x_2025_, 0);
v_snd_2029_ = lean_ctor_get(v_x_2025_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_2025_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2031_ = v_x_2025_;
v_isShared_2032_ = v_isSharedCheck_2048_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_x_2025_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2048_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fst_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2046_; 
v_fst_2033_ = lean_ctor_get(v_x_2026_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_x_2026_, 1);
lean_dec(v_unused_2047_);
v___x_2035_ = v_x_2026_;
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_fst_2033_);
lean_dec(v_x_2026_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_priority_2037_; lean_object* v___x_2039_; 
v_priority_2037_ = lean_ctor_get(v_snd_2027_, 0);
lean_inc(v_priority_2037_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_priority_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_fst_2033_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_priority_2037_);
v___x_2039_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2040_ = lean_array_push(v_fst_2028_, v___x_2039_);
v___x_2041_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_snd_2029_, v_snd_2027_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2041_);
lean_ctor_set(v___x_2031_, 0, v___x_2040_);
v___x_2043_ = v___x_2031_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2049_, lean_object* v___x_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_st_ref_get(v___x_2049_);
v___x_2053_ = lean_mk_empty_array_with_capacity(v___x_2050_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___x_2052_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2056_, lean_object* v___x_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2056_, v___x_2057_);
lean_dec(v___x_2057_);
lean_dec(v___x_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(lean_object* v_as_2060_, size_t v_i_2061_, size_t v_stop_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_eq(v_i_2061_, v_stop_2062_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2090_; 
v___x_2067_ = lean_array_uget(v_as_2060_, v_i_2061_);
v_fst_2068_ = lean_ctor_get(v___x_2067_, 0);
v_snd_2069_ = lean_ctor_get(v___x_2067_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2071_ = v___x_2067_;
v_isShared_2072_ = v_isSharedCheck_2090_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v___x_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2090_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; 
v___x_2073_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_fst_2068_, v___y_2064_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2074_);
lean_ctor_set(v___x_2071_, 0, v_snd_2069_);
v___x_2076_ = v___x_2071_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_snd_2069_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_a_2074_);
v___x_2076_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; 
v___x_2077_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_b_2063_, v___x_2076_);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2061_, v___x_2078_);
v_i_2061_ = v___x_2079_;
v_b_2063_ = v___x_2077_;
goto _start;
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_del_object(v___x_2071_);
lean_dec(v_snd_2069_);
lean_dec_ref(v_b_2063_);
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2073_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2073_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_b_2063_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_2092_, lean_object* v_i_2093_, lean_object* v_stop_2094_, lean_object* v_b_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
size_t v_i_boxed_2098_; size_t v_stop_boxed_2099_; lean_object* v_res_2100_; 
v_i_boxed_2098_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_stop_boxed_2099_ = lean_unbox_usize(v_stop_2094_);
lean_dec(v_stop_2094_);
v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v_as_2092_, v_i_boxed_2098_, v_stop_boxed_2099_, v_b_2095_, v___y_2096_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_as_2092_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(lean_object* v_as_2101_, size_t v_i_2102_, size_t v_stop_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_a_2108_; uint8_t v___x_2112_; 
v___x_2112_ = lean_usize_dec_eq(v_i_2102_, v_stop_2103_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = lean_array_uget_borrowed(v_as_2101_, v_i_2102_);
v___x_2115_ = lean_array_get_size(v___x_2114_);
v___x_2116_ = lean_nat_dec_lt(v___x_2113_, v___x_2115_);
if (v___x_2116_ == 0)
{
v_a_2108_ = v_b_2104_;
goto v___jp_2107_;
}
else
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2115_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v___x_2114_, v___x_2117_, v___x_2118_, v_b_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v_a_2108_ = v_a_2120_;
goto v___jp_2107_;
}
else
{
return v___x_2119_;
}
}
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_b_2104_);
return v___x_2121_;
}
v___jp_2107_:
{
size_t v___x_2109_; size_t v___x_2110_; 
v___x_2109_ = ((size_t)1ULL);
v___x_2110_ = lean_usize_add(v_i_2102_, v___x_2109_);
v_i_2102_ = v___x_2110_;
v_b_2104_ = v_a_2108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_2122_, lean_object* v_i_2123_, lean_object* v_stop_2124_, lean_object* v_b_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
size_t v_i_boxed_2128_; size_t v_stop_boxed_2129_; lean_object* v_res_2130_; 
v_i_boxed_2128_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_stop_boxed_2129_ = lean_unbox_usize(v_stop_2124_);
lean_dec(v_stop_2124_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2122_, v_i_boxed_2128_, v_stop_boxed_2129_, v_b_2125_, v___y_2126_);
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_as_2122_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v_as_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_a_2137_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = lean_st_ref_get(v___x_2132_);
v___x_2142_ = lean_array_get_size(v_as_2133_);
v___x_2143_ = lean_nat_dec_lt(v___x_2131_, v___x_2142_);
if (v___x_2143_ == 0)
{
v_a_2137_ = v___x_2141_;
goto v___jp_2136_;
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2142_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2133_, v___x_2144_, v___x_2145_, v___x_2141_, v___y_2134_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v_a_2137_ = v_a_2147_;
goto v___jp_2136_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2146_);
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
v___jp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_mk_empty_array_with_capacity(v___x_2131_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_a_2137_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v_as_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2156_, v___x_2157_, v_as_2158_, v___y_2159_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_as_2158_);
lean_dec(v___x_2157_);
lean_dec(v___x_2156_);
return v_res_2161_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___f_2172_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_2172_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_2172_, 0, v___x_2171_);
lean_closure_set(v___f_2172_, 1, v___x_2170_);
return v___f_2172_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___f_2175_; 
v___x_2173_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_2174_ = lean_unsigned_to_nat(0u);
v___f_2175_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_2175_, 0, v___x_2174_);
lean_closure_set(v___f_2175_, 1, v___x_2173_);
return v___f_2175_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2176_ = 0;
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_box(2);
v___f_2179_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2180_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2181_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2182_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___f_2183_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2185_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___f_2183_);
lean_ctor_set(v___x_2185_, 2, v___f_2182_);
lean_ctor_set(v___x_2185_, 3, v___f_2181_);
lean_ctor_set(v___x_2185_, 4, v___f_2180_);
lean_ctor_set(v___x_2185_, 5, v___f_2179_);
lean_ctor_set(v___x_2185_, 6, v___x_2178_);
lean_ctor_set(v___x_2185_, 7, v___x_2177_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*8, v___x_2176_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*8 + 1, v___x_2176_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___f_2186_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2187_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___f_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2191_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object* v_env_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v_toEnvExtension_2196_; lean_object* v_asyncMode_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v_snd_2202_; 
v___x_2195_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2196_ = lean_ctor_get(v___x_2195_, 0);
v_asyncMode_2197_ = lean_ctor_get(v_toEnvExtension_2196_, 2);
v___x_2198_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_2199_ = lean_box(0);
v___x_2200_ = 0;
v___x_2201_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2198_, v___x_2195_, v_env_2194_, v_asyncMode_2197_, v___x_2199_, v___x_2200_);
v_snd_2202_ = lean_ctor_get(v___x_2201_, 1);
lean_inc(v_snd_2202_);
lean_dec(v___x_2201_);
return v_snd_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v_addEntryFn_2203_, lean_object* v___x_2204_, lean_object* v_s_2205_){
_start:
{
lean_object* v_importedEntries_2206_; lean_object* v_state_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_importedEntries_2206_ = lean_ctor_get(v_s_2205_, 0);
v_state_2207_ = lean_ctor_get(v_s_2205_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_s_2205_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v_s_2205_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_state_2207_);
lean_inc(v_importedEntries_2206_);
lean_dec(v_s_2205_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_state_2211_; lean_object* v___x_2213_; 
v_state_2211_ = lean_apply_2(v_addEntryFn_2203_, v_state_2207_, v___x_2204_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v_state_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_importedEntries_2206_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_state_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v___x_2219_, lean_object* v_decl_2220_, lean_object* v_stx_2221_, uint8_t v_kind_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Attribute_Builtin_getPrio(v_stx_2221_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___x_2286_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
lean_inc(v_decl_2220_);
lean_inc(v___x_2219_);
v___x_2286_ = l_Lean_ensureAttrDeclIsMeta(v___x_2219_, v_decl_2220_, v_kind_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2286_) == 0)
{
uint8_t v___x_2287_; uint8_t v___x_2288_; 
lean_dec_ref_known(v___x_2286_, 1);
v___x_2287_ = 0;
v___x_2288_ = l_Lean_instBEqAttributeKind_beq(v_kind_2222_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_a_2227_);
lean_dec(v_decl_2220_);
lean_dec_ref(v___x_2218_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2216_);
v___x_2289_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_2219_, v_kind_2222_, v___y_2223_, v___y_2224_);
return v___x_2289_;
}
else
{
v___y_2267_ = v___y_2223_;
v___y_2268_ = v___y_2224_;
goto v___jp_2266_;
}
}
else
{
lean_dec(v_a_2227_);
lean_dec(v_decl_2220_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2216_);
return v___x_2286_;
}
v___jp_2228_:
{
lean_object* v___x_2231_; lean_object* v_env_2232_; lean_object* v_ref_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2231_ = lean_st_ref_get(v___y_2230_);
v_env_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc_ref(v_env_2232_);
lean_dec(v___x_2231_);
v_ref_2233_ = lean_ctor_get(v___y_2229_, 2);
v___x_2234_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2229_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_env_2232_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
lean_inc(v_decl_2220_);
v___x_2236_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_decl_2220_, v___x_2235_);
lean_dec_ref_known(v___x_2235_, 2);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v_env_2240_; lean_object* v___x_2241_; lean_object* v_toEnvExtension_2242_; lean_object* v_addEntryFn_2243_; lean_object* v_asyncMode_2244_; uint8_t v_logWrites_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; uint8_t v___x_2248_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2227_);
lean_ctor_set(v___x_2238_, 1, v_a_2237_);
v___x_2239_ = lean_st_ref_get(v___y_2230_);
v_env_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_ref(v_env_2240_);
lean_dec(v___x_2239_);
v___x_2241_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2242_ = lean_ctor_get(v___x_2241_, 0);
v_addEntryFn_2243_ = lean_ctor_get(v___x_2241_, 3);
v_asyncMode_2244_ = lean_ctor_get(v_toEnvExtension_2242_, 2);
v_logWrites_2245_ = lean_ctor_get_uint8(v_toEnvExtension_2242_, sizeof(void*)*6);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_decl_2220_);
lean_ctor_set(v___x_2246_, 1, v___x_2238_);
lean_inc(v_addEntryFn_2243_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_2247_, 0, v_addEntryFn_2243_);
lean_closure_set(v___f_2247_, 1, v___x_2246_);
v___x_2248_ = 1;
if (v_logWrites_2245_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_inc_ref(v_toEnvExtension_2242_);
v___x_2249_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2242_, v_env_2240_, v___f_2247_, v_asyncMode_2244_, v___x_2216_, v___x_2248_);
v___x_2250_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2249_, v___y_2230_);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_inc_ref_n(v_toEnvExtension_2242_, 2);
v___x_2251_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2242_, v_env_2240_);
lean_dec_ref(v_env_2240_);
v___x_2252_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2242_, v___x_2251_, v___f_2247_, v_asyncMode_2244_, v___x_2216_, v___x_2248_);
v___x_2253_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2252_, v___y_2230_);
return v___x_2253_;
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2227_);
lean_dec(v_decl_2220_);
lean_dec(v___x_2216_);
v_a_2254_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2256_ = v___x_2236_;
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2236_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2265_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2258_ = lean_io_error_to_string(v_a_2254_);
v___x_2259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
v___x_2260_ = l_Lean_MessageData_ofFormat(v___x_2259_);
lean_inc(v_ref_2233_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_ref_2233_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2261_);
v___x_2263_ = v___x_2256_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
v___jp_2266_:
{
lean_object* v___x_2269_; 
lean_inc(v_decl_2220_);
v___x_2269_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_2220_, v___y_2267_, v___y_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_ConstantInfo_type(v_a_2270_);
lean_dec(v_a_2270_);
v___x_2272_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0));
v___x_2273_ = l_Lean_Name_mkStr3(v___x_2217_, v___x_2218_, v___x_2272_);
v___x_2274_ = l_Lean_Expr_isConstOf(v___x_2271_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v_a_2227_);
lean_dec(v___x_2216_);
v___x_2275_ = lean_box(0);
v___x_2276_ = l_Lean_mkConst(v___x_2273_, v___x_2275_);
v___x_2277_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_2219_, v_decl_2220_, v___x_2271_, v___x_2276_, v___y_2267_, v___y_2268_);
return v___x_2277_;
}
else
{
lean_dec(v___x_2273_);
lean_dec_ref(v___x_2271_);
lean_dec(v___x_2219_);
v___y_2229_ = v___y_2267_;
v___y_2230_ = v___y_2268_;
goto v___jp_2228_;
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2227_);
lean_dec(v_decl_2220_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2216_);
v_a_2278_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2269_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2269_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_decl_2220_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2216_);
v_a_2290_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2226_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2226_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v___x_2298_, lean_object* v___x_2299_, lean_object* v___x_2300_, lean_object* v___x_2301_, lean_object* v_decl_2302_, lean_object* v_stx_2303_, lean_object* v_kind_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
uint8_t v_kind_boxed_2308_; lean_object* v_res_2309_; 
v_kind_boxed_2308_ = lean_unbox(v_kind_2304_);
v_res_2309_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(v___x_2298_, v___x_2299_, v___x_2300_, v___x_2301_, v_decl_2302_, v_stx_2303_, v_kind_boxed_2308_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2309_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = lean_unsigned_to_nat(3853185248u);
v___x_2311_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2312_ = l_Lean_Name_num___override(v___x_2311_, v___x_2310_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2314_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2315_ = l_Lean_Name_str___override(v___x_2314_, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2317_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2318_ = l_Lean_Name_str___override(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_unsigned_to_nat(2u);
v___x_2320_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2321_ = l_Lean_Name_num___override(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2333_ = 1;
v___x_2334_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2335_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2336_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2337_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2335_);
lean_ctor_set(v___x_2337_, 2, v___x_2334_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*3, v___x_2333_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___f_2338_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___f_2339_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2340_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___f_2339_);
lean_ctor_set(v___x_2341_, 2, v___f_2338_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2344_ = l_Lean_registerBuiltinAttribute(v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object* v_attr_2347_, lean_object* v_mk_2348_, lean_object* v_env_2349_, lean_object* v_kind_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v_attr_2347_, v_env_2349_, v_kind_2350_);
v___x_2352_ = l_List_head_x3f___redArg(v___x_2351_);
lean_dec(v___x_2351_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_dec_ref(v_mk_2348_);
v___x_2353_ = lean_box(0);
return v___x_2353_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2373_; 
v_val_2354_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2356_ = v___x_2352_;
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_val_2354_);
lean_dec(v___x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_toOLeanEntry_2358_; lean_object* v_value_2359_; lean_object* v_declName_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2371_; 
v_toOLeanEntry_2358_ = lean_ctor_get(v_val_2354_, 0);
lean_inc_ref(v_toOLeanEntry_2358_);
v_value_2359_ = lean_ctor_get(v_val_2354_, 1);
lean_inc(v_value_2359_);
lean_dec(v_val_2354_);
v_declName_2360_ = lean_ctor_get(v_toOLeanEntry_2358_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_toOLeanEntry_2358_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; 
v_unused_2372_ = lean_ctor_get(v_toOLeanEntry_2358_, 0);
lean_dec(v_unused_2372_);
v___x_2362_ = v_toOLeanEntry_2358_;
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_declName_2360_);
lean_dec(v_toOLeanEntry_2358_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_apply_1(v_mk_2348_, v_value_2359_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2364_);
lean_ctor_set(v___x_2362_, 0, v_declName_2360_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_declName_2360_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2366_);
v___x_2368_ = v___x_2356_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object* v_attr_2374_, lean_object* v_mk_2375_, lean_object* v_env_2376_, lean_object* v_kind_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2374_, v_mk_2375_, v_env_2376_, v_kind_2377_);
lean_dec(v_kind_2377_);
lean_dec_ref(v_attr_2374_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object* v_00_u03b1_2379_, lean_object* v_attr_2380_, lean_object* v_mk_2381_, lean_object* v_env_2382_, lean_object* v_x_2383_, lean_object* v_kind_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2380_, v_mk_2381_, v_env_2382_, v_kind_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object* v_00_u03b1_2386_, lean_object* v_attr_2387_, lean_object* v_mk_2388_, lean_object* v_env_2389_, lean_object* v_x_2390_, lean_object* v_kind_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Fmt_keyedFmtProvider(v_00_u03b1_2386_, v_attr_2387_, v_mk_2388_, v_env_2389_, v_x_2390_, v_kind_2391_);
lean_dec(v_kind_2391_);
lean_dec_ref(v_x_2390_);
lean_dec_ref(v_attr_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_2393_, lean_object* v_i_2394_, lean_object* v_k_2395_){
_start:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_array_get_size(v_keys_2393_);
v___x_2397_ = lean_nat_dec_lt(v_i_2394_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_dec(v_i_2394_);
return v___x_2397_;
}
else
{
lean_object* v_k_x27_2398_; uint8_t v___x_2399_; 
v_k_x27_2398_ = lean_array_fget_borrowed(v_keys_2393_, v_i_2394_);
v___x_2399_ = l_Lean_instBEqExtraModUse_beq(v_k_2395_, v_k_x27_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_add(v_i_2394_, v___x_2400_);
lean_dec(v_i_2394_);
v_i_2394_ = v___x_2401_;
goto _start;
}
else
{
lean_dec(v_i_2394_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_2403_, lean_object* v_i_2404_, lean_object* v_k_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2403_, v_i_2404_, v_k_2405_);
lean_dec_ref(v_k_2405_);
lean_dec_ref(v_keys_2403_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_2408_, size_t v_x_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v_es_2411_; lean_object* v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; lean_object* v_j_2415_; lean_object* v___x_2416_; 
v_es_2411_ = lean_ctor_get(v_x_2408_, 0);
v___x_2412_ = lean_box(2);
v___x_2413_ = ((size_t)31ULL);
v___x_2414_ = lean_usize_land(v_x_2409_, v___x_2413_);
v_j_2415_ = lean_usize_to_nat(v___x_2414_);
v___x_2416_ = lean_array_get_borrowed(v___x_2412_, v_es_2411_, v_j_2415_);
lean_dec(v_j_2415_);
switch(lean_obj_tag(v___x_2416_))
{
case 0:
{
lean_object* v_key_2417_; uint8_t v___x_2418_; 
v_key_2417_ = lean_ctor_get(v___x_2416_, 0);
v___x_2418_ = l_Lean_instBEqExtraModUse_beq(v_x_2410_, v_key_2417_);
return v___x_2418_;
}
case 1:
{
lean_object* v_node_2419_; size_t v___x_2420_; size_t v___x_2421_; 
v_node_2419_ = lean_ctor_get(v___x_2416_, 0);
v___x_2420_ = ((size_t)5ULL);
v___x_2421_ = lean_usize_shift_right(v_x_2409_, v___x_2420_);
v_x_2408_ = v_node_2419_;
v_x_2409_ = v___x_2421_;
goto _start;
}
default: 
{
uint8_t v___x_2423_; 
v___x_2423_ = 0;
return v___x_2423_;
}
}
}
else
{
lean_object* v_ks_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v_ks_2424_ = lean_ctor_get(v_x_2408_, 0);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_2424_, v___x_2425_, v_x_2410_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
size_t v_x_5189__boxed_2430_; uint8_t v_res_2431_; lean_object* v_r_2432_; 
v_x_5189__boxed_2430_ = lean_unbox_usize(v_x_2428_);
lean_dec(v_x_2428_);
v_res_2431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2427_, v_x_5189__boxed_2430_, v_x_2429_);
lean_dec_ref(v_x_2429_);
lean_dec_ref(v_x_2427_);
v_r_2432_ = lean_box(v_res_2431_);
return v_r_2432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
uint64_t v___x_2435_; size_t v___x_2436_; uint8_t v___x_2437_; 
v___x_2435_ = l_Lean_instHashableExtraModUse_hash(v_x_2434_);
v___x_2436_ = lean_uint64_to_usize(v___x_2435_);
v___x_2437_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2433_, v___x_2436_, v_x_2434_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
uint8_t v_res_2440_; lean_object* v_r_2441_; 
v_res_2440_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2438_, v_x_2439_);
lean_dec_ref(v_x_2439_);
lean_dec_ref(v_x_2438_);
v_r_2441_ = lean_box(v_res_2440_);
return v_r_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0(lean_object* v___x_2442_, lean_object* v_entry_2443_, lean_object* v_s_2444_){
_start:
{
lean_object* v_addEntryFn_2445_; lean_object* v_importedEntries_2446_; lean_object* v_state_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2455_; 
v_addEntryFn_2445_ = lean_ctor_get(v___x_2442_, 3);
lean_inc(v_addEntryFn_2445_);
lean_dec_ref(v___x_2442_);
v_importedEntries_2446_ = lean_ctor_get(v_s_2444_, 0);
v_state_2447_ = lean_ctor_get(v_s_2444_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_s_2444_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2449_ = v_s_2444_;
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_state_2447_);
lean_inc(v_importedEntries_2446_);
lean_dec(v_s_2444_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_state_2451_; lean_object* v___x_2453_; 
v_state_2451_ = lean_apply_2(v_addEntryFn_2445_, v_state_2447_, v_entry_2443_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_state_2451_);
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_importedEntries_2446_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_state_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2456_; double v___x_2457_; 
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_float_of_nat(v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object* v_cls_2461_, lean_object* v_msg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_ref_2466_; lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2513_; 
v_ref_2466_ = lean_ctor_get(v___y_2463_, 2);
v___x_2467_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_2462_, v___y_2463_, v___y_2464_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2513_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2513_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v_traceState_2473_; lean_object* v_env_2474_; lean_object* v_nextMacroScope_2475_; lean_object* v_ngen_2476_; lean_object* v_auxDeclNGen_2477_; lean_object* v_cache_2478_; lean_object* v_recordedDeps_2479_; lean_object* v_messages_2480_; lean_object* v_infoState_2481_; lean_object* v_snapshotTasks_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2512_; 
v___x_2472_ = lean_st_ref_take(v___y_2464_);
v_traceState_2473_ = lean_ctor_get(v___x_2472_, 4);
v_env_2474_ = lean_ctor_get(v___x_2472_, 0);
v_nextMacroScope_2475_ = lean_ctor_get(v___x_2472_, 1);
v_ngen_2476_ = lean_ctor_get(v___x_2472_, 2);
v_auxDeclNGen_2477_ = lean_ctor_get(v___x_2472_, 3);
v_cache_2478_ = lean_ctor_get(v___x_2472_, 5);
v_recordedDeps_2479_ = lean_ctor_get(v___x_2472_, 6);
v_messages_2480_ = lean_ctor_get(v___x_2472_, 7);
v_infoState_2481_ = lean_ctor_get(v___x_2472_, 8);
v_snapshotTasks_2482_ = lean_ctor_get(v___x_2472_, 9);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2484_ = v___x_2472_;
v_isShared_2485_ = v_isSharedCheck_2512_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_snapshotTasks_2482_);
lean_inc(v_infoState_2481_);
lean_inc(v_messages_2480_);
lean_inc(v_recordedDeps_2479_);
lean_inc(v_cache_2478_);
lean_inc(v_traceState_2473_);
lean_inc(v_auxDeclNGen_2477_);
lean_inc(v_ngen_2476_);
lean_inc(v_nextMacroScope_2475_);
lean_inc(v_env_2474_);
lean_dec(v___x_2472_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2512_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
uint64_t v_tid_2486_; lean_object* v_traces_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2511_; 
v_tid_2486_ = lean_ctor_get_uint64(v_traceState_2473_, sizeof(void*)*1);
v_traces_2487_ = lean_ctor_get(v_traceState_2473_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_traceState_2473_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2489_ = v_traceState_2473_;
v_isShared_2490_ = v_isSharedCheck_2511_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_traces_2487_);
lean_dec(v_traceState_2473_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2511_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; double v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0);
v___x_2494_ = 0;
v___x_2495_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2496_, 0, v_cls_2461_);
lean_ctor_set(v___x_2496_, 1, v___x_2492_);
lean_ctor_set(v___x_2496_, 2, v___x_2495_);
lean_ctor_set_float(v___x_2496_, sizeof(void*)*3, v___x_2493_);
lean_ctor_set_float(v___x_2496_, sizeof(void*)*3 + 8, v___x_2493_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*3 + 16, v___x_2494_);
v___x_2497_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2));
v___x_2498_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v_a_2468_);
lean_ctor_set(v___x_2498_, 2, v___x_2497_);
lean_inc(v_ref_2466_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_ref_2466_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = l_Lean_PersistentArray_push___redArg(v_traces_2487_, v___x_2499_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2500_);
v___x_2502_ = v___x_2489_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2500_);
lean_ctor_set_uint64(v_reuseFailAlloc_2510_, sizeof(void*)*1, v_tid_2486_);
v___x_2502_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 4, v___x_2502_);
v___x_2504_ = v___x_2484_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_env_2474_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_nextMacroScope_2475_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_ngen_2476_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_auxDeclNGen_2477_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v_cache_2478_);
lean_ctor_set(v_reuseFailAlloc_2509_, 6, v_recordedDeps_2479_);
lean_ctor_set(v_reuseFailAlloc_2509_, 7, v_messages_2480_);
lean_ctor_set(v_reuseFailAlloc_2509_, 8, v_infoState_2481_);
lean_ctor_set(v_reuseFailAlloc_2509_, 9, v_snapshotTasks_2482_);
v___x_2504_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_st_ref_put(v___y_2464_, v___x_2504_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2491_);
v___x_2507_ = v___x_2470_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2491_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2514_, v_msg_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2520_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v_cls_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_cls_2535_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2536_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9));
v___x_2537_ = l_Lean_Name_append(v___x_2536_, v_cls_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object* v_mod_2548_, uint8_t v_isMeta_2549_, lean_object* v_hint_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_env_2572_; uint8_t v_isExporting_2573_; lean_object* v_entry_2574_; lean_object* v___x_2575_; lean_object* v_env_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2570_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0);
v___x_2571_ = lean_st_ref_get(v___y_2552_);
v_env_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc_ref(v_env_2572_);
lean_dec(v___x_2571_);
v_isExporting_2573_ = lean_ctor_get_uint8(v_env_2572_, sizeof(void*)*13);
lean_dec_ref(v_env_2572_);
lean_inc(v_mod_2548_);
v_entry_2574_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2574_, 0, v_mod_2548_);
lean_ctor_set_uint8(v_entry_2574_, sizeof(void*)*1, v_isExporting_2573_);
lean_ctor_set_uint8(v_entry_2574_, sizeof(void*)*1 + 1, v_isMeta_2549_);
v___x_2575_ = lean_st_ref_get(v___y_2552_);
v_env_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_env_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2578_ = lean_box(1);
v___x_2579_ = lean_box(0);
v___x_2580_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2570_, v___x_2577_, v_env_2576_, v___x_2578_, v___x_2579_);
v___x_2581_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v___x_2580_, v_entry_2574_);
lean_dec(v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v_toCold_2582_; lean_object* v_options_2583_; lean_object* v_inheritedTraceOptions_2584_; uint8_t v_hasTrace_2585_; lean_object* v___f_2586_; uint8_t v___x_2587_; lean_object* v___y_2589_; 
v_toCold_2582_ = lean_ctor_get(v___y_2551_, 0);
v_options_2583_ = lean_ctor_get(v_toCold_2582_, 2);
v_inheritedTraceOptions_2584_ = lean_ctor_get(v_toCold_2582_, 11);
v_hasTrace_2585_ = lean_ctor_get_uint8(v_options_2583_, sizeof(void*)*1);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2586_, 0, v___x_2577_);
lean_closure_set(v___f_2586_, 1, v_entry_2574_);
v___x_2587_ = 1;
if (v_hasTrace_2585_ == 0)
{
lean_dec(v_hint_2550_);
lean_dec(v_mod_2548_);
v___y_2589_ = v___y_2552_;
goto v___jp_2588_;
}
else
{
lean_object* v_cls_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v_cls_2607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2627_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10);
v___x_2628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2584_, v_options_2583_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec(v_hint_2550_);
lean_dec(v_mod_2548_);
v___y_2589_ = v___y_2552_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2629_; lean_object* v___y_2631_; 
v___x_2629_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12);
if (v_isExporting_2573_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17));
v___y_2631_ = v___x_2638_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18));
v___y_2631_ = v___x_2639_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc_ref(v___y_2631_);
v___x_2632_ = l_Lean_stringToMessageData(v___y_2631_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2629_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
if (v_isMeta_2549_ == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15));
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___x_2636_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16));
v___y_2614_ = v___x_2635_;
v___y_2615_ = v___x_2637_;
goto v___jp_2613_;
}
}
}
v___jp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2609_);
lean_ctor_set(v___x_2611_, 1, v___y_2610_);
v___x_2612_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2607_, v___x_2611_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref_known(v___x_2612_, 1);
v___y_2589_ = v___y_2552_;
goto v___jp_2588_;
}
else
{
lean_dec_ref(v___f_2586_);
return v___x_2612_;
}
}
v___jp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_inc_ref(v___y_2615_);
v___x_2616_ = l_Lean_stringToMessageData(v___y_2615_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___y_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofName(v_mod_2548_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l_Lean_Name_isAnonymous(v_hint_2550_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6);
v___x_2624_ = l_Lean_MessageData_ofName(v_hint_2550_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2625_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_hint_2550_);
v___x_2626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7);
v___y_2609_ = v___x_2621_;
v___y_2610_ = v___x_2626_;
goto v___jp_2608_;
}
}
}
v___jp_2588_:
{
lean_object* v___x_2590_; lean_object* v_toEnvExtension_2591_; lean_object* v_env_2592_; lean_object* v_nextMacroScope_2593_; lean_object* v_ngen_2594_; lean_object* v_auxDeclNGen_2595_; lean_object* v_traceState_2596_; lean_object* v_recordedDeps_2597_; lean_object* v_messages_2598_; lean_object* v_infoState_2599_; lean_object* v_snapshotTasks_2600_; lean_object* v_asyncMode_2601_; uint8_t v_logWrites_2602_; lean_object* v___x_2603_; 
v___x_2590_ = lean_st_ref_take(v___y_2589_);
v_toEnvExtension_2591_ = lean_ctor_get(v___x_2577_, 0);
v_env_2592_ = lean_ctor_get(v___x_2590_, 0);
lean_inc_ref(v_env_2592_);
v_nextMacroScope_2593_ = lean_ctor_get(v___x_2590_, 1);
lean_inc(v_nextMacroScope_2593_);
v_ngen_2594_ = lean_ctor_get(v___x_2590_, 2);
lean_inc_ref(v_ngen_2594_);
v_auxDeclNGen_2595_ = lean_ctor_get(v___x_2590_, 3);
lean_inc_ref(v_auxDeclNGen_2595_);
v_traceState_2596_ = lean_ctor_get(v___x_2590_, 4);
lean_inc_ref(v_traceState_2596_);
v_recordedDeps_2597_ = lean_ctor_get(v___x_2590_, 6);
lean_inc_ref(v_recordedDeps_2597_);
v_messages_2598_ = lean_ctor_get(v___x_2590_, 7);
lean_inc_ref(v_messages_2598_);
v_infoState_2599_ = lean_ctor_get(v___x_2590_, 8);
lean_inc_ref(v_infoState_2599_);
v_snapshotTasks_2600_ = lean_ctor_get(v___x_2590_, 9);
lean_inc_ref(v_snapshotTasks_2600_);
lean_dec(v___x_2590_);
v_asyncMode_2601_ = lean_ctor_get(v_toEnvExtension_2591_, 2);
v_logWrites_2602_ = lean_ctor_get_uint8(v_toEnvExtension_2591_, sizeof(void*)*6);
v___x_2603_ = lean_box(0);
if (v_logWrites_2602_ == 0)
{
lean_object* v___x_2604_; 
lean_inc_ref(v_toEnvExtension_2591_);
v___x_2604_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2591_, v_env_2592_, v___f_2586_, v_asyncMode_2601_, v___x_2579_, v___x_2587_);
v___y_2555_ = v_auxDeclNGen_2595_;
v___y_2556_ = v_traceState_2596_;
v___y_2557_ = v_ngen_2594_;
v___y_2558_ = v_snapshotTasks_2600_;
v___y_2559_ = v___y_2589_;
v___y_2560_ = v_recordedDeps_2597_;
v___y_2561_ = v_messages_2598_;
v___y_2562_ = v_nextMacroScope_2593_;
v___y_2563_ = v___x_2603_;
v___y_2564_ = v_infoState_2599_;
v___y_2565_ = v___x_2604_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_inc_ref_n(v_toEnvExtension_2591_, 2);
v___x_2605_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2591_, v_env_2592_);
lean_dec_ref(v_env_2592_);
v___x_2606_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2591_, v___x_2605_, v___f_2586_, v_asyncMode_2601_, v___x_2579_, v___x_2587_);
v___y_2555_ = v_auxDeclNGen_2595_;
v___y_2556_ = v_traceState_2596_;
v___y_2557_ = v_ngen_2594_;
v___y_2558_ = v_snapshotTasks_2600_;
v___y_2559_ = v___y_2589_;
v___y_2560_ = v_recordedDeps_2597_;
v___y_2561_ = v_messages_2598_;
v___y_2562_ = v_nextMacroScope_2593_;
v___y_2563_ = v___x_2603_;
v___y_2564_ = v_infoState_2599_;
v___y_2565_ = v___x_2606_;
goto v___jp_2554_;
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref_known(v_entry_2574_, 1);
lean_dec(v_hint_2550_);
lean_dec(v_mod_2548_);
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
v___jp_2554_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2566_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
v___x_2567_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2567_, 0, v___y_2565_);
lean_ctor_set(v___x_2567_, 1, v___y_2562_);
lean_ctor_set(v___x_2567_, 2, v___y_2557_);
lean_ctor_set(v___x_2567_, 3, v___y_2555_);
lean_ctor_set(v___x_2567_, 4, v___y_2556_);
lean_ctor_set(v___x_2567_, 5, v___x_2566_);
lean_ctor_set(v___x_2567_, 6, v___y_2560_);
lean_ctor_set(v___x_2567_, 7, v___y_2561_);
lean_ctor_set(v___x_2567_, 8, v___y_2564_);
lean_ctor_set(v___x_2567_, 9, v___y_2558_);
v___x_2568_ = lean_st_ref_put(v___y_2559_, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2563_);
return v___x_2569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object* v_mod_2642_, lean_object* v_isMeta_2643_, lean_object* v_hint_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v_isMeta_boxed_2648_; lean_object* v_res_2649_; 
v_isMeta_boxed_2648_ = lean_unbox(v_isMeta_2643_);
v_res_2649_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_mod_2642_, v_isMeta_boxed_2648_, v_hint_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object* v___x_2650_, lean_object* v_declName_2651_, lean_object* v_as_2652_, size_t v_sz_2653_, size_t v_i_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_2659_; 
v___x_2659_ = lean_usize_dec_lt(v_i_2654_, v_sz_2653_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec(v_declName_2651_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_b_2655_);
return v___x_2660_;
}
else
{
lean_object* v___x_2661_; lean_object* v_modules_2662_; lean_object* v___x_2663_; lean_object* v_a_2664_; lean_object* v___x_2665_; lean_object* v_toImport_2666_; lean_object* v_module_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; 
v___x_2661_ = l_Lean_Environment_header(v___x_2650_);
v_modules_2662_ = lean_ctor_get(v___x_2661_, 3);
lean_inc_ref(v_modules_2662_);
lean_dec_ref(v___x_2661_);
v___x_2663_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2664_ = lean_array_uget_borrowed(v_as_2652_, v_i_2654_);
v___x_2665_ = lean_array_get(v___x_2663_, v_modules_2662_, v_a_2664_);
lean_dec_ref(v_modules_2662_);
v_toImport_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_ref(v_toImport_2666_);
lean_dec(v___x_2665_);
v_module_2667_ = lean_ctor_get(v_toImport_2666_, 0);
lean_inc(v_module_2667_);
lean_dec_ref(v_toImport_2666_);
v___x_2668_ = lean_box(0);
v___x_2669_ = 0;
lean_inc(v_declName_2651_);
v___x_2670_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2667_, v___x_2669_, v_declName_2651_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2670_) == 0)
{
size_t v___x_2671_; size_t v___x_2672_; 
lean_dec_ref_known(v___x_2670_, 1);
v___x_2671_ = ((size_t)1ULL);
v___x_2672_ = lean_usize_add(v_i_2654_, v___x_2671_);
v_i_2654_ = v___x_2672_;
v_b_2655_ = v___x_2668_;
goto _start;
}
else
{
lean_dec(v_declName_2651_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object* v___x_2674_, lean_object* v_declName_2675_, lean_object* v_as_2676_, lean_object* v_sz_2677_, lean_object* v_i_2678_, lean_object* v_b_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
size_t v_sz_boxed_2683_; size_t v_i_boxed_2684_; lean_object* v_res_2685_; 
v_sz_boxed_2683_ = lean_unbox_usize(v_sz_2677_);
lean_dec(v_sz_2677_);
v_i_boxed_2684_ = lean_unbox_usize(v_i_2678_);
lean_dec(v_i_2678_);
v_res_2685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v___x_2674_, v_declName_2675_, v_as_2676_, v_sz_boxed_2683_, v_i_boxed_2684_, v_b_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_as_2676_);
lean_dec_ref(v___x_2674_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2686_, lean_object* v_x_2687_){
_start:
{
if (lean_obj_tag(v_x_2687_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_box(0);
return v___x_2688_;
}
else
{
lean_object* v_key_2689_; lean_object* v_value_2690_; lean_object* v_tail_2691_; uint8_t v___x_2692_; 
v_key_2689_ = lean_ctor_get(v_x_2687_, 0);
v_value_2690_ = lean_ctor_get(v_x_2687_, 1);
v_tail_2691_ = lean_ctor_get(v_x_2687_, 2);
v___x_2692_ = lean_name_eq(v_key_2689_, v_a_2686_);
if (v___x_2692_ == 0)
{
v_x_2687_ = v_tail_2691_;
goto _start;
}
else
{
lean_object* v___x_2694_; 
lean_inc(v_value_2690_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_value_2690_);
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2695_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec(v_a_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object* v_m_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_buckets_2700_; lean_object* v___x_2701_; uint64_t v___y_2703_; 
v_buckets_2700_ = lean_ctor_get(v_m_2698_, 1);
v___x_2701_ = lean_array_get_size(v_buckets_2700_);
if (lean_obj_tag(v_a_2699_) == 0)
{
uint64_t v___x_2717_; 
v___x_2717_ = 1723ULL;
v___y_2703_ = v___x_2717_;
goto v___jp_2702_;
}
else
{
uint64_t v_hash_2718_; 
v_hash_2718_ = lean_ctor_get_uint64(v_a_2699_, sizeof(void*)*2);
v___y_2703_ = v_hash_2718_;
goto v___jp_2702_;
}
v___jp_2702_:
{
uint64_t v___x_2704_; uint64_t v___x_2705_; uint64_t v_fold_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; size_t v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2704_ = 32ULL;
v___x_2705_ = lean_uint64_shift_right(v___y_2703_, v___x_2704_);
v_fold_2706_ = lean_uint64_xor(v___y_2703_, v___x_2705_);
v___x_2707_ = 16ULL;
v___x_2708_ = lean_uint64_shift_right(v_fold_2706_, v___x_2707_);
v___x_2709_ = lean_uint64_xor(v_fold_2706_, v___x_2708_);
v___x_2710_ = lean_uint64_to_usize(v___x_2709_);
v___x_2711_ = lean_usize_of_nat(v___x_2701_);
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_sub(v___x_2711_, v___x_2712_);
v___x_2714_ = lean_usize_land(v___x_2710_, v___x_2713_);
v___x_2715_ = lean_array_uget_borrowed(v_buckets_2700_, v___x_2714_);
v___x_2716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2699_, v___x_2715_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object* v_m_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec_ref(v_m_2719_);
return v_res_2721_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object* v_declName_2725_, uint8_t v_isMeta_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_env_2735_; lean_object* v___y_2737_; lean_object* v___x_2750_; 
v___x_2730_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0);
v___x_2731_ = lean_st_ref_get(v___y_2728_);
v_env_2735_ = lean_ctor_get(v___x_2731_, 0);
lean_inc_ref(v_env_2735_);
lean_dec(v___x_2731_);
v___x_2750_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2735_, v_declName_2725_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_dec_ref(v_env_2735_);
lean_dec(v_declName_2725_);
goto v___jp_2732_;
}
else
{
lean_object* v_val_2751_; lean_object* v___x_2752_; lean_object* v_modules_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_val_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Environment_header(v_env_2735_);
v_modules_2753_ = lean_ctor_get(v___x_2752_, 3);
lean_inc_ref(v_modules_2753_);
lean_dec_ref(v___x_2752_);
v___x_2754_ = lean_array_get_size(v_modules_2753_);
v___x_2755_ = lean_nat_dec_lt(v_val_2751_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_dec_ref(v_modules_2753_);
lean_dec(v_val_2751_);
lean_dec_ref(v_env_2735_);
lean_dec(v_declName_2725_);
goto v___jp_2732_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___y_2759_; 
v___x_2756_ = lean_array_fget(v_modules_2753_, v_val_2751_);
lean_dec(v_val_2751_);
lean_dec_ref(v_modules_2753_);
v___x_2757_ = lean_st_ref_get(v___y_2728_);
if (v_isMeta_2726_ == 0)
{
lean_dec(v___x_2757_);
v___y_2759_ = v_isMeta_2726_;
goto v___jp_2758_;
}
else
{
lean_object* v_env_2770_; uint8_t v___x_2771_; 
v_env_2770_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_ref(v_env_2770_);
lean_dec(v___x_2757_);
lean_inc(v_declName_2725_);
v___x_2771_ = l_Lean_isMarkedMeta(v_env_2770_, v_declName_2725_);
if (v___x_2771_ == 0)
{
v___y_2759_ = v_isMeta_2726_;
goto v___jp_2758_;
}
else
{
uint8_t v___x_2772_; 
v___x_2772_ = 0;
v___y_2759_ = v___x_2772_;
goto v___jp_2758_;
}
}
v___jp_2758_:
{
lean_object* v_toImport_2760_; lean_object* v_module_2761_; lean_object* v___x_2762_; 
v_toImport_2760_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_ref(v_toImport_2760_);
lean_dec(v___x_2756_);
v_module_2761_ = lean_ctor_get(v_toImport_2760_, 0);
lean_inc(v_module_2761_);
lean_dec_ref(v_toImport_2760_);
lean_inc(v_declName_2725_);
v___x_2762_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2761_, v___y_2759_, v_declName_2725_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec_ref_known(v___x_2762_, 1);
v___x_2763_ = l_Lean_indirectModUseExt;
v___x_2764_ = lean_box(1);
v___x_2765_ = lean_box(0);
lean_inc_ref(v_env_2735_);
v___x_2766_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2730_, v___x_2763_, v_env_2735_, v___x_2764_, v___x_2765_);
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v___x_2766_, v_declName_2725_);
lean_dec(v___x_2766_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v___x_2768_; 
v___x_2768_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1));
v___y_2737_ = v___x_2768_;
goto v___jp_2736_;
}
else
{
lean_object* v_val_2769_; 
v_val_2769_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2737_ = v_val_2769_;
goto v___jp_2736_;
}
}
else
{
lean_dec_ref(v_env_2735_);
lean_dec(v_declName_2725_);
return v___x_2762_;
}
}
}
}
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
v___jp_2736_:
{
lean_object* v___x_2738_; size_t v_sz_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2738_ = lean_box(0);
v_sz_2739_ = lean_array_size(v___y_2737_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v_env_2735_, v_declName_2725_, v___y_2737_, v_sz_2739_, v___x_2740_, v___x_2738_, v___y_2727_, v___y_2728_);
lean_dec_ref(v___y_2737_);
lean_dec_ref(v_env_2735_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2741_, 0);
lean_dec(v_unused_2749_);
v___x_2743_ = v___x_2741_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_dec(v___x_2741_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2738_);
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2738_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object* v_declName_2773_, lean_object* v_isMeta_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v_isMeta_boxed_2778_; lean_object* v_res_2779_; 
v_isMeta_boxed_2778_ = lean_unbox(v_isMeta_2774_);
v_res_2779_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v_declName_2773_, v_isMeta_boxed_2778_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2779_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object* v_a_2780_, lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
uint8_t v___x_2782_; 
v___x_2782_ = 0;
return v___x_2782_;
}
else
{
lean_object* v_head_2783_; lean_object* v_tail_2784_; uint8_t v___x_2785_; 
v_head_2783_ = lean_ctor_get(v_x_2781_, 0);
v_tail_2784_ = lean_ctor_get(v_x_2781_, 1);
v___x_2785_ = lean_name_eq(v_a_2780_, v_head_2783_);
if (v___x_2785_ == 0)
{
v_x_2781_ = v_tail_2784_;
goto _start;
}
else
{
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object* v_a_2787_, lean_object* v_x_2788_){
_start:
{
uint8_t v_res_2789_; lean_object* v_r_2790_; 
v_res_2789_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v_a_2787_, v_x_2788_);
lean_dec(v_x_2788_);
lean_dec(v_a_2787_);
v_r_2790_ = lean_box(v_res_2789_);
return v_r_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object* v_t_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v_infoState_2795_; uint8_t v_enabled_2796_; 
v___x_2794_ = lean_st_ref_get(v___y_2792_);
v_infoState_2795_ = lean_ctor_get(v___x_2794_, 8);
lean_inc_ref(v_infoState_2795_);
lean_dec(v___x_2794_);
v_enabled_2796_ = lean_ctor_get_uint8(v_infoState_2795_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2795_);
if (v_enabled_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v_t_2791_);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; lean_object* v_infoState_2800_; lean_object* v_env_2801_; lean_object* v_nextMacroScope_2802_; lean_object* v_ngen_2803_; lean_object* v_auxDeclNGen_2804_; lean_object* v_traceState_2805_; lean_object* v_cache_2806_; lean_object* v_recordedDeps_2807_; lean_object* v_messages_2808_; lean_object* v_snapshotTasks_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2831_; 
v___x_2799_ = lean_st_ref_take(v___y_2792_);
v_infoState_2800_ = lean_ctor_get(v___x_2799_, 8);
v_env_2801_ = lean_ctor_get(v___x_2799_, 0);
v_nextMacroScope_2802_ = lean_ctor_get(v___x_2799_, 1);
v_ngen_2803_ = lean_ctor_get(v___x_2799_, 2);
v_auxDeclNGen_2804_ = lean_ctor_get(v___x_2799_, 3);
v_traceState_2805_ = lean_ctor_get(v___x_2799_, 4);
v_cache_2806_ = lean_ctor_get(v___x_2799_, 5);
v_recordedDeps_2807_ = lean_ctor_get(v___x_2799_, 6);
v_messages_2808_ = lean_ctor_get(v___x_2799_, 7);
v_snapshotTasks_2809_ = lean_ctor_get(v___x_2799_, 9);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2811_ = v___x_2799_;
v_isShared_2812_ = v_isSharedCheck_2831_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_snapshotTasks_2809_);
lean_inc(v_infoState_2800_);
lean_inc(v_messages_2808_);
lean_inc(v_recordedDeps_2807_);
lean_inc(v_cache_2806_);
lean_inc(v_traceState_2805_);
lean_inc(v_auxDeclNGen_2804_);
lean_inc(v_ngen_2803_);
lean_inc(v_nextMacroScope_2802_);
lean_inc(v_env_2801_);
lean_dec(v___x_2799_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2831_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
uint8_t v_enabled_2813_; lean_object* v_assignment_2814_; lean_object* v_lazyAssignment_2815_; lean_object* v_trees_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2830_; 
v_enabled_2813_ = lean_ctor_get_uint8(v_infoState_2800_, sizeof(void*)*3);
v_assignment_2814_ = lean_ctor_get(v_infoState_2800_, 0);
v_lazyAssignment_2815_ = lean_ctor_get(v_infoState_2800_, 1);
v_trees_2816_ = lean_ctor_get(v_infoState_2800_, 2);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_infoState_2800_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2818_ = v_infoState_2800_;
v_isShared_2819_ = v_isSharedCheck_2830_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_trees_2816_);
lean_inc(v_lazyAssignment_2815_);
lean_inc(v_assignment_2814_);
lean_dec(v_infoState_2800_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2830_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2820_ = lean_box(0);
v___x_2821_ = l_Lean_PersistentArray_push___redArg(v_trees_2816_, v_t_2791_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 2, v___x_2821_);
v___x_2823_ = v___x_2818_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_assignment_2814_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_lazyAssignment_2815_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v___x_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2829_, sizeof(void*)*3, v_enabled_2813_);
v___x_2823_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 8, v___x_2823_);
v___x_2825_ = v___x_2811_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_env_2801_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_nextMacroScope_2802_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_ngen_2803_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_auxDeclNGen_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_traceState_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_cache_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_recordedDeps_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_messages_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2828_, 9, v_snapshotTasks_2809_);
v___x_2825_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_st_ref_put(v___y_2792_, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2820_);
return v___x_2827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2832_, v___y_2833_);
lean_dec(v___y_2833_);
return v_res_2835_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_unsigned_to_nat(32u);
v___x_2837_ = lean_mk_empty_array_with_capacity(v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((size_t)5ULL);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = lean_unsigned_to_nat(32u);
v___x_2842_ = lean_mk_empty_array_with_capacity(v___x_2841_);
v___x_2843_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0);
v___x_2844_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2842_);
lean_ctor_set(v___x_2844_, 2, v___x_2840_);
lean_ctor_set(v___x_2844_, 3, v___x_2840_);
lean_ctor_set_usize(v___x_2844_, 4, v___x_2839_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object* v_t_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v_infoState_2850_; uint8_t v_enabled_2851_; 
v___x_2849_ = lean_st_ref_get(v___y_2847_);
v_infoState_2850_ = lean_ctor_get(v___x_2849_, 8);
lean_inc_ref(v_infoState_2850_);
lean_dec(v___x_2849_);
v_enabled_2851_ = lean_ctor_get_uint8(v_infoState_2850_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2850_);
if (v_enabled_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_t_2845_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_t_2845_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v___x_2855_, v___y_2847_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object* v_t_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v_t_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
if (lean_obj_tag(v_a_2862_) == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l_List_reverse___redArg(v_a_2863_);
return v___x_2864_;
}
else
{
lean_object* v_head_2865_; lean_object* v_tail_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2875_; 
v_head_2865_ = lean_ctor_get(v_a_2862_, 0);
v_tail_2866_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2868_ = v_a_2862_;
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_tail_2866_);
lean_inc(v_head_2865_);
lean_dec(v_a_2862_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = l_Lean_mkLevelParam(v_head_2865_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v_a_2863_);
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_a_2863_);
v___x_2872_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v_a_2862_ = v_tail_2866_;
v_a_2863_ = v___x_2872_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; lean_object* v_env_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2880_ = lean_st_ref_get(v___y_2878_);
v_env_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc_ref(v_env_2881_);
lean_dec(v___x_2880_);
v___x_2882_ = 0;
lean_inc(v_constName_2876_);
v___x_2883_ = l_Lean_Environment_findConstVal_x3f(v_env_2881_, v_constName_2876_, v___x_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_2876_, v___y_2877_, v___y_2878_);
return v___x_2884_;
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_constName_2876_);
v_val_2885_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2883_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_val_2885_);
lean_dec(v___x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set_tag(v___x_2887_, 0);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_val_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object* v_constName_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
lean_inc(v_constName_2898_);
v___x_2902_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2914_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_levelParams_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_levelParams_2907_ = lean_ctor_get(v_a_2903_, 1);
lean_inc(v_levelParams_2907_);
lean_dec(v_a_2903_);
v___x_2908_ = lean_box(0);
v___x_2909_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(v_levelParams_2907_, v___x_2908_);
v___x_2910_ = l_Lean_mkConst(v_constName_2898_, v___x_2909_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2910_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_constName_2898_);
v_a_2915_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2902_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2902_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object* v_constName_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_constName_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object* v_stx_2928_, lean_object* v_n_2929_, lean_object* v_expectedType_x3f_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_n_2929_, v___y_2931_, v___y_2932_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v_stx_2928_);
v___x_2938_ = l_Lean_LocalContext_empty;
v___x_2939_ = 0;
v___x_2940_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2940_, 0, v___x_2937_);
lean_ctor_set(v___x_2940_, 1, v___x_2938_);
lean_ctor_set(v___x_2940_, 2, v_expectedType_x3f_2930_);
lean_ctor_set(v___x_2940_, 3, v_a_2935_);
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*4, v___x_2939_);
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*4 + 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___x_2942_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v___x_2941_, v___y_2931_, v___y_2932_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_expectedType_x3f_2930_);
lean_dec(v_stx_2928_);
v_a_2943_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2934_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2934_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object* v_stx_2951_, lean_object* v_n_2952_, lean_object* v_expectedType_x3f_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_stx_2951_, v_n_2952_, v_expectedType_x3f_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2957_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2));
v___x_2963_ = l_Lean_stringToMessageData(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object* v_attrName_2964_, lean_object* v_extraKinds_2965_, uint8_t v_builtin_2966_, lean_object* v_stx_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v_env_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_st_ref_get(v_a_2969_);
v_env_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc_ref(v_env_2972_);
lean_dec(v___x_2971_);
v___x_2973_ = l_Lean_Attribute_Builtin_getIdent(v_stx_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3051_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_3051_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3051_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___y_2980_; lean_object* v___y_2981_; 
v___x_2978_ = l_Lean_Syntax_getId(v_a_2974_);
if (v_builtin_2966_ == 0)
{
goto v___jp_3028_;
}
else
{
uint8_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = 0;
lean_inc(v___x_2978_);
lean_inc_ref(v_env_2972_);
v___x_3050_ = l_Lean_Environment_find_x3f(v_env_2972_, v___x_2978_, v___x_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
goto v___jp_3028_;
}
else
{
lean_dec_ref_known(v___x_3050_, 1);
lean_dec_ref(v_env_2972_);
lean_dec(v_attrName_2964_);
v___y_2980_ = v_a_2968_;
v___y_2981_ = v_a_2969_;
goto v___jp_2979_;
}
}
v___jp_2979_:
{
lean_object* v___x_2982_; lean_object* v_env_2983_; uint8_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2982_ = lean_st_ref_get(v___y_2981_);
v_env_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc_ref(v_env_2983_);
lean_dec(v___x_2982_);
v___x_2984_ = 1;
lean_inc(v___x_2978_);
v___x_2985_ = l_Lean_Environment_contains(v_env_2983_, v___x_2978_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2987_; 
lean_dec(v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2987_ = v___x_2976_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2978_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
else
{
uint8_t v___x_2989_; lean_object* v___x_2990_; 
lean_del_object(v___x_2976_);
v___x_2989_ = 0;
lean_inc(v___x_2978_);
v___x_2990_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v___x_2978_, v___x_2989_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3018_; 
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v___x_2990_, 0);
lean_dec(v_unused_3019_);
v___x_2992_ = v___x_2990_;
v_isShared_2993_ = v_isSharedCheck_3018_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v___x_2990_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3018_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v_infoState_2995_; uint8_t v_enabled_2996_; 
v___x_2994_ = lean_st_ref_get(v___y_2981_);
v_infoState_2995_ = lean_ctor_get(v___x_2994_, 8);
lean_inc_ref(v_infoState_2995_);
lean_dec(v___x_2994_);
v_enabled_2996_ = lean_ctor_get_uint8(v_infoState_2995_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2995_);
if (v_enabled_2996_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_a_2974_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2978_);
v___x_2998_ = v___x_2992_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2978_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_del_object(v___x_2992_);
v___x_3000_ = lean_box(0);
lean_inc(v___x_2978_);
v___x_3001_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_a_2974_, v___x_2978_, v___x_3000_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v___x_3001_, 0);
lean_dec(v_unused_3009_);
v___x_3003_ = v___x_3001_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_dec(v___x_3001_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_2978_);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2978_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v___x_2978_);
v_a_3010_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3001_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3001_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v___x_2978_);
lean_dec(v_a_2974_);
v_a_3020_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_2990_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_2990_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
v___jp_3028_:
{
uint8_t v___x_3029_; 
lean_inc(v___x_2978_);
v___x_3029_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2972_, v___x_2978_);
if (v___x_3029_ == 0)
{
uint8_t v___x_3030_; 
v___x_3030_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v___x_2978_, v_extraKinds_2965_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_del_object(v___x_2976_);
lean_dec(v_a_2974_);
v___x_3031_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1);
v___x_3032_ = l_Lean_MessageData_ofName(v_attrName_2964_);
v___x_3033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = l_Lean_MessageData_ofName(v___x_2978_);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3039_, v_a_2968_, v_a_2969_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_dec(v_attrName_2964_);
v___y_2980_ = v_a_2968_;
v___y_2981_ = v_a_2969_;
goto v___jp_2979_;
}
}
else
{
lean_dec(v_attrName_2964_);
v___y_2980_ = v_a_2968_;
v___y_2981_ = v_a_2969_;
goto v___jp_2979_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_env_2972_);
lean_dec(v_attrName_2964_);
v_a_3052_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2973_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2973_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object* v_attrName_3060_, lean_object* v_extraKinds_3061_, lean_object* v_builtin_3062_, lean_object* v_stx_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
uint8_t v_builtin_boxed_3067_; lean_object* v_res_3068_; 
v_builtin_boxed_3067_ = lean_unbox(v_builtin_3062_);
v_res_3068_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(v_attrName_3060_, v_extraKinds_3061_, v_builtin_boxed_3067_, v_stx_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_extraKinds_3061_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object* v_00_u03b2_3069_, lean_object* v_m_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_3070_, v_a_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3073_, lean_object* v_m_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(v_00_u03b2_3073_, v_m_3074_, v_a_3075_);
lean_dec(v_a_3075_);
lean_dec_ref(v_m_3074_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object* v_t_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_3077_, v___y_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object* v_t_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(v_t_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3086_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_){
_start:
{
uint8_t v___x_3090_; 
v___x_3090_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_3088_, v_x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(v_00_u03b2_3091_, v_x_3092_, v_x_3093_);
lean_dec_ref(v_x_3093_);
lean_dec_ref(v_x_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3096_, lean_object* v_a_3097_, lean_object* v_x_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_3097_, v_x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3100_, lean_object* v_a_3101_, lean_object* v_x_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(v_00_u03b2_3100_, v_a_3101_, v_x_3102_);
lean_dec(v_x_3102_);
lean_dec(v_a_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3104_, lean_object* v_x_3105_, size_t v_x_3106_, lean_object* v_x_3107_){
_start:
{
uint8_t v___x_3108_; 
v___x_3108_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3105_, v_x_3106_, v_x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
size_t v_x_6265__boxed_3113_; uint8_t v_res_3114_; lean_object* v_r_3115_; 
v_x_6265__boxed_3113_ = lean_unbox_usize(v_x_3111_);
lean_dec(v_x_3111_);
v_res_3114_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3109_, v_x_3110_, v_x_6265__boxed_3113_, v_x_3112_);
lean_dec_ref(v_x_3112_);
lean_dec_ref(v_x_3110_);
v_r_3115_ = lean_box(v_res_3114_);
return v_r_3115_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_3116_, lean_object* v_keys_3117_, lean_object* v_vals_3118_, lean_object* v_heq_3119_, lean_object* v_i_3120_, lean_object* v_k_3121_){
_start:
{
uint8_t v___x_3122_; 
v___x_3122_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_3117_, v_i_3120_, v_k_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3123_, lean_object* v_keys_3124_, lean_object* v_vals_3125_, lean_object* v_heq_3126_, lean_object* v_i_3127_, lean_object* v_k_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_3123_, v_keys_3124_, v_vals_3125_, v_heq_3126_, v_i_3127_, v_k_3128_);
lean_dec_ref(v_k_3128_);
lean_dec_ref(v_vals_3125_);
lean_dec_ref(v_keys_3124_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(uint8_t v_builtin_3131_, lean_object* v_declName_3132_, lean_object* v_key_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_builtin_3139_, lean_object* v_declName_3140_, lean_object* v_key_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v_builtin_boxed_3145_; lean_object* v_res_3146_; 
v_builtin_boxed_3145_ = lean_unbox(v_builtin_3139_);
v_res_3146_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(v_builtin_boxed_3145_, v_declName_3140_, v_key_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v_key_3141_);
lean_dec(v_declName_3140_);
return v_res_3146_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_box(0);
v___x_3159_ = l_Lean_Fmt_headerKind;
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___x_3158_);
return v___x_3160_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3162_ = l_Lean_Fmt_cmdsKind;
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v___x_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3165_ = l_Lean_Fmt_moduleKind;
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3168_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3169_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed), 7, 2);
lean_closure_set(v___x_3169_, 0, v___x_3168_);
lean_closure_set(v___x_3169_, 1, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___f_3170_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3171_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3172_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3173_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3174_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3175_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3176_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3174_);
lean_ctor_set(v___x_3176_, 2, v___x_3173_);
lean_ctor_set(v___x_3176_, 3, v___x_3172_);
lean_ctor_set(v___x_3176_, 4, v___x_3171_);
lean_ctor_set(v___x_3176_, 5, v___f_3170_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3184_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3185_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3183_, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object* v_constName_3193_, lean_object* v_env_3194_, lean_object* v_opts_3195_){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
v___x_3197_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3194_, v_opts_3195_, v___x_3196_, v_constName_3193_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object* v_constName_3198_, lean_object* v_env_3199_, lean_object* v_opts_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(v_constName_3198_, v_env_3199_, v_opts_3200_);
lean_dec_ref(v_opts_3200_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object* v_constName_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_env_3205_; lean_object* v_opts_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_env_3205_ = lean_ctor_get(v_a_3203_, 0);
v_opts_3206_ = lean_ctor_get(v_a_3203_, 1);
v___x_3207_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
lean_inc_ref(v_env_3205_);
v___x_3208_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3205_, v_opts_3206_, v___x_3207_, v_constName_3202_);
v___x_3209_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object* v_constName_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_constName_3210_, v_a_3211_);
lean_dec_ref(v_a_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_));
v___x_3218_ = lean_st_mk_ref(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object* v_f_3222_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3224_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3225_ = lean_st_ref_take(v___x_3224_);
v___x_3226_ = lean_array_push(v___x_3225_, v_f_3222_);
v___x_3227_ = lean_st_ref_put(v___x_3224_, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object* v_f_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_Fmt_addBuiltinStickyTermFn(v_f_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3232_){
_start:
{
lean_object* v_fst_3233_; 
v_fst_3233_ = lean_ctor_get(v_x_3232_, 0);
lean_inc(v_fst_3233_);
return v_fst_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3234_);
lean_dec_ref(v_x_3234_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_box(0);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3238_);
lean_dec_ref(v_x_3238_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3240_, lean_object* v_s_3241_){
_start:
{
lean_object* v_fst_3242_; lean_object* v___x_3243_; 
v_fst_3242_ = lean_ctor_get(v_s_3241_, 0);
lean_inc_n(v_fst_3242_, 3);
v___x_3243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3243_, 0, v_fst_3242_);
lean_ctor_set(v___x_3243_, 1, v_fst_3242_);
lean_ctor_set(v___x_3243_, 2, v_fst_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3244_, lean_object* v_s_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3244_, v_s_3245_);
lean_dec_ref(v_s_3245_);
lean_dec_ref(v_x_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v_fst_3249_; lean_object* v_snd_3250_; lean_object* v_fst_3251_; lean_object* v_snd_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3261_; 
v_fst_3249_ = lean_ctor_get(v_x_3247_, 0);
lean_inc(v_fst_3249_);
v_snd_3250_ = lean_ctor_get(v_x_3247_, 1);
lean_inc(v_snd_3250_);
lean_dec_ref(v_x_3247_);
v_fst_3251_ = lean_ctor_get(v_x_3248_, 0);
v_snd_3252_ = lean_ctor_get(v_x_3248_, 1);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_x_3248_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3254_ = v_x_3248_;
v_isShared_3255_ = v_isSharedCheck_3261_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_snd_3252_);
lean_inc(v_fst_3251_);
lean_dec(v_x_3248_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3261_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3256_ = lean_array_push(v_fst_3249_, v_fst_3251_);
v___x_3257_ = lean_array_push(v_snd_3250_, v_snd_3252_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v___x_3257_);
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3259_ = v___x_3254_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3262_, lean_object* v___x_3263_){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3265_ = lean_st_ref_get(v___x_3262_);
v___x_3266_ = lean_mk_empty_array_with_capacity(v___x_3263_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___x_3265_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3269_, v___x_3270_);
lean_dec(v___x_3270_);
lean_dec(v___x_3269_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(lean_object* v_as_3273_, size_t v_i_3274_, size_t v_stop_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v___x_3279_; 
v___x_3279_ = lean_usize_dec_eq(v_i_3274_, v_stop_3275_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_array_uget_borrowed(v_as_3273_, v_i_3274_);
lean_inc(v___x_3280_);
v___x_3281_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v___x_3280_, v___y_3277_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = lean_array_push(v_b_3276_, v_a_3282_);
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3274_, v___x_3284_);
v_i_3274_ = v___x_3285_;
v_b_3276_ = v___x_3283_;
goto _start;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v_b_3276_);
v_a_3287_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3281_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3281_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_b_3276_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_3296_, lean_object* v_i_3297_, lean_object* v_stop_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
size_t v_i_boxed_3302_; size_t v_stop_boxed_3303_; lean_object* v_res_3304_; 
v_i_boxed_3302_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_stop_boxed_3303_ = lean_unbox_usize(v_stop_3298_);
lean_dec(v_stop_3298_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v_as_3296_, v_i_boxed_3302_, v_stop_boxed_3303_, v_b_3299_, v___y_3300_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v_as_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(lean_object* v_as_3305_, size_t v_i_3306_, size_t v_stop_3307_, lean_object* v_b_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_a_3312_; uint8_t v___x_3316_; 
v___x_3316_ = lean_usize_dec_eq(v_i_3306_, v_stop_3307_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_array_uget_borrowed(v_as_3305_, v_i_3306_);
v___x_3319_ = lean_array_get_size(v___x_3318_);
v___x_3320_ = lean_nat_dec_lt(v___x_3317_, v___x_3319_);
if (v___x_3320_ == 0)
{
v_a_3312_ = v_b_3308_;
goto v___jp_3311_;
}
else
{
size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3319_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v___x_3318_, v___x_3321_, v___x_3322_, v_b_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v_a_3312_ = v_a_3324_;
goto v___jp_3311_;
}
else
{
return v___x_3323_;
}
}
}
else
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_b_3308_);
return v___x_3325_;
}
v___jp_3311_:
{
size_t v___x_3313_; size_t v___x_3314_; 
v___x_3313_ = ((size_t)1ULL);
v___x_3314_ = lean_usize_add(v_i_3306_, v___x_3313_);
v_i_3306_ = v___x_3314_;
v_b_3308_ = v_a_3312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_3326_, lean_object* v_i_3327_, lean_object* v_stop_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
size_t v_i_boxed_3332_; size_t v_stop_boxed_3333_; lean_object* v_res_3334_; 
v_i_boxed_3332_ = lean_unbox_usize(v_i_3327_);
lean_dec(v_i_3327_);
v_stop_boxed_3333_ = lean_unbox_usize(v_stop_3328_);
lean_dec(v_stop_3328_);
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3326_, v_i_boxed_3332_, v_stop_boxed_3333_, v_b_3329_, v___y_3330_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v_as_3326_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_as_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_a_3341_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3345_ = lean_st_ref_get(v___x_3336_);
v___x_3346_ = lean_array_get_size(v_as_3337_);
v___x_3347_ = lean_nat_dec_lt(v___x_3335_, v___x_3346_);
if (v___x_3347_ == 0)
{
v_a_3341_ = v___x_3345_;
goto v___jp_3340_;
}
else
{
size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((size_t)0ULL);
v___x_3349_ = lean_usize_of_nat(v___x_3346_);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3337_, v___x_3348_, v___x_3349_, v___x_3345_, v___y_3338_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v_a_3341_ = v_a_3351_;
goto v___jp_3340_;
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_a_3352_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3350_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3350_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
v___jp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_mk_empty_array_with_capacity(v___x_3335_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v_a_3341_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3360_, lean_object* v___x_3361_, lean_object* v_as_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3360_, v___x_3361_, v_as_3362_, v___y_3363_);
lean_dec_ref(v___y_3363_);
lean_dec_ref(v_as_3362_);
lean_dec(v___x_3361_);
lean_dec(v___x_3360_);
return v_res_3365_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; 
v___x_3374_ = lean_unsigned_to_nat(0u);
v___x_3375_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_3376_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_3376_, 0, v___x_3375_);
lean_closure_set(v___f_3376_, 1, v___x_3374_);
return v___f_3376_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___f_3379_; 
v___x_3377_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3378_ = lean_unsigned_to_nat(0u);
v___f_3379_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_3379_, 0, v___x_3378_);
lean_closure_set(v___f_3379_, 1, v___x_3377_);
return v___f_3379_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3380_ = 0;
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_box(2);
v___f_3383_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3384_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3385_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3386_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___f_3387_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3389_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___f_3387_);
lean_ctor_set(v___x_3389_, 2, v___f_3386_);
lean_ctor_set(v___x_3389_, 3, v___f_3385_);
lean_ctor_set(v___x_3389_, 4, v___f_3384_);
lean_ctor_set(v___x_3389_, 5, v___f_3383_);
lean_ctor_set(v___x_3389_, 6, v___x_3382_);
lean_ctor_set(v___x_3389_, 7, v___x_3381_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*8, v___x_3380_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*8 + 1, v___x_3380_);
return v___x_3389_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___f_3390_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3391_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___f_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3395_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_name_3398_, lean_object* v_decl_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3404_ = l_Lean_MessageData_ofName(v_name_3398_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3407_, v___y_3400_, v___y_3401_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_name_3409_, lean_object* v_decl_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_name_3409_, v_decl_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v_decl_3410_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_addEntryFn_3415_, lean_object* v___x_3416_, lean_object* v_s_3417_){
_start:
{
lean_object* v_importedEntries_3418_; lean_object* v_state_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3427_; 
v_importedEntries_3418_ = lean_ctor_get(v_s_3417_, 0);
v_state_3419_ = lean_ctor_get(v_s_3417_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_s_3417_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3421_ = v_s_3417_;
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_state_3419_);
lean_inc(v_importedEntries_3418_);
lean_dec(v_s_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_state_3423_; lean_object* v___x_3425_; 
v_state_3423_ = lean_apply_2(v_addEntryFn_3415_, v_state_3419_, v___x_3416_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v_state_3423_);
v___x_3425_ = v___x_3421_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_importedEntries_3418_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_state_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3429_, lean_object* v___x_3430_, lean_object* v___x_3431_, lean_object* v___x_3432_, lean_object* v_name_3433_, lean_object* v_decl_3434_, lean_object* v_stx_3435_, uint8_t v_kind_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3435_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_dec_ref_known(v___x_3508_, 1);
if (v_builtin_3429_ == 0)
{
lean_object* v___x_3509_; 
lean_inc(v_decl_3434_);
lean_inc(v_name_3433_);
v___x_3509_ = l_Lean_ensureAttrDeclIsMeta(v_name_3433_, v_decl_3434_, v_kind_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_dec_ref_known(v___x_3509_, 1);
goto v___jp_3504_;
}
else
{
lean_dec(v_decl_3434_);
lean_dec(v_name_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec(v___x_3430_);
return v___x_3509_;
}
}
else
{
goto v___jp_3504_;
}
}
else
{
lean_dec(v_decl_3434_);
lean_dec(v_name_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec(v___x_3430_);
return v___x_3508_;
}
v___jp_3440_:
{
if (v_builtin_3429_ == 0)
{
lean_object* v___x_3443_; lean_object* v_env_3444_; lean_object* v___x_3445_; lean_object* v_env_3446_; lean_object* v_ref_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
v___x_3443_ = lean_st_ref_get(v___y_3442_);
v_env_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_ref(v_env_3444_);
lean_dec(v___x_3443_);
v___x_3445_ = lean_st_ref_get(v___y_3442_);
v_env_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc_ref(v_env_3446_);
lean_dec(v___x_3445_);
v_ref_3447_ = lean_ctor_get(v___y_3441_, 2);
v___x_3448_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3441_);
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_env_3446_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
lean_inc(v_decl_3434_);
v___x_3450_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_decl_3434_, v___x_3449_);
lean_dec_ref_known(v___x_3449_, 2);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v_toEnvExtension_3453_; lean_object* v_addEntryFn_3454_; lean_object* v_asyncMode_3455_; uint8_t v_logWrites_3456_; lean_object* v___x_3457_; lean_object* v___f_3458_; uint8_t v___x_3459_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3453_ = lean_ctor_get(v___x_3452_, 0);
v_addEntryFn_3454_ = lean_ctor_get(v___x_3452_, 3);
v_asyncMode_3455_ = lean_ctor_get(v_toEnvExtension_3453_, 2);
v_logWrites_3456_ = lean_ctor_get_uint8(v_toEnvExtension_3453_, sizeof(void*)*6);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_decl_3434_);
lean_ctor_set(v___x_3457_, 1, v_a_3451_);
lean_inc(v_addEntryFn_3454_);
v___f_3458_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_3458_, 0, v_addEntryFn_3454_);
lean_closure_set(v___f_3458_, 1, v___x_3457_);
v___x_3459_ = 1;
if (v_logWrites_3456_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_inc_ref(v_toEnvExtension_3453_);
v___x_3460_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3453_, v_env_3444_, v___f_3458_, v_asyncMode_3455_, v___x_3430_, v___x_3459_);
v___x_3461_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3460_, v___y_3442_);
return v___x_3461_;
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_inc_ref_n(v_toEnvExtension_3453_, 2);
v___x_3462_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3453_, v_env_3444_);
lean_dec_ref(v_env_3444_);
v___x_3463_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3453_, v___x_3462_, v___f_3458_, v_asyncMode_3455_, v___x_3430_, v___x_3459_);
v___x_3464_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3463_, v___y_3442_);
return v___x_3464_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v_env_3444_);
lean_dec(v_decl_3434_);
lean_dec(v___x_3430_);
v_a_3465_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3467_ = v___x_3450_;
v_isShared_3468_ = v_isSharedCheck_3476_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3450_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3476_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3469_ = lean_io_error_to_string(v_a_3465_);
v___x_3470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
v___x_3471_ = l_Lean_MessageData_ofFormat(v___x_3470_);
lean_inc(v_ref_3447_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_ref_3447_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3472_);
v___x_3474_ = v___x_3467_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v___x_3430_);
v___x_3477_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3478_ = l_Lean_Name_mkStr3(v___x_3431_, v___x_3432_, v___x_3477_);
v___x_3479_ = lean_box(0);
v___x_3480_ = l_Lean_mkConst(v___x_3478_, v___x_3479_);
lean_inc(v_decl_3434_);
v___x_3481_ = l_Lean_mkConst(v_decl_3434_, v___x_3479_);
v___x_3482_ = l_Lean_Expr_app___override(v___x_3480_, v___x_3481_);
v___x_3483_ = l_Lean_declareBuiltin(v_decl_3434_, v___x_3482_, v___y_3441_, v___y_3442_);
return v___x_3483_;
}
}
v___jp_3484_:
{
lean_object* v___x_3487_; 
lean_inc(v_decl_3434_);
v___x_3487_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_3434_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l_Lean_ConstantInfo_type(v_a_3488_);
lean_dec(v_a_3488_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0));
lean_inc_ref(v___x_3432_);
lean_inc_ref(v___x_3431_);
v___x_3491_ = l_Lean_Name_mkStr3(v___x_3431_, v___x_3432_, v___x_3490_);
v___x_3492_ = l_Lean_Expr_isConstOf(v___x_3489_, v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec(v___x_3430_);
v___x_3493_ = lean_box(0);
v___x_3494_ = l_Lean_mkConst(v___x_3491_, v___x_3493_);
v___x_3495_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_name_3433_, v_decl_3434_, v___x_3489_, v___x_3494_, v___y_3485_, v___y_3486_);
return v___x_3495_;
}
else
{
lean_dec(v___x_3491_);
lean_dec_ref(v___x_3489_);
lean_dec(v_name_3433_);
v___y_3441_ = v___y_3485_;
v___y_3442_ = v___y_3486_;
goto v___jp_3440_;
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_decl_3434_);
lean_dec(v_name_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec(v___x_3430_);
v_a_3496_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3487_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3487_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
v___jp_3504_:
{
uint8_t v___x_3505_; uint8_t v___x_3506_; 
v___x_3505_ = 0;
v___x_3506_ = l_Lean_instBEqAttributeKind_beq(v_kind_3436_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v_decl_3434_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec(v___x_3430_);
v___x_3507_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_3433_, v_kind_3436_, v___y_3437_, v___y_3438_);
return v___x_3507_;
}
else
{
v___y_3485_ = v___y_3437_;
v___y_3486_ = v___y_3438_;
goto v___jp_3484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3510_, lean_object* v___x_3511_, lean_object* v___x_3512_, lean_object* v___x_3513_, lean_object* v_name_3514_, lean_object* v_decl_3515_, lean_object* v_stx_3516_, lean_object* v_kind_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v_builtin_boxed_3521_; uint8_t v_kind_boxed_3522_; lean_object* v_res_3523_; 
v_builtin_boxed_3521_ = lean_unbox(v_builtin_3510_);
v_kind_boxed_3522_ = lean_unbox(v_kind_3517_);
v_res_3523_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3521_, v___x_3511_, v___x_3512_, v___x_3513_, v_name_3514_, v_decl_3515_, v_stx_3516_, v_kind_boxed_3522_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3538_, lean_object* v_name_3539_){
_start:
{
lean_object* v___f_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v___y_3549_; 
lean_inc_n(v_name_3539_, 2);
v___f_3541_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3541_, 0, v_name_3539_);
v___x_3542_ = lean_box(0);
v___x_3543_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0));
v___x_3544_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1));
v___x_3545_ = lean_box(v_builtin_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_3546_, 0, v___x_3545_);
lean_closure_set(v___f_3546_, 1, v___x_3542_);
lean_closure_set(v___f_3546_, 2, v___x_3543_);
lean_closure_set(v___f_3546_, 3, v___x_3544_);
lean_closure_set(v___f_3546_, 4, v_name_3539_);
v___x_3547_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
if (v_builtin_3538_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___y_3549_ = v___x_3556_;
goto v___jp_3548_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___y_3549_ = v___x_3557_;
goto v___jp_3548_;
}
v___jp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3550_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
lean_inc_ref(v___y_3549_);
v___x_3551_ = lean_string_append(v___y_3549_, v___x_3550_);
v___x_3552_ = 1;
v___x_3553_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3553_, 0, v___x_3547_);
lean_ctor_set(v___x_3553_, 1, v_name_3539_);
lean_ctor_set(v___x_3553_, 2, v___x_3551_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*3, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
lean_ctor_set(v___x_3554_, 1, v___f_3546_);
lean_ctor_set(v___x_3554_, 2, v___f_3541_);
v___x_3555_ = l_Lean_registerBuiltinAttribute(v___x_3554_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3558_, lean_object* v_name_3559_, lean_object* v___y_3560_){
_start:
{
uint8_t v_builtin_boxed_3561_; lean_object* v_res_3562_; 
v_builtin_boxed_3561_ = lean_unbox(v_builtin_3558_);
v_res_3562_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3561_, v_name_3559_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = 1;
v___x_3571_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3572_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3570_, v___x_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec_ref_known(v___x_3572_, 1);
v___x_3573_ = 0;
v___x_3574_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3575_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3573_, v___x_3574_);
return v___x_3575_;
}
else
{
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
return v_res_3577_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object* v_t_3578_, lean_object* v_as_3579_, size_t v_i_3580_, size_t v_stop_3581_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_eq(v_i_3580_, v_stop_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_158__overap_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_158__overap_3583_ = lean_array_uget_borrowed(v_as_3579_, v_i_3580_);
lean_inc(v___x_158__overap_3583_);
lean_inc(v_t_3578_);
v___x_3584_ = lean_apply_1(v___x_158__overap_3583_, v_t_3578_);
v___x_3585_ = lean_unbox(v___x_3584_);
if (v___x_3585_ == 0)
{
size_t v___x_3586_; size_t v___x_3587_; 
v___x_3586_ = ((size_t)1ULL);
v___x_3587_ = lean_usize_add(v_i_3580_, v___x_3586_);
v_i_3580_ = v___x_3587_;
goto _start;
}
else
{
uint8_t v___x_3589_; 
lean_dec(v_t_3578_);
v___x_3589_ = lean_unbox(v___x_3584_);
return v___x_3589_;
}
}
else
{
uint8_t v___x_3590_; 
lean_dec(v_t_3578_);
v___x_3590_ = 0;
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object* v_t_3591_, lean_object* v_as_3592_, lean_object* v_i_3593_, lean_object* v_stop_3594_){
_start:
{
size_t v_i_boxed_3595_; size_t v_stop_boxed_3596_; uint8_t v_res_3597_; lean_object* v_r_3598_; 
v_i_boxed_3595_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_stop_boxed_3596_ = lean_unbox_usize(v_stop_3594_);
lean_dec(v_stop_3594_);
v_res_3597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3591_, v_as_3592_, v_i_boxed_3595_, v_stop_boxed_3596_);
lean_dec_ref(v_as_3592_);
v_r_3598_ = lean_box(v_res_3597_);
return v_r_3598_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object* v_env_3599_, lean_object* v_t_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v_toEnvExtension_3602_; lean_object* v_asyncMode_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; lean_object* v_snd_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3601_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3602_ = lean_ctor_get(v___x_3601_, 0);
v_asyncMode_3603_ = lean_ctor_get(v_toEnvExtension_3602_, 2);
v___x_3604_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_3605_ = lean_box(0);
v___x_3606_ = 0;
v___x_3607_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3604_, v___x_3601_, v_env_3599_, v_asyncMode_3603_, v___x_3605_, v___x_3606_);
v_snd_3608_ = lean_ctor_get(v___x_3607_, 1);
lean_inc(v_snd_3608_);
lean_dec(v___x_3607_);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = lean_array_get_size(v_snd_3608_);
v___x_3611_ = lean_nat_dec_lt(v___x_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_dec(v_snd_3608_);
lean_dec(v_t_3600_);
return v___x_3611_;
}
else
{
if (v___x_3611_ == 0)
{
lean_dec(v_snd_3608_);
lean_dec(v_t_3600_);
return v___x_3611_;
}
else
{
size_t v___x_3612_; size_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_usize_of_nat(v___x_3610_);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3600_, v_snd_3608_, v___x_3612_, v___x_3613_);
lean_dec(v_snd_3608_);
return v___x_3614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object* v_env_3615_, lean_object* v_t_3616_){
_start:
{
uint8_t v_res_3617_; lean_object* v_r_3618_; 
v_res_3617_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_3615_, v_t_3616_);
v_r_3618_ = lean_box(v_res_3617_);
return v_r_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(uint8_t v_x_3619_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_box(v_x_3619_);
v___x_3621_ = lean_obj_tag_nat(v___x_3620_);
lean_dec(v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl___boxed(lean_object* v_x_3622_){
_start:
{
uint8_t v_x_4__boxed_3623_; lean_object* v_res_3624_; 
v_x_4__boxed_3623_ = lean_unbox(v_x_3622_);
v_res_3624_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(v_x_4__boxed_3623_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object* v_k_3625_){
_start:
{
lean_inc(v_k_3625_);
return v_k_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object* v_k_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(v_k_3626_);
lean_dec(v_k_3626_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object* v_motive_3628_, lean_object* v_ctorIdx_3629_, uint8_t v_t_3630_, lean_object* v_h_3631_, lean_object* v_k_3632_){
_start:
{
lean_inc(v_k_3632_);
return v_k_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object* v_motive_3633_, lean_object* v_ctorIdx_3634_, lean_object* v_t_3635_, lean_object* v_h_3636_, lean_object* v_k_3637_){
_start:
{
uint8_t v_t_boxed_3638_; lean_object* v_res_3639_; 
v_t_boxed_3638_ = lean_unbox(v_t_3635_);
v_res_3639_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim(v_motive_3633_, v_ctorIdx_3634_, v_t_boxed_3638_, v_h_3636_, v_k_3637_);
lean_dec(v_k_3637_);
lean_dec(v_ctorIdx_3634_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object* v_left_3640_){
_start:
{
lean_inc(v_left_3640_);
return v_left_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object* v_left_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(v_left_3641_);
lean_dec(v_left_3641_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object* v_motive_3643_, uint8_t v_t_3644_, lean_object* v_h_3645_, lean_object* v_left_3646_){
_start:
{
lean_inc(v_left_3646_);
return v_left_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object* v_motive_3647_, lean_object* v_t_3648_, lean_object* v_h_3649_, lean_object* v_left_3650_){
_start:
{
uint8_t v_t_boxed_3651_; lean_object* v_res_3652_; 
v_t_boxed_3651_ = lean_unbox(v_t_3648_);
v_res_3652_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim(v_motive_3647_, v_t_boxed_3651_, v_h_3649_, v_left_3650_);
lean_dec(v_left_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object* v_right_3653_){
_start:
{
lean_inc(v_right_3653_);
return v_right_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object* v_right_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(v_right_3654_);
lean_dec(v_right_3654_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object* v_motive_3656_, uint8_t v_t_3657_, lean_object* v_h_3658_, lean_object* v_right_3659_){
_start:
{
lean_inc(v_right_3659_);
return v_right_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object* v_motive_3660_, lean_object* v_t_3661_, lean_object* v_h_3662_, lean_object* v_right_3663_){
_start:
{
uint8_t v_t_boxed_3664_; lean_object* v_res_3665_; 
v_t_boxed_3664_ = lean_unbox(v_t_3661_);
v_res_3665_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim(v_motive_3660_, v_t_boxed_3664_, v_h_3662_, v_right_3663_);
lean_dec(v_right_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object* v_middle_3666_){
_start:
{
lean_inc(v_middle_3666_);
return v_middle_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object* v_middle_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(v_middle_3667_);
lean_dec(v_middle_3667_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object* v_motive_3669_, uint8_t v_t_3670_, lean_object* v_h_3671_, lean_object* v_middle_3672_){
_start:
{
lean_inc(v_middle_3672_);
return v_middle_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object* v_motive_3673_, lean_object* v_t_3674_, lean_object* v_h_3675_, lean_object* v_middle_3676_){
_start:
{
uint8_t v_t_boxed_3677_; lean_object* v_res_3678_; 
v_t_boxed_3677_ = lean_unbox(v_t_3674_);
v_res_3678_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim(v_motive_3673_, v_t_boxed_3677_, v_h_3675_, v_middle_3676_);
lean_dec(v_middle_3676_);
return v_res_3678_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default(void){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = 0;
return v___x_3679_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity(void){
_start:
{
uint8_t v___x_3680_; 
v___x_3680_ = 0;
return v___x_3680_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t v_x_3681_, uint8_t v_y_3682_){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3683_ = lean_box(v_x_3681_);
v___x_3684_ = lean_obj_tag_nat(v___x_3683_);
lean_dec(v___x_3683_);
v___x_3685_ = lean_box(v_y_3682_);
v___x_3686_ = lean_obj_tag_nat(v___x_3685_);
lean_dec(v___x_3685_);
v___x_3687_ = lean_nat_dec_eq(v___x_3684_, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object* v_x_3688_, lean_object* v_y_3689_){
_start:
{
uint8_t v_x_24__boxed_3690_; uint8_t v_y_25__boxed_3691_; uint8_t v_res_3692_; lean_object* v_r_3693_; 
v_x_24__boxed_3690_ = lean_unbox(v_x_3688_);
v_y_25__boxed_3691_ = lean_unbox(v_y_3689_);
v_res_3692_ = l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(v_x_24__boxed_3690_, v_y_25__boxed_3691_);
v_r_3693_ = lean_box(v_res_3692_);
return v_r_3693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object* v_x_3700_, lean_object* v_x_3701_){
_start:
{
lean_object* v_prec_3702_; lean_object* v_lhsPrec_3703_; lean_object* v_rhsPrec_3704_; lean_object* v_prec_3705_; lean_object* v_lhsPrec_3706_; lean_object* v_rhsPrec_3707_; uint8_t v___x_3708_; 
v_prec_3702_ = lean_ctor_get(v_x_3700_, 0);
v_lhsPrec_3703_ = lean_ctor_get(v_x_3700_, 1);
v_rhsPrec_3704_ = lean_ctor_get(v_x_3700_, 2);
v_prec_3705_ = lean_ctor_get(v_x_3701_, 0);
v_lhsPrec_3706_ = lean_ctor_get(v_x_3701_, 1);
v_rhsPrec_3707_ = lean_ctor_get(v_x_3701_, 2);
v___x_3708_ = lean_nat_dec_eq(v_prec_3702_, v_prec_3705_);
if (v___x_3708_ == 0)
{
return v___x_3708_;
}
else
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_nat_dec_eq(v_lhsPrec_3703_, v_lhsPrec_3706_);
if (v___x_3709_ == 0)
{
return v___x_3709_;
}
else
{
uint8_t v___x_3710_; 
v___x_3710_ = lean_nat_dec_eq(v_rhsPrec_3704_, v_rhsPrec_3707_);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object* v_x_3711_, lean_object* v_x_3712_){
_start:
{
uint8_t v_res_3713_; lean_object* v_r_3714_; 
v_res_3713_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_x_3711_, v_x_3712_);
lean_dec_ref(v_x_3712_);
lean_dec_ref(v_x_3711_);
v_r_3714_ = lean_box(v_res_3713_);
return v_r_3714_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_unsigned_to_nat(16u);
v___x_3719_ = lean_mk_array(v___x_3718_, v___x_3717_);
return v___x_3719_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0);
v___x_3721_ = lean_unsigned_to_nat(0u);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3720_);
return v___x_3722_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3723_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1);
v___x_3724_ = lean_box(0);
v___x_3725_ = 0;
v___x_3726_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3723_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*2, v___x_3725_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*2 + 1, v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default(void){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2);
return v___x_3727_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation(void){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Fmt_instInhabitedInfixOperation_default;
return v___x_3728_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object* v_x_3729_, lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3729_) == 0)
{
if (lean_obj_tag(v_x_3730_) == 0)
{
uint8_t v___x_3731_; 
v___x_3731_ = 1;
return v___x_3731_;
}
else
{
uint8_t v___x_3732_; 
v___x_3732_ = 0;
return v___x_3732_;
}
}
else
{
if (lean_obj_tag(v_x_3730_) == 0)
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
return v___x_3733_;
}
else
{
lean_object* v_val_3734_; lean_object* v_val_3735_; uint8_t v___x_3736_; 
v_val_3734_ = lean_ctor_get(v_x_3729_, 0);
v_val_3735_ = lean_ctor_get(v_x_3730_, 0);
v___x_3736_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_3734_, v_val_3735_);
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_res_3739_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_x_3737_, v_x_3738_);
lean_dec(v_x_3738_);
lean_dec(v_x_3737_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_3741_, lean_object* v_x_3742_){
_start:
{
if (lean_obj_tag(v_x_3741_) == 0)
{
if (lean_obj_tag(v_x_3742_) == 0)
{
uint8_t v___x_3743_; 
v___x_3743_ = 1;
return v___x_3743_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = 0;
return v___x_3744_;
}
}
else
{
if (lean_obj_tag(v_x_3742_) == 0)
{
uint8_t v___x_3745_; 
v___x_3745_ = 0;
return v___x_3745_;
}
else
{
uint8_t v___x_3746_; 
v___x_3746_ = 1;
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_x_3747_, lean_object* v_x_3748_){
_start:
{
uint8_t v_res_3749_; lean_object* v_r_3750_; 
v_res_3749_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v_x_3747_, v_x_3748_);
lean_dec(v_x_3748_);
lean_dec(v_x_3747_);
v_r_3750_ = lean_box(v_res_3749_);
return v_r_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_m_u2082_3754_, lean_object* v___x_3755_, lean_object* v___x_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; uint8_t v___y_3762_; uint8_t v___x_3775_; 
v___x_3759_ = lean_box(0);
v___x_3760_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v___x_3775_ = lean_nat_dec_eq(v___x_3755_, v___x_3756_);
if (v___x_3775_ == 0)
{
uint8_t v___x_3776_; 
v___x_3776_ = 1;
v___y_3762_ = v___x_3776_;
goto v___jp_3761_;
}
else
{
uint8_t v___x_3777_; 
v___x_3777_ = 0;
v___y_3762_ = v___x_3777_;
goto v___jp_3761_;
}
v___jp_3761_:
{
if (lean_obj_tag(v_a_3757_) == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3758_);
return v___x_3763_;
}
else
{
lean_object* v_key_3764_; lean_object* v_value_3765_; lean_object* v_tail_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
lean_dec_ref(v_a_3758_);
v_key_3764_ = lean_ctor_get(v_a_3757_, 0);
v_value_3765_ = lean_ctor_get(v_a_3757_, 1);
v_tail_3766_ = lean_ctor_get(v_a_3757_, 2);
v___x_3767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_u2082_3754_, v_key_3764_);
lean_inc(v_value_3765_);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_value_3765_);
v___x_3769_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v___x_3767_, v___x_3768_);
lean_dec_ref_known(v___x_3768_, 1);
lean_dec(v___x_3767_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3770_ = lean_box(v___y_3762_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set(v___x_3772_, 1, v___x_3759_);
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
else
{
v_a_3757_ = v_tail_3766_;
v_a_3758_ = v___x_3760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_m_u2082_3778_, lean_object* v___x_3779_, lean_object* v___x_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3778_, v___x_3779_, v___x_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3781_);
lean_dec(v___x_3780_);
lean_dec(v___x_3779_);
lean_dec_ref(v_m_u2082_3778_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_m_u2082_3784_, lean_object* v___x_3785_, lean_object* v___x_3786_, lean_object* v_as_3787_, size_t v_sz_3788_, size_t v_i_3789_, lean_object* v_b_3790_){
_start:
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
if (v___x_3791_ == 0)
{
return v_b_3790_;
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3793_; 
v_a_3792_ = lean_array_uget_borrowed(v_as_3787_, v_i_3789_);
v___x_3793_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3784_, v___x_3785_, v___x_3786_, v_a_3792_, v_b_3790_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref_known(v___x_3793_, 1);
return v_a_3794_;
}
else
{
lean_object* v_a_3795_; size_t v___x_3796_; size_t v___x_3797_; 
v_a_3795_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3789_, v___x_3796_);
v_i_3789_ = v___x_3797_;
v_b_3790_ = v_a_3795_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_m_u2082_3799_, lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v_as_3802_, lean_object* v_sz_3803_, lean_object* v_i_3804_, lean_object* v_b_3805_){
_start:
{
size_t v_sz_boxed_3806_; size_t v_i_boxed_3807_; lean_object* v_res_3808_; 
v_sz_boxed_3806_ = lean_unbox_usize(v_sz_3803_);
lean_dec(v_sz_3803_);
v_i_boxed_3807_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_res_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3799_, v___x_3800_, v___x_3801_, v_as_3802_, v_sz_boxed_3806_, v_i_boxed_3807_, v_b_3805_);
lean_dec_ref(v_as_3802_);
lean_dec(v___x_3801_);
lean_dec(v___x_3800_);
lean_dec_ref(v_m_u2082_3799_);
return v_res_3808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object* v_m_u2081_3809_, lean_object* v_m_u2082_3810_){
_start:
{
lean_object* v_size_3811_; lean_object* v_buckets_3812_; lean_object* v_size_3813_; uint8_t v___x_3814_; 
v_size_3811_ = lean_ctor_get(v_m_u2081_3809_, 0);
v_buckets_3812_ = lean_ctor_get(v_m_u2081_3809_, 1);
v_size_3813_ = lean_ctor_get(v_m_u2082_3810_, 0);
v___x_3814_ = lean_nat_dec_eq(v_size_3811_, v_size_3813_);
if (v___x_3814_ == 0)
{
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; size_t v_sz_3816_; size_t v___x_3817_; lean_object* v___x_3818_; lean_object* v_fst_3819_; 
v___x_3815_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v_sz_3816_ = lean_array_size(v_buckets_3812_);
v___x_3817_ = ((size_t)0ULL);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3810_, v_size_3811_, v_size_3813_, v_buckets_3812_, v_sz_3816_, v___x_3817_, v___x_3815_);
v_fst_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_fst_3819_);
lean_dec_ref(v___x_3818_);
if (lean_obj_tag(v_fst_3819_) == 0)
{
return v___x_3814_;
}
else
{
lean_object* v_val_3820_; uint8_t v___x_3821_; 
v_val_3820_ = lean_ctor_get(v_fst_3819_, 0);
lean_inc(v_val_3820_);
lean_dec_ref_known(v_fst_3819_, 1);
v___x_3821_ = lean_unbox(v_val_3820_);
lean_dec(v_val_3820_);
return v___x_3821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_m_u2081_3822_, lean_object* v_m_u2082_3823_){
_start:
{
uint8_t v_res_3824_; lean_object* v_r_3825_; 
v_res_3824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3822_, v_m_u2082_3823_);
lean_dec_ref(v_m_u2082_3823_);
lean_dec_ref(v_m_u2081_3822_);
v_r_3825_ = lean_box(v_res_3824_);
return v_r_3825_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object* v_m_u2081_3826_, lean_object* v_m_u2082_3827_){
_start:
{
uint8_t v___x_3828_; 
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3826_, v_m_u2082_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object* v_m_u2081_3829_, lean_object* v_m_u2082_3830_){
_start:
{
uint8_t v_res_3831_; lean_object* v_r_3832_; 
v_res_3831_ = l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(v_m_u2081_3829_, v_m_u2082_3830_);
lean_dec_ref(v_m_u2082_3830_);
lean_dec_ref(v_m_u2081_3829_);
v_r_3832_ = lean_box(v_res_3831_);
return v_r_3832_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object* v_m_u2081_3833_, lean_object* v_m_u2082_3834_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3833_, v_m_u2082_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object* v_m_u2081_3836_, lean_object* v_m_u2082_3837_){
_start:
{
uint8_t v_res_3838_; lean_object* v_r_3839_; 
v_res_3838_ = l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(v_m_u2081_3836_, v_m_u2082_3837_);
lean_dec_ref(v_m_u2082_3837_);
lean_dec_ref(v_m_u2081_3836_);
v_r_3839_ = lean_box(v_res_3838_);
return v_r_3839_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object* v_m_u2081_3840_, lean_object* v_m_u2082_3841_){
_start:
{
uint8_t v___x_3842_; 
v___x_3842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3840_, v_m_u2082_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object* v_m_u2081_3843_, lean_object* v_m_u2082_3844_){
_start:
{
uint8_t v_res_3845_; lean_object* v_r_3846_; 
v_res_3845_ = l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(v_m_u2081_3843_, v_m_u2082_3844_);
lean_dec_ref(v_m_u2082_3844_);
lean_dec_ref(v_m_u2081_3843_);
v_r_3846_ = lean_box(v_res_3845_);
return v_r_3846_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
uint8_t v_sparse_3849_; uint8_t v_separateFinalOperand_3850_; lean_object* v_precs_x3f_3851_; lean_object* v_extendedChainKinds_3852_; uint8_t v_sparse_3853_; uint8_t v_separateFinalOperand_3854_; lean_object* v_precs_x3f_3855_; lean_object* v_extendedChainKinds_3856_; 
v_sparse_3849_ = lean_ctor_get_uint8(v_x_3847_, sizeof(void*)*2);
v_separateFinalOperand_3850_ = lean_ctor_get_uint8(v_x_3847_, sizeof(void*)*2 + 1);
v_precs_x3f_3851_ = lean_ctor_get(v_x_3847_, 0);
v_extendedChainKinds_3852_ = lean_ctor_get(v_x_3847_, 1);
v_sparse_3853_ = lean_ctor_get_uint8(v_x_3848_, sizeof(void*)*2);
v_separateFinalOperand_3854_ = lean_ctor_get_uint8(v_x_3848_, sizeof(void*)*2 + 1);
v_precs_x3f_3855_ = lean_ctor_get(v_x_3848_, 0);
v_extendedChainKinds_3856_ = lean_ctor_get(v_x_3848_, 1);
if (v_sparse_3853_ == 0)
{
if (v_sparse_3849_ == 0)
{
goto v___jp_3860_;
}
else
{
return v_sparse_3853_;
}
}
else
{
if (v_sparse_3849_ == 0)
{
return v_sparse_3849_;
}
else
{
goto v___jp_3860_;
}
}
v___jp_3857_:
{
uint8_t v___x_3858_; 
v___x_3858_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_precs_x3f_3851_, v_precs_x3f_3855_);
if (v___x_3858_ == 0)
{
return v___x_3858_;
}
else
{
uint8_t v___x_3859_; 
v___x_3859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_extendedChainKinds_3852_, v_extendedChainKinds_3856_);
return v___x_3859_;
}
}
v___jp_3860_:
{
if (v_separateFinalOperand_3854_ == 0)
{
if (v_separateFinalOperand_3850_ == 0)
{
goto v___jp_3857_;
}
else
{
return v_separateFinalOperand_3854_;
}
}
else
{
if (v_separateFinalOperand_3850_ == 0)
{
return v_separateFinalOperand_3850_;
}
else
{
goto v___jp_3857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object* v_x_3861_, lean_object* v_x_3862_){
_start:
{
uint8_t v_res_3863_; lean_object* v_r_3864_; 
v_res_3863_ = l_Lean_Fmt_instBEqInfixOperation_beq(v_x_3861_, v_x_3862_);
lean_dec_ref(v_x_3862_);
lean_dec_ref(v_x_3861_);
v_r_3864_ = lean_box(v_res_3863_);
return v_r_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3896_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3897_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3895_, v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2____boxed(lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3929_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3930_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3928_, v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2____boxed(lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(lean_object* v_x_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_obj_tag_nat(v_x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl___boxed(lean_object* v_x_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(v_x_3935_);
lean_dec_ref(v_x_3935_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object* v_t_3937_, lean_object* v_k_3938_){
_start:
{
if (lean_obj_tag(v_t_3937_) == 0)
{
lean_object* v_group_3939_; lean_object* v___x_3940_; 
v_group_3939_ = lean_ctor_get(v_t_3937_, 0);
lean_inc_ref(v_group_3939_);
lean_dec_ref_known(v_t_3937_, 1);
v___x_3940_ = lean_apply_1(v_k_3938_, v_group_3939_);
return v___x_3940_;
}
else
{
lean_object* v_lhs_3941_; lean_object* v_rhs_3942_; lean_object* v___x_3943_; 
v_lhs_3941_ = lean_ctor_get(v_t_3937_, 0);
lean_inc(v_lhs_3941_);
v_rhs_3942_ = lean_ctor_get(v_t_3937_, 1);
lean_inc(v_rhs_3942_);
lean_dec_ref_known(v_t_3937_, 2);
v___x_3943_ = lean_apply_2(v_k_3938_, v_lhs_3941_, v_rhs_3942_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object* v_motive_3944_, lean_object* v_ctorIdx_3945_, lean_object* v_t_3946_, lean_object* v_h_3947_, lean_object* v_k_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3946_, v_k_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object* v_motive_3950_, lean_object* v_ctorIdx_3951_, lean_object* v_t_3952_, lean_object* v_h_3953_, lean_object* v_k_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Fmt_QuantifierBinders_ctorElim(v_motive_3950_, v_ctorIdx_3951_, v_t_3952_, v_h_3953_, v_k_3954_);
lean_dec(v_ctorIdx_3951_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object* v_t_3956_, lean_object* v_binders_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3956_, v_binders_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object* v_motive_3959_, lean_object* v_t_3960_, lean_object* v_h_3961_, lean_object* v_binders_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3960_, v_binders_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object* v_t_3964_, lean_object* v_pred_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3964_, v_pred_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object* v_motive_3967_, lean_object* v_t_3968_, lean_object* v_h_3969_, lean_object* v_pred_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3968_, v_pred_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_4001_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_4002_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4000_, v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2____boxed(lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
return v_res_4004_;
}
}
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedRangeKind_default = _init_l_Lean_Fmt_instInhabitedRangeKind_default();
l_Lean_Fmt_instInhabitedRangeKind = _init_l_Lean_Fmt_instInhabitedRangeKind();
l_Lean_Fmt_instInhabitedBacktrackableState_default = _init_l_Lean_Fmt_instInhabitedBacktrackableState_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedBacktrackableState_default);
l_Lean_Fmt_instInhabitedBacktrackableState = _init_l_Lean_Fmt_instInhabitedBacktrackableState();
lean_mark_persistent(l_Lean_Fmt_instInhabitedBacktrackableState);
l_Lean_Fmt_instInhabitedState_default = _init_l_Lean_Fmt_instInhabitedState_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedState_default);
l_Lean_Fmt_instInhabitedState = _init_l_Lean_Fmt_instInhabitedState();
lean_mark_persistent(l_Lean_Fmt_instInhabitedState);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_Comment_instInhabitedWhitespace_default = _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default();
l_Lean_Fmt_Comment_instInhabitedWhitespace = _init_l_Lean_Fmt_Comment_instInhabitedWhitespace();
l_Lean_Fmt_Comment_instInhabitedPlacement_default = _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default();
l_Lean_Fmt_Comment_instInhabitedPlacement = _init_l_Lean_Fmt_Comment_instInhabitedPlacement();
l_Lean_Fmt_Comment_instInhabitedKind_default = _init_l_Lean_Fmt_Comment_instInhabitedKind_default();
l_Lean_Fmt_Comment_instInhabitedKind = _init_l_Lean_Fmt_Comment_instInhabitedKind();
l_Lean_Fmt_instInhabitedComment_default = _init_l_Lean_Fmt_instInhabitedComment_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedComment_default);
l_Lean_Fmt_instInhabitedComment = _init_l_Lean_Fmt_instInhabitedComment();
lean_mark_persistent(l_Lean_Fmt_instInhabitedComment);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_fmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_fmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default = _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default();
l_Lean_Fmt_instInhabitedInfixOperationAssociativity = _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity();
l_Lean_Fmt_instInhabitedInfixOperation_default = _init_l_Lean_Fmt_instInhabitedInfixOperation_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedInfixOperation_default);
l_Lean_Fmt_instInhabitedInfixOperation = _init_l_Lean_Fmt_instInhabitedInfixOperation();
lean_mark_persistent(l_Lean_Fmt_instInhabitedInfixOperation);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_infixFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_infixFmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_conditionalFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_conditionalFmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_quantifierFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_quantifierFmtAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Module(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Attribute(builtin);
}
#ifdef __cplusplus
}
#endif
