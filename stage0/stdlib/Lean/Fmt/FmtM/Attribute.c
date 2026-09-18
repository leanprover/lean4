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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
extern lean_object* l_Lean_Fmt_headerKind;
extern lean_object* l_Lean_Fmt_cmdsKind;
extern lean_object* l_Lean_Fmt_moduleKind;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_findChoiceResolution_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value)} };
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__value)} };
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
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "addBuiltinStickyTermFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1916596973) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(179, 4, 9, 36, 218, 22, 47, 250)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 254, 143, 77, 65, 149, 80, 160)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 217, 72, 220, 27, 233, 198, 218)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(21, 161, 79, 54, 3, 163, 193, 91)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "Marks a function of type `Lean.Fmt.StickyTermFn` that determines whether a term propagates the stickiness of its right-hand side in applications."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object* v_x_149_, lean_object* v_x_150_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v_x_157_, v_x_158_);
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
v___x_172_ = l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v___x_169_, v___x_171_);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx(uint8_t v_x_195_){
_start:
{
switch(v_x_195_)
{
case 0:
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(0u);
return v___x_196_;
}
case 1:
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(1u);
return v___x_197_;
}
default: 
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(2u);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___boxed(lean_object* v_x_199_){
_start:
{
uint8_t v_x_boxed_200_; lean_object* v_res_201_; 
v_x_boxed_200_ = lean_unbox(v_x_199_);
v_res_201_ = l_Lean_Fmt_RangeKind_ctorIdx(v_x_boxed_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg(lean_object* v_k_202_){
_start:
{
lean_inc(v_k_202_);
return v_k_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg___boxed(lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Fmt_RangeKind_ctorElim___redArg(v_k_203_);
lean_dec(v_k_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_inc(v_k_209_);
return v_k_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___boxed(lean_object* v_motive_210_, lean_object* v_ctorIdx_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_k_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_Fmt_RangeKind_ctorElim(v_motive_210_, v_ctorIdx_211_, v_t_boxed_215_, v_h_213_, v_k_214_);
lean_dec(v_k_214_);
lean_dec(v_ctorIdx_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg(lean_object* v_whitespace_217_){
_start:
{
lean_inc(v_whitespace_217_);
return v_whitespace_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg___boxed(lean_object* v_whitespace_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Fmt_RangeKind_whitespace_elim___redArg(v_whitespace_218_);
lean_dec(v_whitespace_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_whitespace_223_){
_start:
{
lean_inc(v_whitespace_223_);
return v_whitespace_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_whitespace_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_Fmt_RangeKind_whitespace_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_whitespace_227_);
lean_dec(v_whitespace_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg(lean_object* v_node_230_){
_start:
{
lean_inc(v_node_230_);
return v_node_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg___boxed(lean_object* v_node_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Fmt_RangeKind_node_elim___redArg(v_node_231_);
lean_dec(v_node_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_node_236_){
_start:
{
lean_inc(v_node_236_);
return v_node_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_node_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_Fmt_RangeKind_node_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_node_240_);
lean_dec(v_node_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg(lean_object* v_text_243_){
_start:
{
lean_inc(v_text_243_);
return v_text_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg___boxed(lean_object* v_text_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Fmt_RangeKind_text_elim___redArg(v_text_244_);
lean_dec(v_text_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_text_249_){
_start:
{
lean_inc(v_text_249_);
return v_text_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_text_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_Fmt_RangeKind_text_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_text_253_);
lean_dec(v_text_253_);
return v_res_255_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind_default(void){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind(void){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_unsigned_to_nat(16u);
v___x_260_ = lean_mk_array(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = l_Lean_ShareCommon_objectFactory;
v___x_267_ = l_ShareCommon_mkStateImpl(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__0, &l_Lean_Fmt_instInhabitedState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__0);
v___x_271_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
v___x_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_269_);
lean_ctor_set(v___x_272_, 3, v___x_268_);
lean_ctor_set(v___x_272_, 4, v___x_268_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__1, &l_Lean_Fmt_instInhabitedState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__1);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Fmt_instInhabitedState_default;
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object* v_s_275_){
_start:
{
lean_object* v_toBacktrackableState_276_; 
v_toBacktrackableState_276_ = lean_ctor_get(v_s_275_, 0);
lean_inc_ref(v_toBacktrackableState_276_);
return v_toBacktrackableState_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object* v_s_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(v_s_277_);
lean_dec_ref(v_s_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object* v_s_279_, lean_object* v_d_280_){
_start:
{
lean_object* v_shareCommonState_281_; lean_object* v_freshTagId_282_; lean_object* v_missingFormatters_283_; lean_object* v_partialFormatters_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_shareCommonState_281_ = lean_ctor_get(v_s_279_, 1);
v_freshTagId_282_ = lean_ctor_get(v_s_279_, 2);
v_missingFormatters_283_ = lean_ctor_get(v_s_279_, 3);
v_partialFormatters_284_ = lean_ctor_get(v_s_279_, 4);
v_isSharedCheck_291_ = !lean_is_exclusive(v_s_279_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_s_279_, 0);
lean_dec(v_unused_292_);
v___x_286_ = v_s_279_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_partialFormatters_284_);
lean_inc(v_missingFormatters_283_);
lean_inc(v_freshTagId_282_);
lean_inc(v_shareCommonState_281_);
lean_dec(v_s_279_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_d_280_);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_d_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_shareCommonState_281_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_freshTagId_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_missingFormatters_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_partialFormatters_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object* v_entry_304_, lean_object* v_as_305_, lean_object* v_j_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_as_305_);
v___x_308_ = lean_nat_dec_lt(v_j_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v_j_306_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v_priority_311_; lean_object* v_priority_312_; uint8_t v___x_313_; 
v___x_310_ = lean_array_fget_borrowed(v_as_305_, v_j_306_);
v_priority_311_ = lean_ctor_get(v___x_310_, 0);
v_priority_312_ = lean_ctor_get(v_entry_304_, 0);
v___x_313_ = lean_nat_dec_lt(v_priority_311_, v_priority_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_j_306_, v___x_314_);
lean_dec(v_j_306_);
v_j_306_ = v___x_315_;
goto _start;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_j_306_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object* v_entry_318_, lean_object* v_as_319_, lean_object* v_j_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_318_, v_as_319_, v_j_320_);
lean_dec_ref(v_as_319_);
lean_dec_ref(v_entry_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object* v_providers_322_, lean_object* v_entry_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_323_, v_providers_322_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_array_get_size(v_providers_322_);
v___x_327_ = l_Array_insertIdx_x21___redArg(v_providers_322_, v___x_326_, v_entry_323_);
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_329_; 
v_val_328_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_325_, 1);
v___x_329_ = l_Array_insertIdx_x21___redArg(v_providers_322_, v_val_328_, v_entry_323_);
lean_dec(v_val_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_));
v___x_334_ = lean_st_mk_ref(v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object* v_priority_338_, lean_object* v_provider_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_342_ = lean_st_ref_take(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_priority_338_);
lean_ctor_set(v___x_343_, 1, v_provider_339_);
v___x_344_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v___x_342_, v___x_343_);
v___x_345_ = lean_st_ref_put(v___x_341_, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object* v_priority_347_, lean_object* v_provider_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Fmt_addBuiltinFmtProvider(v_priority_347_, v_provider_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object* v_constName_358_, lean_object* v_env_359_, lean_object* v_opts_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
v___x_362_ = l_Lean_Environment_evalConstCheck___redArg(v_env_359_, v_opts_360_, v___x_361_, v_constName_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object* v_constName_363_, lean_object* v_env_364_, lean_object* v_opts_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(v_constName_363_, v_env_364_, v_opts_365_);
lean_dec_ref(v_opts_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object* v_e_367_){
_start:
{
if (lean_obj_tag(v_e_367_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_a_369_ = lean_ctor_get(v_e_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_e_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v_e_367_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v_e_367_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_mk_io_user_error(v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v_e_367_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_e_367_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v_e_367_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_e_367_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object* v_e_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object* v_00_u03b1_389_, lean_object* v_e_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object* v_00_u03b1_393_, lean_object* v_e_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(v_00_u03b1_393_, v_e_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object* v_constName_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_env_400_; lean_object* v_opts_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_env_400_ = lean_ctor_get(v_a_398_, 0);
v_opts_401_ = lean_ctor_get(v_a_398_, 1);
v___x_402_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
lean_inc_ref(v_env_400_);
v___x_403_ = l_Lean_Environment_evalConstCheck___redArg(v_env_400_, v_opts_401_, v___x_402_, v_constName_397_);
v___x_404_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object* v_constName_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_constName_405_, v_a_406_);
lean_dec_ref(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_409_){
_start:
{
lean_object* v_fst_410_; 
v_fst_410_ = lean_ctor_get(v_x_409_, 0);
lean_inc(v_fst_410_);
return v_fst_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_411_);
lean_dec_ref(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_415_);
lean_dec_ref(v_x_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_fst_419_; lean_object* v___x_420_; 
v_fst_419_ = lean_ctor_get(v_s_418_, 0);
lean_inc_n(v_fst_419_, 3);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v_fst_419_);
lean_ctor_set(v___x_420_, 1, v_fst_419_);
lean_ctor_set(v___x_420_, 2, v_fst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_421_, lean_object* v_s_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_421_, v_s_422_);
lean_dec_ref(v_s_422_);
lean_dec_ref(v_x_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_snd_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_447_; 
v_snd_426_ = lean_ctor_get(v_x_425_, 1);
lean_inc(v_snd_426_);
v_fst_427_ = lean_ctor_get(v_x_424_, 0);
v_snd_428_ = lean_ctor_get(v_x_424_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_447_ == 0)
{
v___x_430_ = v_x_424_;
v_isShared_431_ = v_isSharedCheck_447_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_447_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_445_; 
v_fst_432_ = lean_ctor_get(v_x_425_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_x_425_, 1);
lean_dec(v_unused_446_);
v___x_434_ = v_x_425_;
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_priority_436_; lean_object* v___x_438_; 
v_priority_436_ = lean_ctor_get(v_snd_426_, 0);
lean_inc(v_priority_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_priority_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_priority_436_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = lean_array_push(v_fst_427_, v___x_438_);
v___x_440_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_snd_428_, v_snd_426_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_440_);
lean_ctor_set(v___x_430_, 0, v___x_439_);
v___x_442_ = v___x_430_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_448_, lean_object* v___x_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_st_ref_get(v___x_448_);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_449_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_455_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(lean_object* v_as_459_, size_t v_i_460_, size_t v_stop_461_, lean_object* v_b_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_eq(v_i_460_, v_stop_461_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_489_; 
v___x_466_ = lean_array_uget(v_as_459_, v_i_460_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_489_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snd_468_);
lean_inc(v_fst_467_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_fst_467_, v___y_463_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_a_473_);
lean_ctor_set(v___x_470_, 0, v_snd_468_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_snd_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_a_473_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; size_t v___x_477_; size_t v___x_478_; 
v___x_476_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_b_462_, v___x_475_);
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_add(v_i_460_, v___x_477_);
v_i_460_ = v___x_478_;
v_b_462_ = v___x_476_;
goto _start;
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
lean_dec_ref(v_b_462_);
v_a_481_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_472_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_472_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_b_462_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v_i_boxed_497_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v_as_491_, v_i_boxed_497_, v_stop_boxed_498_, v_b_494_, v___y_495_);
lean_dec_ref(v___y_495_);
lean_dec_ref(v_as_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(lean_object* v_as_500_, size_t v_i_501_, size_t v_stop_502_, lean_object* v_b_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_a_507_; lean_object* v___y_512_; uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_501_, v_stop_502_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_array_uget_borrowed(v_as_500_, v_i_501_);
v___x_517_ = lean_array_get_size(v___x_516_);
v___x_518_ = lean_nat_dec_lt(v___x_515_, v___x_517_);
if (v___x_518_ == 0)
{
v_a_507_ = v_b_503_;
goto v___jp_506_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_517_);
if (v___x_519_ == 0)
{
if (v___x_518_ == 0)
{
v_a_507_ = v_b_503_;
goto v___jp_506_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_517_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v___x_516_, v___x_520_, v___x_521_, v_b_503_, v___y_504_);
v___y_512_ = v___x_522_;
goto v___jp_511_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_517_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v___x_516_, v___x_523_, v___x_524_, v_b_503_, v___y_504_);
v___y_512_ = v___x_525_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_b_503_);
return v___x_526_;
}
v___jp_506_:
{
size_t v___x_508_; size_t v___x_509_; 
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_501_, v___x_508_);
v_i_501_ = v___x_509_;
v_b_503_ = v_a_507_;
goto _start;
}
v___jp_511_:
{
if (lean_obj_tag(v___y_512_) == 0)
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v___y_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___y_512_, 1);
v_a_507_ = v_a_513_;
goto v___jp_506_;
}
else
{
return v___y_512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_527_, lean_object* v_i_528_, lean_object* v_stop_529_, lean_object* v_b_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
size_t v_i_boxed_533_; size_t v_stop_boxed_534_; lean_object* v_res_535_; 
v_i_boxed_533_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_stop_boxed_534_ = lean_unbox_usize(v_stop_529_);
lean_dec(v_stop_529_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_527_, v_i_boxed_533_, v_stop_boxed_534_, v_b_530_, v___y_531_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_as_527_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_as_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_a_542_; lean_object* v___y_547_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_st_ref_get(v___x_537_);
v___x_558_ = lean_array_get_size(v_as_538_);
v___x_559_ = lean_nat_dec_lt(v___x_536_, v___x_558_);
if (v___x_559_ == 0)
{
v_a_542_ = v___x_557_;
goto v___jp_541_;
}
else
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_le(v___x_558_, v___x_558_);
if (v___x_560_ == 0)
{
if (v___x_559_ == 0)
{
v_a_542_ = v___x_557_;
goto v___jp_541_;
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_558_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_538_, v___x_561_, v___x_562_, v___x_557_, v___y_539_);
v___y_547_ = v___x_563_;
goto v___jp_546_;
}
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_558_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_538_, v___x_564_, v___x_565_, v___x_557_, v___y_539_);
v___y_547_ = v___x_566_;
goto v___jp_546_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_536_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_a_542_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_546_:
{
if (lean_obj_tag(v___y_547_) == 0)
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___y_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___y_547_, 1);
v_a_542_ = v_a_548_;
goto v___jp_541_;
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___y_547_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_547_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___y_547_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___y_547_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_as_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_567_, v___x_568_, v_as_569_, v___y_570_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_569_);
lean_dec(v___x_568_);
lean_dec(v___x_567_);
return v_res_572_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___f_610_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___f_610_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_610_, 0, v___x_609_);
lean_closure_set(v___f_610_, 1, v___x_608_);
return v___f_610_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___f_613_; 
v___x_611_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_612_ = lean_unsigned_to_nat(0u);
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_613_, 0, v___x_612_);
lean_closure_set(v___f_613_, 1, v___x_611_);
return v___f_613_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_box(2);
v___f_616_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_617_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_618_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_619_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___f_620_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_621_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_622_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___f_620_);
lean_ctor_set(v___x_622_, 2, v___f_619_);
lean_ctor_set(v___x_622_, 3, v___f_618_);
lean_ctor_set(v___x_622_, 4, v___f_617_);
lean_ctor_set(v___x_622_, 5, v___f_616_);
lean_ctor_set(v___x_622_, 6, v___x_615_);
lean_ctor_set(v___x_622_, 7, v___x_614_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_623_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_624_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___f_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_628_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_();
return v_res_630_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Array_instInhabited___redArg();
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__0, &l_Lean_Fmt_getFmtProviders___closed__0_once, _init_l_Lean_Fmt_getFmtProviders___closed__0);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object* v_env_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_toEnvExtension_636_; lean_object* v_asyncMode_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_snd_641_; 
v___x_635_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_636_ = lean_ctor_get(v___x_635_, 0);
v_asyncMode_637_ = lean_ctor_get(v_toEnvExtension_636_, 2);
v___x_638_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_639_ = lean_box(0);
v___x_640_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_638_, v___x_635_, v_env_634_, v_asyncMode_637_, v___x_639_);
v_snd_641_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_snd_641_);
lean_dec(v___x_640_);
return v_snd_641_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_642_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; lean_object* v_nextMacroScope_651_; lean_object* v_ngen_652_; lean_object* v_auxDeclNGen_653_; lean_object* v_traceState_654_; lean_object* v_messages_655_; lean_object* v_infoState_656_; lean_object* v_snapshotTasks_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_668_; 
v___x_650_ = lean_st_ref_take(v___y_648_);
v_nextMacroScope_651_ = lean_ctor_get(v___x_650_, 1);
v_ngen_652_ = lean_ctor_get(v___x_650_, 2);
v_auxDeclNGen_653_ = lean_ctor_get(v___x_650_, 3);
v_traceState_654_ = lean_ctor_get(v___x_650_, 4);
v_messages_655_ = lean_ctor_get(v___x_650_, 6);
v_infoState_656_ = lean_ctor_get(v___x_650_, 7);
v_snapshotTasks_657_ = lean_ctor_get(v___x_650_, 8);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_669_ = lean_ctor_get(v___x_650_, 5);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_670_);
v___x_659_ = v___x_650_;
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snapshotTasks_657_);
lean_inc(v_infoState_656_);
lean_inc(v_messages_655_);
lean_inc(v_traceState_654_);
lean_inc(v_auxDeclNGen_653_);
lean_inc(v_ngen_652_);
lean_inc(v_nextMacroScope_651_);
lean_dec(v___x_650_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_661_ = lean_box(0);
v___x_662_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 5, v___x_662_);
lean_ctor_set(v___x_659_, 0, v_env_647_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_env_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_nextMacroScope_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_ngen_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_auxDeclNGen_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_traceState_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 5, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 6, v_messages_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 7, v_infoState_656_);
lean_ctor_set(v_reuseFailAlloc_667_, 8, v_snapshotTasks_657_);
v___x_664_ = v_reuseFailAlloc_667_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_st_ref_put(v___y_648_, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_661_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_671_, v___y_672_);
lean_dec(v___y_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(lean_object* v_env_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_675_, v___y_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(v_env_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_684_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_ctor_set(v___x_689_, 2, v___x_688_);
lean_ctor_set(v___x_689_, 3, v___x_688_);
lean_ctor_set(v___x_689_, 4, v___x_687_);
lean_ctor_set(v___x_689_, 5, v___x_687_);
lean_ctor_set(v___x_689_, 6, v___x_687_);
lean_ctor_set(v___x_689_, 7, v___x_687_);
lean_ctor_set(v___x_689_, 8, v___x_687_);
lean_ctor_set(v___x_689_, 9, v___x_687_);
lean_ctor_set(v___x_689_, 10, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(32u);
v___x_691_ = lean_mk_empty_array_with_capacity(v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_unsigned_to_nat(32u);
v___x_696_ = lean_mk_empty_array_with_capacity(v___x_695_);
v___x_697_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_698_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
lean_ctor_set(v___x_698_, 2, v___x_694_);
lean_ctor_set(v___x_698_, 3, v___x_694_);
lean_ctor_set_usize(v___x_698_, 4, v___x_693_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_box(1);
v___x_700_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_701_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_699_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v_toCold_708_; lean_object* v_env_709_; lean_object* v_options_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_707_ = lean_st_ref_get(v___y_705_);
v_toCold_708_ = lean_ctor_get(v___y_704_, 0);
v_env_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_707_);
v_options_710_ = lean_ctor_get(v_toCold_708_, 2);
v___x_711_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_710_);
v___x_713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_713_, 0, v_env_709_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
lean_ctor_set(v___x_713_, 3, v_options_710_);
v___x_714_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_msgData_703_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msgData_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_ref_725_; lean_object* v___x_726_; lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_735_; 
v_ref_725_ = lean_ctor_get(v___y_722_, 2);
v___x_726_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_721_, v___y_722_, v___y_723_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_735_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
lean_inc(v_ref_725_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_ref_725_);
lean_ctor_set(v___x_731_, 1, v_a_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_741_, lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_toCold_746_; lean_object* v_currRecDepth_747_; lean_object* v_ref_748_; uint8_t v_diag_749_; uint8_t v_suppressElabErrors_750_; lean_object* v_ref_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_toCold_746_ = lean_ctor_get(v___y_743_, 0);
v_currRecDepth_747_ = lean_ctor_get(v___y_743_, 1);
v_ref_748_ = lean_ctor_get(v___y_743_, 2);
v_diag_749_ = lean_ctor_get_uint8(v___y_743_, sizeof(void*)*3);
v_suppressElabErrors_750_ = lean_ctor_get_uint8(v___y_743_, sizeof(void*)*3 + 1);
v_ref_751_ = l_Lean_replaceRef(v_ref_741_, v_ref_748_);
lean_inc(v_currRecDepth_747_);
lean_inc_ref(v_toCold_746_);
v___x_752_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_752_, 0, v_toCold_746_);
lean_ctor_set(v___x_752_, 1, v_currRecDepth_747_);
lean_ctor_set(v___x_752_, 2, v_ref_751_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*3, v_diag_749_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*3 + 1, v_suppressElabErrors_750_);
v___x_753_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_742_, v___x_752_, v___y_744_);
lean_dec_ref_known(v___x_752_, 3);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_754_, lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_754_, v_msg_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v_ref_754_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_781_, lean_object* v_declHint_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_env_787_; uint8_t v___x_788_; 
v___x_785_ = lean_box(0);
v___x_786_ = lean_st_ref_get(v___y_783_);
v_env_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_env_787_);
lean_dec(v___x_786_);
v___x_788_ = l_Lean_Name_isAnonymous(v_declHint_782_);
if (v___x_788_ == 0)
{
uint8_t v_isExporting_789_; 
v_isExporting_789_ = lean_ctor_get_uint8(v_env_787_, sizeof(void*)*8);
if (v_isExporting_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec_ref(v_env_787_);
lean_dec(v_declHint_782_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_msg_781_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
lean_inc_ref(v_env_787_);
v___x_791_ = l_Lean_Environment_setExporting(v_env_787_, v___x_788_);
lean_inc(v_declHint_782_);
lean_inc_ref(v___x_791_);
v___x_792_ = l_Lean_Environment_contains(v___x_791_, v_declHint_782_, v_isExporting_789_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec_ref(v___x_791_);
lean_dec_ref(v_env_787_);
lean_dec(v_declHint_782_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_msg_781_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_c_799_; lean_object* v___x_800_; 
v___x_794_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_795_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_796_ = l_Lean_Options_empty;
v___x_797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_797_, 0, v___x_791_);
lean_ctor_set(v___x_797_, 1, v___x_794_);
lean_ctor_set(v___x_797_, 2, v___x_795_);
lean_ctor_set(v___x_797_, 3, v___x_796_);
lean_inc(v_declHint_782_);
v___x_798_ = l_Lean_MessageData_ofConstName(v_declHint_782_, v___x_788_);
v_c_799_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_799_, 0, v___x_797_);
lean_ctor_set(v_c_799_, 1, v___x_798_);
v___x_800_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_787_, v_declHint_782_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref(v_env_787_);
lean_dec(v_declHint_782_);
v___x_801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_c_799_);
v___x_803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_MessageData_note(v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v_msg_781_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
else
{
lean_object* v_val_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_842_; 
v_val_808_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_842_ == 0)
{
v___x_810_ = v___x_800_;
v_isShared_811_ = v_isSharedCheck_842_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_val_808_);
lean_dec(v___x_800_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_842_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_mod_814_; uint8_t v___x_815_; 
v___x_812_ = l_Lean_Environment_header(v_env_787_);
lean_dec_ref(v_env_787_);
v___x_813_ = l_Lean_EnvironmentHeader_moduleNames(v___x_812_);
v_mod_814_ = lean_array_get(v___x_785_, v___x_813_, v_val_808_);
lean_dec(v_val_808_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_isPrivateName(v_declHint_782_);
lean_dec(v_declHint_782_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_c_799_);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_MessageData_ofName(v_mod_814_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_MessageData_note(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v_msg_781_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 0);
lean_ctor_set(v___x_810_, 0, v___x_825_);
v___x_827_ = v___x_810_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_c_799_);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_MessageData_ofName(v_mod_814_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_MessageData_note(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v_msg_781_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 0);
lean_ctor_set(v___x_810_, 0, v___x_838_);
v___x_840_ = v___x_810_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v_env_787_);
lean_dec(v_declHint_782_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_msg_781_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_844_, lean_object* v_declHint_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_844_, v_declHint_845_, v___y_846_);
lean_dec(v___y_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_849_, lean_object* v_declHint_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v___x_854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_849_, v_declHint_850_, v___y_852_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_859_ = l_Lean_unknownIdentifierMessageTag;
v___x_860_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_865_, v_declHint_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_871_, lean_object* v_msg_872_, lean_object* v_declHint_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_879_; 
v___x_877_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_872_, v_declHint_873_, v___y_874_, v___y_875_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_871_, v_a_878_, v___y_874_, v___y_875_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_880_, lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_880_, v_msg_881_, v_declHint_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v_ref_880_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_893_, lean_object* v_constName_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_898_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_899_ = 0;
lean_inc(v_constName_894_);
v___x_900_ = l_Lean_MessageData_ofConstName(v_constName_894_, v___x_899_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_898_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_893_, v___x_903_, v_constName_894_, v___y_895_, v___y_896_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_905_, lean_object* v_constName_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_905_, v_constName_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v_ref_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_ref_915_; lean_object* v___x_916_; 
v_ref_915_ = lean_ctor_get(v___y_912_, 2);
v___x_916_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_915_, v_constName_911_, v___y_912_, v___y_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_env_927_; uint8_t v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_st_ref_get(v___y_924_);
v_env_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc_ref(v_env_927_);
lean_dec(v___x_926_);
v___x_928_ = 0;
lean_inc(v_constName_922_);
v___x_929_ = l_Lean_Environment_find_x3f(v_env_927_, v_constName_922_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_922_, v___y_923_, v___y_924_);
return v___x_930_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_constName_922_);
v_val_931_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_val_931_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 0);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_val_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_constName_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_953_, uint8_t v_kind_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___y_964_; 
v___x_958_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_959_ = l_Lean_MessageData_ofName(v_name_953_);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
switch(v_kind_954_)
{
case 0:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___y_964_ = v___x_971_;
goto v___jp_963_;
}
case 1:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5));
v___y_964_ = v___x_972_;
goto v___jp_963_;
}
default: 
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_inc_ref(v___y_964_);
v___x_965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_965_, 0, v___y_964_);
v___x_966_ = l_Lean_MessageData_ofFormat(v___x_965_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_962_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_969_, v___y_955_, v___y_956_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_974_, lean_object* v_kind_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v_kind_boxed_979_; lean_object* v_res_980_; 
v_kind_boxed_979_ = lean_unbox(v_kind_975_);
v_res_980_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_974_, v_kind_boxed_979_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_996_, lean_object* v_declName_997_, lean_object* v_givenType_998_, lean_object* v_expectedType_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1003_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_1004_ = l_Lean_MessageData_ofName(v_attrName_996_);
lean_inc_ref(v___x_1004_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_MessageData_ofConstName(v_declName_997_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_indentExpr(v_givenType_998_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1004_);
v___x_1018_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_indentExpr(v_expectedType_999_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1021_, v___y_1000_, v___y_1001_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_1023_, lean_object* v_declName_1024_, lean_object* v_givenType_1025_, lean_object* v_expectedType_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1023_, v_declName_1024_, v_givenType_1025_, v_expectedType_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_decl_1035_, lean_object* v_stx_1036_, uint8_t v_kind_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1036_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___x_1095_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
lean_inc(v_decl_1035_);
lean_inc(v___x_1034_);
v___x_1095_ = l_Lean_ensureAttrDeclIsMeta(v___x_1034_, v_decl_1035_, v_kind_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1095_) == 0)
{
uint8_t v___x_1096_; uint8_t v___x_1097_; 
lean_dec_ref_known(v___x_1095_, 1);
v___x_1096_ = 0;
v___x_1097_ = l_Lean_instBEqAttributeKind_beq(v_kind_1037_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_a_1042_);
lean_dec(v_decl_1035_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
v___x_1098_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_1034_, v_kind_1037_, v___y_1038_, v___y_1039_);
return v___x_1098_;
}
else
{
v___y_1076_ = v___y_1038_;
v___y_1077_ = v___y_1039_;
goto v___jp_1075_;
}
}
else
{
lean_dec(v_a_1042_);
lean_dec(v_decl_1035_);
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
return v___x_1095_;
}
v___jp_1043_:
{
lean_object* v___x_1046_; lean_object* v_toCold_1047_; lean_object* v_env_1048_; lean_object* v_ref_1049_; lean_object* v_options_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1046_ = lean_st_ref_get(v___y_1045_);
v_toCold_1047_ = lean_ctor_get(v___y_1044_, 0);
v_env_1048_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_env_1048_);
lean_dec(v___x_1046_);
v_ref_1049_ = lean_ctor_get(v___y_1044_, 2);
v_options_1050_ = lean_ctor_get(v_toCold_1047_, 2);
lean_inc_ref(v_options_1050_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_env_1048_);
lean_ctor_set(v___x_1051_, 1, v_options_1050_);
lean_inc(v_decl_1035_);
v___x_1052_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_decl_1035_, v___x_1051_);
lean_dec_ref_known(v___x_1051_, 2);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_env_1056_; lean_object* v___x_1057_; lean_object* v_toEnvExtension_1058_; lean_object* v_asyncMode_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_a_1042_);
lean_ctor_set(v___x_1054_, 1, v_a_1053_);
v___x_1055_ = lean_st_ref_get(v___y_1045_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_1058_ = lean_ctor_get(v___x_1057_, 0);
v_asyncMode_1059_ = lean_ctor_get(v_toEnvExtension_1058_, 2);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_decl_1035_);
lean_ctor_set(v___x_1060_, 1, v___x_1054_);
v___x_1061_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1057_, v_env_1056_, v___x_1060_, v_asyncMode_1059_, v___x_1031_);
v___x_1062_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1061_, v___y_1045_);
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1042_);
lean_dec(v_decl_1035_);
lean_dec(v___x_1031_);
v_a_1063_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v___x_1052_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1052_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1067_ = lean_io_error_to_string(v_a_1063_);
v___x_1068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
lean_inc(v_ref_1049_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_ref_1049_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
v___jp_1075_:
{
lean_object* v___x_1078_; 
lean_inc(v_decl_1035_);
v___x_1078_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_1035_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = l_Lean_ConstantInfo_type(v_a_1079_);
lean_dec(v_a_1079_);
v___x_1081_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2));
v___x_1082_ = l_Lean_Name_mkStr3(v___x_1032_, v___x_1033_, v___x_1081_);
v___x_1083_ = l_Lean_Expr_isConstOf(v___x_1080_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec(v_a_1042_);
lean_dec(v___x_1031_);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_mkConst(v___x_1082_, v___x_1084_);
v___x_1086_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_1034_, v_decl_1035_, v___x_1080_, v___x_1085_, v___y_1076_, v___y_1077_);
return v___x_1086_;
}
else
{
lean_dec(v___x_1082_);
lean_dec_ref(v___x_1080_);
lean_dec(v___x_1034_);
v___y_1044_ = v___y_1076_;
v___y_1045_ = v___y_1077_;
goto v___jp_1043_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1042_);
lean_dec(v_decl_1035_);
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
v_a_1087_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1078_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1078_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_decl_1035_);
lean_dec(v___x_1034_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
v_a_1099_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1041_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1041_);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v_decl_1111_, lean_object* v_stx_1112_, lean_object* v_kind_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v_kind_boxed_1117_; lean_object* v_res_1118_; 
v_kind_boxed_1117_ = lean_unbox(v_kind_1113_);
v_res_1118_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1107_, v___x_1108_, v___x_1109_, v___x_1110_, v_decl_1111_, v_stx_1112_, v_kind_boxed_1117_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1118_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1125_, lean_object* v_decl_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1131_ = l_Lean_MessageData_ofName(v___x_1125_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1134_, v___y_1127_, v___y_1128_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1136_, lean_object* v_decl_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1136_, v_decl_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v_decl_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1198_ = l_Lean_registerBuiltinAttribute(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1201_, lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_1202_, v___y_1203_, v___y_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1207_, lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(v_00_u03b1_1207_, v_msg_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1213_, lean_object* v_attrName_1214_, lean_object* v_declName_1215_, lean_object* v_givenType_1216_, lean_object* v_expectedType_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1214_, v_declName_1215_, v_givenType_1216_, v_expectedType_1217_, v___y_1218_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_attrName_1223_, lean_object* v_declName_1224_, lean_object* v_givenType_1225_, lean_object* v_expectedType_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(v_00_u03b1_1222_, v_attrName_1223_, v_declName_1224_, v_givenType_1225_, v_expectedType_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1231_, lean_object* v_name_1232_, uint8_t v_kind_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_1232_, v_kind_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_name_1239_, lean_object* v_kind_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_kind_boxed_1244_; lean_object* v_res_1245_; 
v_kind_boxed_1244_ = lean_unbox(v_kind_1240_);
v_res_1245_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(v_00_u03b1_1238_, v_name_1239_, v_kind_boxed_1244_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1246_, lean_object* v_constName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1252_, v_constName_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1258_, lean_object* v_ref_1259_, lean_object* v_constName_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1259_, v_constName_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_ref_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1265_, v_ref_1266_, v_constName_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v_ref_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_msg_1274_, lean_object* v_declHint_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1273_, v_msg_1274_, v_declHint_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_ref_1281_, lean_object* v_msg_1282_, lean_object* v_declHint_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1280_, v_ref_1281_, v_msg_1282_, v_declHint_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v_ref_1281_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1288_, lean_object* v_declHint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1288_, v_declHint_1289_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1300_, lean_object* v_ref_1301_, lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1301_, v_msg_1302_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_ref_1308_, lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1307_, v_ref_1308_, v_msg_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_ref_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx(uint8_t v_x_1314_){
_start:
{
if (v_x_1314_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___boxed(lean_object* v_x_1317_){
_start:
{
uint8_t v_x_boxed_1318_; lean_object* v_res_1319_; 
v_x_boxed_1318_ = lean_unbox(v_x_1317_);
v_res_1319_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx(v_x_boxed_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object* v_k_1320_){
_start:
{
lean_inc(v_k_1320_);
return v_k_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object* v_k_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(v_k_1321_);
lean_dec(v_k_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object* v_motive_1323_, lean_object* v_ctorIdx_1324_, uint8_t v_t_1325_, lean_object* v_h_1326_, lean_object* v_k_1327_){
_start:
{
lean_inc(v_k_1327_);
return v_k_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object* v_motive_1328_, lean_object* v_ctorIdx_1329_, lean_object* v_t_1330_, lean_object* v_h_1331_, lean_object* v_k_1332_){
_start:
{
uint8_t v_t_boxed_1333_; lean_object* v_res_1334_; 
v_t_boxed_1333_ = lean_unbox(v_t_1330_);
v_res_1334_ = l_Lean_Fmt_Comment_Whitespace_ctorElim(v_motive_1328_, v_ctorIdx_1329_, v_t_boxed_1333_, v_h_1331_, v_k_1332_);
lean_dec(v_k_1332_);
lean_dec(v_ctorIdx_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object* v_leading_1335_){
_start:
{
lean_inc(v_leading_1335_);
return v_leading_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object* v_leading_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(v_leading_1336_);
lean_dec(v_leading_1336_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object* v_motive_1338_, uint8_t v_t_1339_, lean_object* v_h_1340_, lean_object* v_leading_1341_){
_start:
{
lean_inc(v_leading_1341_);
return v_leading_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object* v_motive_1342_, lean_object* v_t_1343_, lean_object* v_h_1344_, lean_object* v_leading_1345_){
_start:
{
uint8_t v_t_boxed_1346_; lean_object* v_res_1347_; 
v_t_boxed_1346_ = lean_unbox(v_t_1343_);
v_res_1347_ = l_Lean_Fmt_Comment_Whitespace_leading_elim(v_motive_1342_, v_t_boxed_1346_, v_h_1344_, v_leading_1345_);
lean_dec(v_leading_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object* v_trailing_1348_){
_start:
{
lean_inc(v_trailing_1348_);
return v_trailing_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object* v_trailing_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(v_trailing_1349_);
lean_dec(v_trailing_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object* v_motive_1351_, uint8_t v_t_1352_, lean_object* v_h_1353_, lean_object* v_trailing_1354_){
_start:
{
lean_inc(v_trailing_1354_);
return v_trailing_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object* v_motive_1355_, lean_object* v_t_1356_, lean_object* v_h_1357_, lean_object* v_trailing_1358_){
_start:
{
uint8_t v_t_boxed_1359_; lean_object* v_res_1360_; 
v_t_boxed_1359_ = lean_unbox(v_t_1356_);
v_res_1360_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim(v_motive_1355_, v_t_boxed_1359_, v_h_1357_, v_trailing_1358_);
lean_dec(v_trailing_1358_);
return v_res_1360_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default(void){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = 0;
return v___x_1361_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace(void){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = 0;
return v___x_1362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqWhitespace_beq(uint8_t v_x_1363_, uint8_t v_y_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx(v_x_1363_);
v___x_1366_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx(v_y_1364_);
v___x_1367_ = lean_nat_dec_eq(v___x_1365_, v___x_1366_);
lean_dec(v___x_1366_);
lean_dec(v___x_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed(lean_object* v_x_1368_, lean_object* v_y_1369_){
_start:
{
uint8_t v_x_21__boxed_1370_; uint8_t v_y_22__boxed_1371_; uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_x_21__boxed_1370_ = lean_unbox(v_x_1368_);
v_y_22__boxed_1371_ = lean_unbox(v_y_1369_);
v_res_1372_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_x_21__boxed_1370_, v_y_22__boxed_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(2u);
v___x_1383_ = lean_nat_to_int(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_to_int(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t v_x_1386_, lean_object* v_prec_1387_){
_start:
{
lean_object* v___y_1389_; lean_object* v___y_1396_; 
if (v_x_1386_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = lean_unsigned_to_nat(1024u);
v___x_1403_ = lean_nat_dec_le(v___x_1402_, v_prec_1387_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1389_ = v___x_1404_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1389_ = v___x_1405_;
goto v___jp_1388_;
}
}
else
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = lean_unsigned_to_nat(1024u);
v___x_1407_ = lean_nat_dec_le(v___x_1406_, v_prec_1387_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1396_ = v___x_1408_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1396_ = v___x_1409_;
goto v___jp_1395_;
}
}
v___jp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1390_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1));
lean_inc(v___y_1389_);
v___x_1391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = 0;
v___x_1393_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*1, v___x_1392_);
v___x_1394_ = l_Repr_addAppParen(v___x_1393_, v_prec_1387_);
return v___x_1394_;
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1397_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3));
lean_inc(v___y_1396_);
v___x_1398_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___y_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = 0;
v___x_1400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*1, v___x_1399_);
v___x_1401_ = l_Repr_addAppParen(v___x_1400_, v_prec_1387_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object* v_x_1410_, lean_object* v_prec_1411_){
_start:
{
uint8_t v_x_117__boxed_1412_; lean_object* v_res_1413_; 
v_x_117__boxed_1412_ = lean_unbox(v_x_1410_);
v_res_1413_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_x_117__boxed_1412_, v_prec_1411_);
lean_dec(v_prec_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx(uint8_t v_x_1416_){
_start:
{
if (v_x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_unsigned_to_nat(1u);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___boxed(lean_object* v_x_1419_){
_start:
{
uint8_t v_x_boxed_1420_; lean_object* v_res_1421_; 
v_x_boxed_1420_ = lean_unbox(v_x_1419_);
v_res_1421_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_x_boxed_1420_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object* v_k_1422_){
_start:
{
lean_inc(v_k_1422_);
return v_k_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object* v_k_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Fmt_Comment_Placement_ctorElim___redArg(v_k_1423_);
lean_dec(v_k_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object* v_motive_1425_, lean_object* v_ctorIdx_1426_, uint8_t v_t_1427_, lean_object* v_h_1428_, lean_object* v_k_1429_){
_start:
{
lean_inc(v_k_1429_);
return v_k_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object* v_motive_1430_, lean_object* v_ctorIdx_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_k_1434_){
_start:
{
uint8_t v_t_boxed_1435_; lean_object* v_res_1436_; 
v_t_boxed_1435_ = lean_unbox(v_t_1432_);
v_res_1436_ = l_Lean_Fmt_Comment_Placement_ctorElim(v_motive_1430_, v_ctorIdx_1431_, v_t_boxed_1435_, v_h_1433_, v_k_1434_);
lean_dec(v_k_1434_);
lean_dec(v_ctorIdx_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object* v_afterToken_1437_){
_start:
{
lean_inc(v_afterToken_1437_);
return v_afterToken_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object* v_afterToken_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(v_afterToken_1438_);
lean_dec(v_afterToken_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object* v_motive_1440_, uint8_t v_t_1441_, lean_object* v_h_1442_, lean_object* v_afterToken_1443_){
_start:
{
lean_inc(v_afterToken_1443_);
return v_afterToken_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object* v_motive_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_afterToken_1447_){
_start:
{
uint8_t v_t_boxed_1448_; lean_object* v_res_1449_; 
v_t_boxed_1448_ = lean_unbox(v_t_1445_);
v_res_1449_ = l_Lean_Fmt_Comment_Placement_afterToken_elim(v_motive_1444_, v_t_boxed_1448_, v_h_1446_, v_afterToken_1447_);
lean_dec(v_afterToken_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object* v_onLineBeforeToken_1450_){
_start:
{
lean_inc(v_onLineBeforeToken_1450_);
return v_onLineBeforeToken_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object* v_onLineBeforeToken_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(v_onLineBeforeToken_1451_);
lean_dec(v_onLineBeforeToken_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object* v_motive_1453_, uint8_t v_t_1454_, lean_object* v_h_1455_, lean_object* v_onLineBeforeToken_1456_){
_start:
{
lean_inc(v_onLineBeforeToken_1456_);
return v_onLineBeforeToken_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object* v_motive_1457_, lean_object* v_t_1458_, lean_object* v_h_1459_, lean_object* v_onLineBeforeToken_1460_){
_start:
{
uint8_t v_t_boxed_1461_; lean_object* v_res_1462_; 
v_t_boxed_1461_ = lean_unbox(v_t_1458_);
v_res_1462_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(v_motive_1457_, v_t_boxed_1461_, v_h_1459_, v_onLineBeforeToken_1460_);
lean_dec(v_onLineBeforeToken_1460_);
return v_res_1462_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default(void){
_start:
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement(void){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = 0;
return v___x_1464_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t v_x_1465_, uint8_t v_y_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_x_1465_);
v___x_1468_ = l_Lean_Fmt_Comment_Placement_ctorIdx(v_y_1466_);
v___x_1469_ = lean_nat_dec_eq(v___x_1467_, v___x_1468_);
lean_dec(v___x_1468_);
lean_dec(v___x_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object* v_x_1470_, lean_object* v_y_1471_){
_start:
{
uint8_t v_x_21__boxed_1472_; uint8_t v_y_22__boxed_1473_; uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_x_21__boxed_1472_ = lean_unbox(v_x_1470_);
v_y_22__boxed_1473_ = lean_unbox(v_y_1471_);
v_res_1474_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_x_21__boxed_1472_, v_y_22__boxed_1473_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t v_x_1484_, lean_object* v_prec_1485_){
_start:
{
lean_object* v___y_1487_; lean_object* v___y_1494_; 
if (v_x_1484_ == 0)
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_unsigned_to_nat(1024u);
v___x_1501_ = lean_nat_dec_le(v___x_1500_, v_prec_1485_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1487_ = v___x_1502_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1487_ = v___x_1503_;
goto v___jp_1486_;
}
}
else
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1024u);
v___x_1505_ = lean_nat_dec_le(v___x_1504_, v_prec_1485_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1494_ = v___x_1506_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1494_ = v___x_1507_;
goto v___jp_1493_;
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1488_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1));
lean_inc(v___y_1487_);
v___x_1489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = 0;
v___x_1491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*1, v___x_1490_);
v___x_1492_ = l_Repr_addAppParen(v___x_1491_, v_prec_1485_);
return v___x_1492_;
}
v___jp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3));
lean_inc(v___y_1494_);
v___x_1496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = 0;
v___x_1498_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*1, v___x_1497_);
v___x_1499_ = l_Repr_addAppParen(v___x_1498_, v_prec_1485_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object* v_x_1508_, lean_object* v_prec_1509_){
_start:
{
uint8_t v_x_113__boxed_1510_; lean_object* v_res_1511_; 
v_x_113__boxed_1510_ = lean_unbox(v_x_1508_);
v_res_1511_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_x_113__boxed_1510_, v_prec_1509_);
lean_dec(v_prec_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx(uint8_t v_x_1514_){
_start:
{
if (v_x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___boxed(lean_object* v_x_1517_){
_start:
{
uint8_t v_x_boxed_1518_; lean_object* v_res_1519_; 
v_x_boxed_1518_ = lean_unbox(v_x_1517_);
v_res_1519_ = l_Lean_Fmt_Comment_Kind_ctorIdx(v_x_boxed_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object* v_k_1520_){
_start:
{
lean_inc(v_k_1520_);
return v_k_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object* v_k_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Fmt_Comment_Kind_ctorElim___redArg(v_k_1521_);
lean_dec(v_k_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object* v_motive_1523_, lean_object* v_ctorIdx_1524_, uint8_t v_t_1525_, lean_object* v_h_1526_, lean_object* v_k_1527_){
_start:
{
lean_inc(v_k_1527_);
return v_k_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object* v_motive_1528_, lean_object* v_ctorIdx_1529_, lean_object* v_t_1530_, lean_object* v_h_1531_, lean_object* v_k_1532_){
_start:
{
uint8_t v_t_boxed_1533_; lean_object* v_res_1534_; 
v_t_boxed_1533_ = lean_unbox(v_t_1530_);
v_res_1534_ = l_Lean_Fmt_Comment_Kind_ctorElim(v_motive_1528_, v_ctorIdx_1529_, v_t_boxed_1533_, v_h_1531_, v_k_1532_);
lean_dec(v_k_1532_);
lean_dec(v_ctorIdx_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object* v_lineComment_1535_){
_start:
{
lean_inc(v_lineComment_1535_);
return v_lineComment_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object* v_lineComment_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(v_lineComment_1536_);
lean_dec(v_lineComment_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object* v_motive_1538_, uint8_t v_t_1539_, lean_object* v_h_1540_, lean_object* v_lineComment_1541_){
_start:
{
lean_inc(v_lineComment_1541_);
return v_lineComment_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object* v_motive_1542_, lean_object* v_t_1543_, lean_object* v_h_1544_, lean_object* v_lineComment_1545_){
_start:
{
uint8_t v_t_boxed_1546_; lean_object* v_res_1547_; 
v_t_boxed_1546_ = lean_unbox(v_t_1543_);
v_res_1547_ = l_Lean_Fmt_Comment_Kind_lineComment_elim(v_motive_1542_, v_t_boxed_1546_, v_h_1544_, v_lineComment_1545_);
lean_dec(v_lineComment_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object* v_blockComment_1548_){
_start:
{
lean_inc(v_blockComment_1548_);
return v_blockComment_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object* v_blockComment_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(v_blockComment_1549_);
lean_dec(v_blockComment_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object* v_motive_1551_, uint8_t v_t_1552_, lean_object* v_h_1553_, lean_object* v_blockComment_1554_){
_start:
{
lean_inc(v_blockComment_1554_);
return v_blockComment_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object* v_motive_1555_, lean_object* v_t_1556_, lean_object* v_h_1557_, lean_object* v_blockComment_1558_){
_start:
{
uint8_t v_t_boxed_1559_; lean_object* v_res_1560_; 
v_t_boxed_1559_ = lean_unbox(v_t_1556_);
v_res_1560_ = l_Lean_Fmt_Comment_Kind_blockComment_elim(v_motive_1555_, v_t_boxed_1559_, v_h_1557_, v_blockComment_1558_);
lean_dec(v_blockComment_1558_);
return v_res_1560_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = 0;
return v___x_1561_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind(void){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = 0;
return v___x_1562_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqKind_beq(uint8_t v_x_1563_, uint8_t v_y_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = l_Lean_Fmt_Comment_Kind_ctorIdx(v_x_1563_);
v___x_1566_ = l_Lean_Fmt_Comment_Kind_ctorIdx(v_y_1564_);
v___x_1567_ = lean_nat_dec_eq(v___x_1565_, v___x_1566_);
lean_dec(v___x_1566_);
lean_dec(v___x_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqKind_beq___boxed(lean_object* v_x_1568_, lean_object* v_y_1569_){
_start:
{
uint8_t v_x_21__boxed_1570_; uint8_t v_y_22__boxed_1571_; uint8_t v_res_1572_; lean_object* v_r_1573_; 
v_x_21__boxed_1570_ = lean_unbox(v_x_1568_);
v_y_22__boxed_1571_ = lean_unbox(v_y_1569_);
v_res_1572_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_x_21__boxed_1570_, v_y_22__boxed_1571_);
v_r_1573_ = lean_box(v_res_1572_);
return v_r_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t v_x_1582_, lean_object* v_prec_1583_){
_start:
{
lean_object* v___y_1585_; lean_object* v___y_1592_; 
if (v_x_1582_ == 0)
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_unsigned_to_nat(1024u);
v___x_1599_ = lean_nat_dec_le(v___x_1598_, v_prec_1583_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1585_ = v___x_1600_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1585_ = v___x_1601_;
goto v___jp_1584_;
}
}
else
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = lean_unsigned_to_nat(1024u);
v___x_1603_ = lean_nat_dec_le(v___x_1602_, v_prec_1583_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1592_ = v___x_1604_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1592_ = v___x_1605_;
goto v___jp_1591_;
}
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1586_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__1));
lean_inc(v___y_1585_);
v___x_1587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___y_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = 0;
v___x_1589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*1, v___x_1588_);
v___x_1590_ = l_Repr_addAppParen(v___x_1589_, v_prec_1583_);
return v___x_1590_;
}
v___jp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1593_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__3));
lean_inc(v___y_1592_);
v___x_1594_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___y_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = 0;
v___x_1596_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*1, v___x_1595_);
v___x_1597_ = l_Repr_addAppParen(v___x_1596_, v_prec_1583_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object* v_x_1606_, lean_object* v_prec_1607_){
_start:
{
uint8_t v_x_113__boxed_1608_; lean_object* v_res_1609_; 
v_x_113__boxed_1608_ = lean_unbox(v_x_1606_);
v_res_1609_ = l_Lean_Fmt_Comment_instReprKind_repr(v_x_113__boxed_1608_, v_prec_1607_);
lean_dec(v_prec_1607_);
return v_res_1609_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default___closed__1(void){
_start:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l_Lean_Fmt_instInhabitedComment_default___closed__0));
v___x_1615_ = 0;
v___x_1616_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_1617_ = 0;
v___x_1618_ = 0;
v___x_1619_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1616_);
lean_ctor_set(v___x_1619_, 2, v___x_1614_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*3, v___x_1618_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*3 + 1, v___x_1617_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*3 + 2, v___x_1615_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default(void){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_obj_once(&l_Lean_Fmt_instInhabitedComment_default___closed__1, &l_Lean_Fmt_instInhabitedComment_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedComment_default___closed__1);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment(void){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Fmt_instInhabitedComment_default;
return v___x_1621_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(lean_object* v_xs_1622_, lean_object* v_ys_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v_zero_1625_; uint8_t v_isZero_1626_; 
v_zero_1625_ = lean_unsigned_to_nat(0u);
v_isZero_1626_ = lean_nat_dec_eq(v_x_1624_, v_zero_1625_);
if (v_isZero_1626_ == 1)
{
lean_dec(v_x_1624_);
return v_isZero_1626_;
}
else
{
lean_object* v_one_1627_; lean_object* v_n_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_one_1627_ = lean_unsigned_to_nat(1u);
v_n_1628_ = lean_nat_sub(v_x_1624_, v_one_1627_);
lean_dec(v_x_1624_);
v___x_1629_ = lean_array_fget_borrowed(v_xs_1622_, v_n_1628_);
v___x_1630_ = lean_array_fget_borrowed(v_ys_1623_, v_n_1628_);
v___x_1631_ = lean_string_dec_eq(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_dec(v_n_1628_);
return v___x_1631_;
}
else
{
v_x_1624_ = v_n_1628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg___boxed(lean_object* v_xs_1633_, lean_object* v_ys_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1633_, v_ys_1634_, v_x_1635_);
lean_dec_ref(v_ys_1634_);
lean_dec_ref(v_xs_1633_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqComment_beq(lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_kind_1640_; uint8_t v_placement_1641_; lean_object* v_originalTokenRange_1642_; lean_object* v_originalWhitespaceRange_1643_; uint8_t v_originalWhitespaceKind_1644_; lean_object* v_content_1645_; uint8_t v_kind_1646_; uint8_t v_placement_1647_; lean_object* v_originalTokenRange_1648_; lean_object* v_originalWhitespaceRange_1649_; uint8_t v_originalWhitespaceKind_1650_; lean_object* v_content_1651_; uint8_t v___x_1652_; 
v_kind_1640_ = lean_ctor_get_uint8(v_x_1638_, sizeof(void*)*3);
v_placement_1641_ = lean_ctor_get_uint8(v_x_1638_, sizeof(void*)*3 + 1);
v_originalTokenRange_1642_ = lean_ctor_get(v_x_1638_, 0);
v_originalWhitespaceRange_1643_ = lean_ctor_get(v_x_1638_, 1);
v_originalWhitespaceKind_1644_ = lean_ctor_get_uint8(v_x_1638_, sizeof(void*)*3 + 2);
v_content_1645_ = lean_ctor_get(v_x_1638_, 2);
v_kind_1646_ = lean_ctor_get_uint8(v_x_1639_, sizeof(void*)*3);
v_placement_1647_ = lean_ctor_get_uint8(v_x_1639_, sizeof(void*)*3 + 1);
v_originalTokenRange_1648_ = lean_ctor_get(v_x_1639_, 0);
v_originalWhitespaceRange_1649_ = lean_ctor_get(v_x_1639_, 1);
v_originalWhitespaceKind_1650_ = lean_ctor_get_uint8(v_x_1639_, sizeof(void*)*3 + 2);
v_content_1651_ = lean_ctor_get(v_x_1639_, 2);
v___x_1652_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_kind_1640_, v_kind_1646_);
if (v___x_1652_ == 0)
{
return v___x_1652_;
}
else
{
uint8_t v___x_1653_; 
v___x_1653_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_placement_1641_, v_placement_1647_);
if (v___x_1653_ == 0)
{
return v___x_1653_;
}
else
{
uint8_t v___x_1654_; 
v___x_1654_ = l_Lean_Syntax_instBEqRange_beq(v_originalTokenRange_1642_, v_originalTokenRange_1648_);
if (v___x_1654_ == 0)
{
return v___x_1654_;
}
else
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Lean_Syntax_instBEqRange_beq(v_originalWhitespaceRange_1643_, v_originalWhitespaceRange_1649_);
if (v___x_1655_ == 0)
{
return v___x_1655_;
}
else
{
uint8_t v___x_1656_; 
v___x_1656_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_originalWhitespaceKind_1644_, v_originalWhitespaceKind_1650_);
if (v___x_1656_ == 0)
{
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = lean_array_get_size(v_content_1645_);
v___x_1658_ = lean_array_get_size(v_content_1651_);
v___x_1659_ = lean_nat_dec_eq(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
return v___x_1659_;
}
else
{
uint8_t v___x_1660_; 
v___x_1660_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_content_1645_, v_content_1651_, v___x_1657_);
return v___x_1660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqComment_beq___boxed(lean_object* v_x_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v_res_1663_; lean_object* v_r_1664_; 
v_res_1663_ = l_Lean_Fmt_instBEqComment_beq(v_x_1661_, v_x_1662_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_x_1661_);
v_r_1664_ = lean_box(v_res_1663_);
return v_r_1664_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(lean_object* v_xs_1665_, lean_object* v_ys_1666_, lean_object* v_hsz_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1665_, v_ys_1666_, v_x_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___boxed(lean_object* v_xs_1671_, lean_object* v_ys_1672_, lean_object* v_hsz_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(v_xs_1671_, v_ys_1672_, v_hsz_1673_, v_x_1674_, v_x_1675_);
lean_dec_ref(v_ys_1672_);
lean_dec_ref(v_xs_1671_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
lean_dec(v_x_1680_);
return v_x_1681_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1695_; 
v_head_1683_ = lean_ctor_get(v_x_1682_, 0);
v_tail_1684_ = lean_ctor_get(v_x_1682_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1682_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1686_ = v_x_1682_;
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_tail_1684_);
lean_inc(v_head_1683_);
lean_dec(v_x_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
lean_inc(v_x_1680_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 5);
lean_ctor_set(v___x_1686_, 1, v_x_1680_);
lean_ctor_set(v___x_1686_, 0, v_x_1681_);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_x_1681_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_x_1680_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = l_String_quote(v_head_1683_);
v___x_1691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v_x_1681_ = v___x_1692_;
v_x_1682_ = v_tail_1684_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(lean_object* v_x_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
lean_dec(v_x_1696_);
return v_x_1697_;
}
else
{
lean_object* v_head_1699_; lean_object* v_tail_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1711_; 
v_head_1699_ = lean_ctor_get(v_x_1698_, 0);
v_tail_1700_ = lean_ctor_get(v_x_1698_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1702_ = v_x_1698_;
v_isShared_1703_ = v_isSharedCheck_1711_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_tail_1700_);
lean_inc(v_head_1699_);
lean_dec(v_x_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1711_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
lean_inc(v_x_1696_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 5);
lean_ctor_set(v___x_1702_, 1, v_x_1696_);
lean_ctor_set(v___x_1702_, 0, v_x_1697_);
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_x_1697_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_x_1696_);
v___x_1705_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = l_String_quote(v_head_1699_);
v___x_1707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1705_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(v_x_1696_, v___x_1708_, v_tail_1700_);
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = l_String_quote(v___y_1712_);
v___x_1714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_x_1716_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
lean_object* v_tail_1718_; 
v_tail_1718_ = lean_ctor_get(v_x_1715_, 1);
if (lean_obj_tag(v_tail_1718_) == 0)
{
lean_object* v_head_1719_; lean_object* v___x_1720_; 
lean_dec(v_x_1716_);
v_head_1719_ = lean_ctor_get(v_x_1715_, 0);
lean_inc(v_head_1719_);
lean_dec_ref_known(v_x_1715_, 2);
v___x_1720_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1719_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_inc(v_tail_1718_);
v_head_1721_ = lean_ctor_get(v_x_1715_, 0);
lean_inc(v_head_1721_);
lean_dec_ref_known(v_x_1715_, 2);
v___x_1722_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1721_);
v___x_1723_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(v_x_1716_, v___x_1722_, v_tail_1718_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object* v_xs_1724_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_array_get_size(v_xs_1724_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_nat_dec_eq(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1728_ = lean_array_to_list(v_xs_1724_);
v___x_1729_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_1730_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_1732_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_1733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1730_);
v___x_1734_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1731_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Std_Format_fill(v___x_1736_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; 
lean_dec_ref(v_xs_1724_);
v___x_1738_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_1738_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(8u);
v___x_1749_ = lean_nat_to_int(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(13u);
v___x_1754_ = lean_nat_to_int(v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(22u);
v___x_1759_ = lean_nat_to_int(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_unsigned_to_nat(11u);
v___x_1770_ = lean_nat_to_int(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object* v_x_1771_){
_start:
{
uint8_t v_kind_1772_; uint8_t v_placement_1773_; lean_object* v_originalTokenRange_1774_; lean_object* v_originalWhitespaceRange_1775_; uint8_t v_originalWhitespaceKind_1776_; lean_object* v_content_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_kind_1772_ = lean_ctor_get_uint8(v_x_1771_, sizeof(void*)*3);
v_placement_1773_ = lean_ctor_get_uint8(v_x_1771_, sizeof(void*)*3 + 1);
v_originalTokenRange_1774_ = lean_ctor_get(v_x_1771_, 0);
lean_inc_ref(v_originalTokenRange_1774_);
v_originalWhitespaceRange_1775_ = lean_ctor_get(v_x_1771_, 1);
lean_inc_ref(v_originalWhitespaceRange_1775_);
v_originalWhitespaceKind_1776_ = lean_ctor_get_uint8(v_x_1771_, sizeof(void*)*3 + 2);
v_content_1777_ = lean_ctor_get(v_x_1771_, 2);
lean_inc_ref(v_content_1777_);
lean_dec_ref(v_x_1771_);
v___x_1778_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_1779_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__3));
v___x_1780_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__4, &l_Lean_Fmt_instReprComment_repr___redArg___closed__4_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = l_Lean_Fmt_Comment_instReprKind_repr(v_kind_1772_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = 0;
v___x_1785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set_uint8(v___x_1785_, sizeof(void*)*1, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1779_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_1788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_box(1);
v___x_1790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__6));
v___x_1792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___x_1778_);
v___x_1794_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__7, &l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7);
v___x_1795_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_placement_1773_, v___x_1781_);
v___x_1796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*1, v___x_1784_);
v___x_1798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1793_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1787_);
v___x_1800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1789_);
v___x_1801_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__9));
v___x_1802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1778_);
v___x_1804_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_1805_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalTokenRange_1774_);
v___x_1806_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set_uint8(v___x_1807_, sizeof(void*)*1, v___x_1784_);
v___x_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1787_);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___x_1789_);
v___x_1811_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__12));
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1778_);
v___x_1814_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_1815_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalWhitespaceRange_1775_);
v___x_1816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*1, v___x_1784_);
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1787_);
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1789_);
v___x_1821_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__14));
v___x_1822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1778_);
v___x_1824_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_1825_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_originalWhitespaceKind_1776_, v___x_1781_);
v___x_1826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v___x_1784_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1787_);
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1789_);
v___x_1831_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__16));
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1778_);
v___x_1834_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__17, &l_Lean_Fmt_instReprComment_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17);
v___x_1835_ = l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(v_content_1777_);
v___x_1836_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*1, v___x_1784_);
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1833_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_1840_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1838_);
v___x_1842_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*1, v___x_1784_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object* v_x_1846_, lean_object* v_prec_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Fmt_instReprComment_repr___redArg(v_x_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object* v_x_1849_, lean_object* v_prec_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Fmt_instReprComment_repr(v_x_1849_, v_prec_1850_);
lean_dec(v_prec_1850_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object* v_entry_1854_, lean_object* v_as_1855_, lean_object* v_j_1856_){
_start:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_array_get_size(v_as_1855_);
v___x_1858_ = lean_nat_dec_lt(v_j_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec(v_j_1856_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v_priority_1861_; lean_object* v_priority_1862_; uint8_t v___x_1863_; 
v___x_1860_ = lean_array_fget_borrowed(v_as_1855_, v_j_1856_);
v_priority_1861_ = lean_ctor_get(v___x_1860_, 0);
v_priority_1862_ = lean_ctor_get(v_entry_1854_, 0);
v___x_1863_ = lean_nat_dec_lt(v_priority_1861_, v_priority_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = lean_nat_add(v_j_1856_, v___x_1864_);
lean_dec(v_j_1856_);
v_j_1856_ = v___x_1865_;
goto _start;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_j_1856_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object* v_entry_1868_, lean_object* v_as_1869_, lean_object* v_j_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1868_, v_as_1869_, v_j_1870_);
lean_dec_ref(v_as_1869_);
lean_dec_ref(v_entry_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object* v_collectors_1872_, lean_object* v_entry_1873_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1873_, v_collectors_1872_, v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_array_get_size(v_collectors_1872_);
v___x_1877_ = l_Array_insertIdx_x21___redArg(v_collectors_1872_, v___x_1876_, v_entry_1873_);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1879_; 
v_val_1878_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_val_1878_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1879_ = l_Array_insertIdx_x21___redArg(v_collectors_1872_, v_val_1878_, v_entry_1873_);
lean_dec(v_val_1878_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_));
v___x_1884_ = lean_st_mk_ref(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object* v_priority_1888_, lean_object* v_collector_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1891_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_1892_ = lean_st_ref_take(v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_priority_1888_);
lean_ctor_set(v___x_1893_, 1, v_collector_1889_);
v___x_1894_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v___x_1892_, v___x_1893_);
v___x_1895_ = lean_st_ref_put(v___x_1891_, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object* v_priority_1897_, lean_object* v_collector_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Fmt_addBuiltinCommentCollector(v_priority_1897_, v_collector_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object* v_constName_1906_, lean_object* v_env_1907_, lean_object* v_opts_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
v___x_1910_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1907_, v_opts_1908_, v___x_1909_, v_constName_1906_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object* v_constName_1911_, lean_object* v_env_1912_, lean_object* v_opts_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(v_constName_1911_, v_env_1912_, v_opts_1913_);
lean_dec_ref(v_opts_1913_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object* v_constName_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_env_1918_; lean_object* v_opts_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_env_1918_ = lean_ctor_get(v_a_1916_, 0);
v_opts_1919_ = lean_ctor_get(v_a_1916_, 1);
v___x_1920_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
lean_inc_ref(v_env_1918_);
v___x_1921_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1918_, v_opts_1919_, v___x_1920_, v_constName_1915_);
v___x_1922_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object* v_constName_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_constName_1923_, v_a_1924_);
lean_dec_ref(v_a_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1927_){
_start:
{
lean_object* v_fst_1928_; 
v_fst_1928_ = lean_ctor_get(v_x_1927_, 0);
lean_inc(v_fst_1928_);
return v_fst_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1929_);
lean_dec_ref(v_x_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_box(0);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1933_);
lean_dec_ref(v_x_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1935_, lean_object* v_s_1936_){
_start:
{
lean_object* v_fst_1937_; lean_object* v___x_1938_; 
v_fst_1937_ = lean_ctor_get(v_s_1936_, 0);
lean_inc_n(v_fst_1937_, 3);
v___x_1938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1938_, 0, v_fst_1937_);
lean_ctor_set(v___x_1938_, 1, v_fst_1937_);
lean_ctor_set(v___x_1938_, 2, v_fst_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1939_, lean_object* v_s_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1939_, v_s_1940_);
lean_dec_ref(v_s_1940_);
lean_dec_ref(v_x_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1942_, lean_object* v_x_1943_){
_start:
{
lean_object* v_snd_1944_; lean_object* v_fst_1945_; lean_object* v_snd_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1965_; 
v_snd_1944_ = lean_ctor_get(v_x_1943_, 1);
lean_inc(v_snd_1944_);
v_fst_1945_ = lean_ctor_get(v_x_1942_, 0);
v_snd_1946_ = lean_ctor_get(v_x_1942_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_x_1942_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1948_ = v_x_1942_;
v_isShared_1949_ = v_isSharedCheck_1965_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snd_1946_);
lean_inc(v_fst_1945_);
lean_dec(v_x_1942_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1965_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_fst_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1963_; 
v_fst_1950_ = lean_ctor_get(v_x_1943_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_x_1943_, 1);
lean_dec(v_unused_1964_);
v___x_1952_ = v_x_1943_;
v_isShared_1953_ = v_isSharedCheck_1963_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_fst_1950_);
lean_dec(v_x_1943_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1963_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_priority_1954_; lean_object* v___x_1956_; 
v_priority_1954_ = lean_ctor_get(v_snd_1944_, 0);
lean_inc(v_priority_1954_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_priority_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_fst_1950_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_priority_1954_);
v___x_1956_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1957_ = lean_array_push(v_fst_1945_, v___x_1956_);
v___x_1958_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_snd_1946_, v_snd_1944_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1958_);
lean_ctor_set(v___x_1948_, 0, v___x_1957_);
v___x_1960_ = v___x_1948_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_1966_, lean_object* v___x_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_st_ref_get(v___x_1966_);
v___x_1970_ = lean_mk_empty_array_with_capacity(v___x_1967_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1969_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_1973_, lean_object* v___x_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_1973_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(lean_object* v_as_1977_, size_t v_i_1978_, size_t v_stop_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_eq(v_i_1978_, v_stop_1979_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2007_; 
v___x_1984_ = lean_array_uget(v_as_1977_, v_i_1978_);
v_fst_1985_ = lean_ctor_get(v___x_1984_, 0);
v_snd_1986_ = lean_ctor_get(v___x_1984_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1988_ = v___x_1984_;
v_isShared_1989_ = v_isSharedCheck_2007_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_snd_1986_);
lean_inc(v_fst_1985_);
lean_dec(v___x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2007_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_fst_1985_, v___y_1981_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_a_1991_);
lean_ctor_set(v___x_1988_, 0, v_snd_1986_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_snd_1986_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_a_1991_);
v___x_1993_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; size_t v___x_1995_; size_t v___x_1996_; 
v___x_1994_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_b_1980_, v___x_1993_);
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1978_, v___x_1995_);
v_i_1978_ = v___x_1996_;
v_b_1980_ = v___x_1994_;
goto _start;
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_del_object(v___x_1988_);
lean_dec(v_snd_1986_);
lean_dec_ref(v_b_1980_);
v_a_1999_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1980_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_2009_, lean_object* v_i_2010_, lean_object* v_stop_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
size_t v_i_boxed_2015_; size_t v_stop_boxed_2016_; lean_object* v_res_2017_; 
v_i_boxed_2015_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_stop_boxed_2016_ = lean_unbox_usize(v_stop_2011_);
lean_dec(v_stop_2011_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v_as_2009_, v_i_boxed_2015_, v_stop_boxed_2016_, v_b_2012_, v___y_2013_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v_as_2009_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(lean_object* v_as_2018_, size_t v_i_2019_, size_t v_stop_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_a_2025_; lean_object* v___y_2030_; uint8_t v___x_2032_; 
v___x_2032_ = lean_usize_dec_eq(v_i_2019_, v_stop_2020_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_array_uget_borrowed(v_as_2018_, v_i_2019_);
v___x_2035_ = lean_array_get_size(v___x_2034_);
v___x_2036_ = lean_nat_dec_lt(v___x_2033_, v___x_2035_);
if (v___x_2036_ == 0)
{
v_a_2025_ = v_b_2021_;
goto v___jp_2024_;
}
else
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_nat_dec_le(v___x_2035_, v___x_2035_);
if (v___x_2037_ == 0)
{
if (v___x_2036_ == 0)
{
v_a_2025_ = v_b_2021_;
goto v___jp_2024_;
}
else
{
size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = lean_usize_of_nat(v___x_2035_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v___x_2034_, v___x_2038_, v___x_2039_, v_b_2021_, v___y_2022_);
v___y_2030_ = v___x_2040_;
goto v___jp_2029_;
}
}
else
{
size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = lean_usize_of_nat(v___x_2035_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v___x_2034_, v___x_2041_, v___x_2042_, v_b_2021_, v___y_2022_);
v___y_2030_ = v___x_2043_;
goto v___jp_2029_;
}
}
}
else
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_b_2021_);
return v___x_2044_;
}
v___jp_2024_:
{
size_t v___x_2026_; size_t v___x_2027_; 
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2019_, v___x_2026_);
v_i_2019_ = v___x_2027_;
v_b_2021_ = v_a_2025_;
goto _start;
}
v___jp_2029_:
{
if (lean_obj_tag(v___y_2030_) == 0)
{
lean_object* v_a_2031_; 
v_a_2031_ = lean_ctor_get(v___y_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___y_2030_, 1);
v_a_2025_ = v_a_2031_;
goto v___jp_2024_;
}
else
{
return v___y_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
size_t v_i_boxed_2051_; size_t v_stop_boxed_2052_; lean_object* v_res_2053_; 
v_i_boxed_2051_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2052_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2045_, v_i_boxed_2051_, v_stop_boxed_2052_, v_b_2048_, v___y_2049_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_as_2045_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2054_, lean_object* v___x_2055_, lean_object* v_as_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_a_2060_; lean_object* v___y_2065_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = lean_st_ref_get(v___x_2055_);
v___x_2076_ = lean_array_get_size(v_as_2056_);
v___x_2077_ = lean_nat_dec_lt(v___x_2054_, v___x_2076_);
if (v___x_2077_ == 0)
{
v_a_2060_ = v___x_2075_;
goto v___jp_2059_;
}
else
{
uint8_t v___x_2078_; 
v___x_2078_ = lean_nat_dec_le(v___x_2076_, v___x_2076_);
if (v___x_2078_ == 0)
{
if (v___x_2077_ == 0)
{
v_a_2060_ = v___x_2075_;
goto v___jp_2059_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2076_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2056_, v___x_2079_, v___x_2080_, v___x_2075_, v___y_2057_);
v___y_2065_ = v___x_2081_;
goto v___jp_2064_;
}
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2076_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2056_, v___x_2082_, v___x_2083_, v___x_2075_, v___y_2057_);
v___y_2065_ = v___x_2084_;
goto v___jp_2064_;
}
}
v___jp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_mk_empty_array_with_capacity(v___x_2054_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_a_2060_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
v___jp_2064_:
{
if (lean_obj_tag(v___y_2065_) == 0)
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___y_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___y_2065_, 1);
v_a_2060_ = v_a_2066_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___y_2065_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___y_2065_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___y_2065_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___y_2065_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v_as_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2085_, v___x_2086_, v_as_2087_, v___y_2088_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v_as_2087_);
lean_dec(v___x_2086_);
lean_dec(v___x_2085_);
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; 
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_2101_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_2101_, 0, v___x_2100_);
lean_closure_set(v___f_2101_, 1, v___x_2099_);
return v___f_2101_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___f_2104_; 
v___x_2102_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_2103_ = lean_unsigned_to_nat(0u);
v___f_2104_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_2104_, 0, v___x_2103_);
lean_closure_set(v___f_2104_, 1, v___x_2102_);
return v___f_2104_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___f_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_box(2);
v___f_2107_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2108_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2109_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2110_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___f_2111_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2113_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___f_2111_);
lean_ctor_set(v___x_2113_, 2, v___f_2110_);
lean_ctor_set(v___x_2113_, 3, v___f_2109_);
lean_ctor_set(v___x_2113_, 4, v___f_2108_);
lean_ctor_set(v___x_2113_, 5, v___f_2107_);
lean_ctor_set(v___x_2113_, 6, v___x_2106_);
lean_ctor_set(v___x_2113_, 7, v___x_2105_);
return v___x_2113_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___f_2114_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2115_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___f_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2119_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object* v_env_2122_){
_start:
{
lean_object* v___x_2123_; lean_object* v_toEnvExtension_2124_; lean_object* v_asyncMode_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_snd_2129_; 
v___x_2123_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2124_ = lean_ctor_get(v___x_2123_, 0);
v_asyncMode_2125_ = lean_ctor_get(v_toEnvExtension_2124_, 2);
v___x_2126_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_2127_ = lean_box(0);
v___x_2128_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2126_, v___x_2123_, v_env_2122_, v_asyncMode_2125_, v___x_2127_);
v_snd_2129_ = lean_ctor_get(v___x_2128_, 1);
lean_inc(v_snd_2129_);
lean_dec(v___x_2128_);
return v_snd_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v___x_2130_, lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v___x_2133_, lean_object* v_decl_2134_, lean_object* v_stx_2135_, uint8_t v_kind_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Attribute_Builtin_getPrio(v_stx_2135_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___x_2194_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc(v_decl_2134_);
lean_inc(v___x_2133_);
v___x_2194_ = l_Lean_ensureAttrDeclIsMeta(v___x_2133_, v_decl_2134_, v_kind_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2194_) == 0)
{
uint8_t v___x_2195_; uint8_t v___x_2196_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2195_ = 0;
v___x_2196_ = l_Lean_instBEqAttributeKind_beq(v_kind_2136_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
lean_dec(v_a_2141_);
lean_dec(v_decl_2134_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec(v___x_2130_);
v___x_2197_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_2133_, v_kind_2136_, v___y_2137_, v___y_2138_);
return v___x_2197_;
}
else
{
v___y_2175_ = v___y_2137_;
v___y_2176_ = v___y_2138_;
goto v___jp_2174_;
}
}
else
{
lean_dec(v_a_2141_);
lean_dec(v_decl_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec(v___x_2130_);
return v___x_2194_;
}
v___jp_2142_:
{
lean_object* v___x_2145_; lean_object* v_toCold_2146_; lean_object* v_env_2147_; lean_object* v_ref_2148_; lean_object* v_options_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2145_ = lean_st_ref_get(v___y_2144_);
v_toCold_2146_ = lean_ctor_get(v___y_2143_, 0);
v_env_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_ref(v_env_2147_);
lean_dec(v___x_2145_);
v_ref_2148_ = lean_ctor_get(v___y_2143_, 2);
v_options_2149_ = lean_ctor_get(v_toCold_2146_, 2);
lean_inc_ref(v_options_2149_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_env_2147_);
lean_ctor_set(v___x_2150_, 1, v_options_2149_);
lean_inc(v_decl_2134_);
v___x_2151_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_decl_2134_, v___x_2150_);
lean_dec_ref_known(v___x_2150_, 2);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_env_2155_; lean_object* v___x_2156_; lean_object* v_toEnvExtension_2157_; lean_object* v_asyncMode_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2141_);
lean_ctor_set(v___x_2153_, 1, v_a_2152_);
v___x_2154_ = lean_st_ref_get(v___y_2144_);
v_env_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc_ref(v_env_2155_);
lean_dec(v___x_2154_);
v___x_2156_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2157_ = lean_ctor_get(v___x_2156_, 0);
v_asyncMode_2158_ = lean_ctor_get(v_toEnvExtension_2157_, 2);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_decl_2134_);
lean_ctor_set(v___x_2159_, 1, v___x_2153_);
v___x_2160_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2156_, v_env_2155_, v___x_2159_, v_asyncMode_2158_, v___x_2130_);
v___x_2161_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2160_, v___y_2144_);
return v___x_2161_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2141_);
lean_dec(v_decl_2134_);
lean_dec(v___x_2130_);
v_a_2162_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2164_ = v___x_2151_;
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2151_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2166_ = lean_io_error_to_string(v_a_2162_);
v___x_2167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
v___x_2168_ = l_Lean_MessageData_ofFormat(v___x_2167_);
lean_inc(v_ref_2148_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v_ref_2148_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2169_);
v___x_2171_ = v___x_2164_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
v___jp_2174_:
{
lean_object* v___x_2177_; 
lean_inc(v_decl_2134_);
v___x_2177_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_2134_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_ConstantInfo_type(v_a_2178_);
lean_dec(v_a_2178_);
v___x_2180_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0));
v___x_2181_ = l_Lean_Name_mkStr3(v___x_2131_, v___x_2132_, v___x_2180_);
v___x_2182_ = l_Lean_Expr_isConstOf(v___x_2179_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_a_2141_);
lean_dec(v___x_2130_);
v___x_2183_ = lean_box(0);
v___x_2184_ = l_Lean_mkConst(v___x_2181_, v___x_2183_);
v___x_2185_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_2133_, v_decl_2134_, v___x_2179_, v___x_2184_, v___y_2175_, v___y_2176_);
return v___x_2185_;
}
else
{
lean_dec(v___x_2181_);
lean_dec_ref(v___x_2179_);
lean_dec(v___x_2133_);
v___y_2143_ = v___y_2175_;
v___y_2144_ = v___y_2176_;
goto v___jp_2142_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2141_);
lean_dec(v_decl_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec(v___x_2130_);
v_a_2186_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_decl_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec(v___x_2130_);
v_a_2198_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2140_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2140_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v___x_2208_, lean_object* v___x_2209_, lean_object* v_decl_2210_, lean_object* v_stx_2211_, lean_object* v_kind_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v_kind_boxed_2216_; lean_object* v_res_2217_; 
v_kind_boxed_2216_ = lean_unbox(v_kind_2212_);
v_res_2217_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(v___x_2206_, v___x_2207_, v___x_2208_, v___x_2209_, v_decl_2210_, v_stx_2211_, v_kind_boxed_2216_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2217_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_unsigned_to_nat(3853185248u);
v___x_2219_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2220_ = l_Lean_Name_num___override(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2222_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2223_ = l_Lean_Name_str___override(v___x_2222_, v___x_2221_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2225_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2226_ = l_Lean_Name_str___override(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_unsigned_to_nat(2u);
v___x_2228_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2229_ = l_Lean_Name_num___override(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2241_ = 1;
v___x_2242_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2243_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2244_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2245_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2243_);
lean_ctor_set(v___x_2245_, 2, v___x_2242_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*3, v___x_2241_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___f_2246_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___f_2247_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2248_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___f_2247_);
lean_ctor_set(v___x_2249_, 2, v___f_2246_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2252_ = l_Lean_registerBuiltinAttribute(v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object* v_attr_2255_, lean_object* v_mk_2256_, lean_object* v_env_2257_, lean_object* v_kind_2258_){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v_attr_2255_, v_env_2257_, v_kind_2258_);
v___x_2260_ = l_List_head_x3f___redArg(v___x_2259_);
lean_dec(v___x_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2261_; 
lean_dec_ref(v_mk_2256_);
v___x_2261_ = lean_box(0);
return v___x_2261_;
}
else
{
lean_object* v_val_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2281_; 
v_val_2262_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2264_ = v___x_2260_;
v_isShared_2265_ = v_isSharedCheck_2281_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_val_2262_);
lean_dec(v___x_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2281_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_toOLeanEntry_2266_; lean_object* v_value_2267_; lean_object* v_declName_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2279_; 
v_toOLeanEntry_2266_ = lean_ctor_get(v_val_2262_, 0);
lean_inc_ref(v_toOLeanEntry_2266_);
v_value_2267_ = lean_ctor_get(v_val_2262_, 1);
lean_inc(v_value_2267_);
lean_dec(v_val_2262_);
v_declName_2268_ = lean_ctor_get(v_toOLeanEntry_2266_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_toOLeanEntry_2266_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v_toOLeanEntry_2266_, 0);
lean_dec(v_unused_2280_);
v___x_2270_ = v_toOLeanEntry_2266_;
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_declName_2268_);
lean_dec(v_toOLeanEntry_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_apply_1(v_mk_2256_, v_value_2267_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2272_);
lean_ctor_set(v___x_2270_, 0, v_declName_2268_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_declName_2268_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2274_);
v___x_2276_ = v___x_2264_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object* v_attr_2282_, lean_object* v_mk_2283_, lean_object* v_env_2284_, lean_object* v_kind_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2282_, v_mk_2283_, v_env_2284_, v_kind_2285_);
lean_dec(v_kind_2285_);
lean_dec_ref(v_attr_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object* v_00_u03b1_2287_, lean_object* v_attr_2288_, lean_object* v_mk_2289_, lean_object* v_env_2290_, lean_object* v_x_2291_, lean_object* v_kind_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2288_, v_mk_2289_, v_env_2290_, v_kind_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_attr_2295_, lean_object* v_mk_2296_, lean_object* v_env_2297_, lean_object* v_x_2298_, lean_object* v_kind_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Fmt_keyedFmtProvider(v_00_u03b1_2294_, v_attr_2295_, v_mk_2296_, v_env_2297_, v_x_2298_, v_kind_2299_);
lean_dec(v_kind_2299_);
lean_dec_ref(v_x_2298_);
lean_dec_ref(v_attr_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_2301_, lean_object* v_i_2302_, lean_object* v_k_2303_){
_start:
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_array_get_size(v_keys_2301_);
v___x_2305_ = lean_nat_dec_lt(v_i_2302_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_dec(v_i_2302_);
return v___x_2305_;
}
else
{
lean_object* v_k_x27_2306_; uint8_t v___x_2307_; 
v_k_x27_2306_ = lean_array_fget_borrowed(v_keys_2301_, v_i_2302_);
v___x_2307_ = l_Lean_instBEqExtraModUse_beq(v_k_2303_, v_k_x27_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_unsigned_to_nat(1u);
v___x_2309_ = lean_nat_add(v_i_2302_, v___x_2308_);
lean_dec(v_i_2302_);
v_i_2302_ = v___x_2309_;
goto _start;
}
else
{
lean_dec(v_i_2302_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_2311_, lean_object* v_i_2312_, lean_object* v_k_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2311_, v_i_2312_, v_k_2313_);
lean_dec_ref(v_k_2313_);
lean_dec_ref(v_keys_2311_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_2316_, size_t v_x_2317_, lean_object* v_x_2318_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v_es_2319_; lean_object* v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v_j_2323_; lean_object* v___x_2324_; 
v_es_2319_ = lean_ctor_get(v_x_2316_, 0);
v___x_2320_ = lean_box(2);
v___x_2321_ = ((size_t)31ULL);
v___x_2322_ = lean_usize_land(v_x_2317_, v___x_2321_);
v_j_2323_ = lean_usize_to_nat(v___x_2322_);
v___x_2324_ = lean_array_get_borrowed(v___x_2320_, v_es_2319_, v_j_2323_);
lean_dec(v_j_2323_);
switch(lean_obj_tag(v___x_2324_))
{
case 0:
{
lean_object* v_key_2325_; uint8_t v___x_2326_; 
v_key_2325_ = lean_ctor_get(v___x_2324_, 0);
v___x_2326_ = l_Lean_instBEqExtraModUse_beq(v_x_2318_, v_key_2325_);
return v___x_2326_;
}
case 1:
{
lean_object* v_node_2327_; size_t v___x_2328_; size_t v___x_2329_; 
v_node_2327_ = lean_ctor_get(v___x_2324_, 0);
v___x_2328_ = ((size_t)5ULL);
v___x_2329_ = lean_usize_shift_right(v_x_2317_, v___x_2328_);
v_x_2316_ = v_node_2327_;
v_x_2317_ = v___x_2329_;
goto _start;
}
default: 
{
uint8_t v___x_2331_; 
v___x_2331_ = 0;
return v___x_2331_;
}
}
}
else
{
lean_object* v_ks_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_ks_2332_ = lean_ctor_get(v_x_2316_, 0);
v___x_2333_ = lean_unsigned_to_nat(0u);
v___x_2334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_2332_, v___x_2333_, v_x_2318_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
size_t v_x_5070__boxed_2338_; uint8_t v_res_2339_; lean_object* v_r_2340_; 
v_x_5070__boxed_2338_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_res_2339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2335_, v_x_5070__boxed_2338_, v_x_2337_);
lean_dec_ref(v_x_2337_);
lean_dec_ref(v_x_2335_);
v_r_2340_ = lean_box(v_res_2339_);
return v_r_2340_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint64_t v___x_2343_; size_t v___x_2344_; uint8_t v___x_2345_; 
v___x_2343_ = l_Lean_instHashableExtraModUse_hash(v_x_2342_);
v___x_2344_ = lean_uint64_to_usize(v___x_2343_);
v___x_2345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2341_, v___x_2344_, v_x_2342_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_res_2348_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2346_, v_x_2347_);
lean_dec_ref(v_x_2347_);
lean_dec_ref(v_x_2346_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2350_; double v___x_2351_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = lean_float_of_nat(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object* v_cls_2355_, lean_object* v_msg_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_ref_2360_; lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2406_; 
v_ref_2360_ = lean_ctor_get(v___y_2357_, 2);
v___x_2361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_2356_, v___y_2357_, v___y_2358_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2406_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2406_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v_traceState_2367_; lean_object* v_env_2368_; lean_object* v_nextMacroScope_2369_; lean_object* v_ngen_2370_; lean_object* v_auxDeclNGen_2371_; lean_object* v_cache_2372_; lean_object* v_messages_2373_; lean_object* v_infoState_2374_; lean_object* v_snapshotTasks_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2405_; 
v___x_2366_ = lean_st_ref_take(v___y_2358_);
v_traceState_2367_ = lean_ctor_get(v___x_2366_, 4);
v_env_2368_ = lean_ctor_get(v___x_2366_, 0);
v_nextMacroScope_2369_ = lean_ctor_get(v___x_2366_, 1);
v_ngen_2370_ = lean_ctor_get(v___x_2366_, 2);
v_auxDeclNGen_2371_ = lean_ctor_get(v___x_2366_, 3);
v_cache_2372_ = lean_ctor_get(v___x_2366_, 5);
v_messages_2373_ = lean_ctor_get(v___x_2366_, 6);
v_infoState_2374_ = lean_ctor_get(v___x_2366_, 7);
v_snapshotTasks_2375_ = lean_ctor_get(v___x_2366_, 8);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2405_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_snapshotTasks_2375_);
lean_inc(v_infoState_2374_);
lean_inc(v_messages_2373_);
lean_inc(v_cache_2372_);
lean_inc(v_traceState_2367_);
lean_inc(v_auxDeclNGen_2371_);
lean_inc(v_ngen_2370_);
lean_inc(v_nextMacroScope_2369_);
lean_inc(v_env_2368_);
lean_dec(v___x_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2405_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
uint64_t v_tid_2379_; lean_object* v_traces_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2404_; 
v_tid_2379_ = lean_ctor_get_uint64(v_traceState_2367_, sizeof(void*)*1);
v_traces_2380_ = lean_ctor_get(v_traceState_2367_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_traceState_2367_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2382_ = v_traceState_2367_;
v_isShared_2383_ = v_isSharedCheck_2404_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_traces_2380_);
lean_dec(v_traceState_2367_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2404_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; double v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0);
v___x_2387_ = 0;
v___x_2388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2389_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2389_, 0, v_cls_2355_);
lean_ctor_set(v___x_2389_, 1, v___x_2385_);
lean_ctor_set(v___x_2389_, 2, v___x_2388_);
lean_ctor_set_float(v___x_2389_, sizeof(void*)*3, v___x_2386_);
lean_ctor_set_float(v___x_2389_, sizeof(void*)*3 + 8, v___x_2386_);
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*3 + 16, v___x_2387_);
v___x_2390_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2));
v___x_2391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v_a_2362_);
lean_ctor_set(v___x_2391_, 2, v___x_2390_);
lean_inc(v_ref_2360_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_ref_2360_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = l_Lean_PersistentArray_push___redArg(v_traces_2380_, v___x_2392_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2393_);
v___x_2395_ = v___x_2382_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2393_);
lean_ctor_set_uint64(v_reuseFailAlloc_2403_, sizeof(void*)*1, v_tid_2379_);
v___x_2395_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 4, v___x_2395_);
v___x_2397_ = v___x_2377_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_env_2368_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_nextMacroScope_2369_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_ngen_2370_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v_auxDeclNGen_2371_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2402_, 5, v_cache_2372_);
lean_ctor_set(v_reuseFailAlloc_2402_, 6, v_messages_2373_);
lean_ctor_set(v_reuseFailAlloc_2402_, 7, v_infoState_2374_);
lean_ctor_set(v_reuseFailAlloc_2402_, 8, v_snapshotTasks_2375_);
v___x_2397_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_st_ref_put(v___y_2358_, v___x_2397_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2384_);
v___x_2400_ = v___x_2364_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2384_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2407_, lean_object* v_msg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2407_, v_msg_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2412_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2413_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v_cls_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_cls_2428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2429_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9));
v___x_2430_ = l_Lean_Name_append(v___x_2429_, v_cls_2428_);
return v___x_2430_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13));
v___x_2436_ = l_Lean_stringToMessageData(v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object* v_mod_2441_, uint8_t v_isMeta_2442_, lean_object* v_hint_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_env_2449_; uint8_t v_isExporting_2450_; lean_object* v_entry_2451_; lean_object* v___x_2452_; lean_object* v_env_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___y_2458_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0);
v___x_2448_ = lean_st_ref_get(v___y_2445_);
v_env_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_env_2449_);
lean_dec(v___x_2448_);
v_isExporting_2450_ = lean_ctor_get_uint8(v_env_2449_, sizeof(void*)*8);
lean_dec_ref(v_env_2449_);
lean_inc(v_mod_2441_);
v_entry_2451_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2451_, 0, v_mod_2441_);
lean_ctor_set_uint8(v_entry_2451_, sizeof(void*)*1, v_isExporting_2450_);
lean_ctor_set_uint8(v_entry_2451_, sizeof(void*)*1 + 1, v_isMeta_2442_);
v___x_2452_ = lean_st_ref_get(v___y_2445_);
v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc_ref(v_env_2453_);
lean_dec(v___x_2452_);
v___x_2454_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2455_ = lean_box(1);
v___x_2456_ = lean_box(0);
v___x_2483_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2447_, v___x_2454_, v_env_2453_, v___x_2455_, v___x_2456_);
v___x_2484_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v___x_2483_, v_entry_2451_);
lean_dec(v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v_toCold_2485_; lean_object* v_options_2486_; uint8_t v_hasTrace_2487_; 
v_toCold_2485_ = lean_ctor_get(v___y_2444_, 0);
v_options_2486_ = lean_ctor_get(v_toCold_2485_, 2);
v_hasTrace_2487_ = lean_ctor_get_uint8(v_options_2486_, sizeof(void*)*1);
if (v_hasTrace_2487_ == 0)
{
lean_dec(v_hint_2443_);
lean_dec(v_mod_2441_);
v___y_2458_ = v___y_2445_;
goto v___jp_2457_;
}
else
{
lean_object* v_inheritedTraceOptions_2488_; lean_object* v_cls_2489_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_inheritedTraceOptions_2488_ = lean_ctor_get(v_toCold_2485_, 11);
v_cls_2489_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2509_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10);
v___x_2510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2488_, v_options_2486_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_dec(v_hint_2443_);
lean_dec(v_mod_2441_);
v___y_2458_ = v___y_2445_;
goto v___jp_2457_;
}
else
{
lean_object* v___x_2511_; lean_object* v___y_2513_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12);
if (v_isExporting_2450_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17));
v___y_2513_ = v___x_2520_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18));
v___y_2513_ = v___x_2521_;
goto v___jp_2512_;
}
v___jp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_inc_ref(v___y_2513_);
v___x_2514_ = l_Lean_stringToMessageData(v___y_2513_);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2511_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
if (v_isMeta_2442_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15));
v___y_2496_ = v___x_2517_;
v___y_2497_ = v___x_2518_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16));
v___y_2496_ = v___x_2517_;
v___y_2497_ = v___x_2519_;
goto v___jp_2495_;
}
}
}
v___jp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2491_);
lean_ctor_set(v___x_2493_, 1, v___y_2492_);
v___x_2494_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2489_, v___x_2493_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref_known(v___x_2494_, 1);
v___y_2458_ = v___y_2445_;
goto v___jp_2457_;
}
else
{
lean_dec_ref_known(v_entry_2451_, 1);
return v___x_2494_;
}
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
lean_inc_ref(v___y_2497_);
v___x_2498_ = l_Lean_stringToMessageData(v___y_2497_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2496_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_MessageData_ofName(v_mod_2441_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_Name_isAnonymous(v_hint_2443_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6);
v___x_2506_ = l_Lean_MessageData_ofName(v_hint_2443_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___y_2491_ = v___x_2503_;
v___y_2492_ = v___x_2507_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2508_; 
lean_dec(v_hint_2443_);
v___x_2508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7);
v___y_2491_ = v___x_2503_;
v___y_2492_ = v___x_2508_;
goto v___jp_2490_;
}
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref_known(v_entry_2451_, 1);
lean_dec(v_hint_2443_);
lean_dec(v_mod_2441_);
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
v___jp_2457_:
{
lean_object* v___x_2459_; lean_object* v_toEnvExtension_2460_; lean_object* v_env_2461_; lean_object* v_nextMacroScope_2462_; lean_object* v_ngen_2463_; lean_object* v_auxDeclNGen_2464_; lean_object* v_traceState_2465_; lean_object* v_messages_2466_; lean_object* v_infoState_2467_; lean_object* v_snapshotTasks_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2481_; 
v___x_2459_ = lean_st_ref_take(v___y_2458_);
v_toEnvExtension_2460_ = lean_ctor_get(v___x_2454_, 0);
v_env_2461_ = lean_ctor_get(v___x_2459_, 0);
v_nextMacroScope_2462_ = lean_ctor_get(v___x_2459_, 1);
v_ngen_2463_ = lean_ctor_get(v___x_2459_, 2);
v_auxDeclNGen_2464_ = lean_ctor_get(v___x_2459_, 3);
v_traceState_2465_ = lean_ctor_get(v___x_2459_, 4);
v_messages_2466_ = lean_ctor_get(v___x_2459_, 6);
v_infoState_2467_ = lean_ctor_get(v___x_2459_, 7);
v_snapshotTasks_2468_ = lean_ctor_get(v___x_2459_, 8);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2459_, 5);
lean_dec(v_unused_2482_);
v___x_2470_ = v___x_2459_;
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_snapshotTasks_2468_);
lean_inc(v_infoState_2467_);
lean_inc(v_messages_2466_);
lean_inc(v_traceState_2465_);
lean_inc(v_auxDeclNGen_2464_);
lean_inc(v_ngen_2463_);
lean_inc(v_nextMacroScope_2462_);
lean_inc(v_env_2461_);
lean_dec(v___x_2459_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_asyncMode_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v_asyncMode_2472_ = lean_ctor_get(v_toEnvExtension_2460_, 2);
v___x_2473_ = lean_box(0);
v___x_2474_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2454_, v_env_2461_, v_entry_2451_, v_asyncMode_2472_, v___x_2456_);
v___x_2475_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 5, v___x_2475_);
lean_ctor_set(v___x_2470_, 0, v___x_2474_);
v___x_2477_ = v___x_2470_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2462_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2463_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2464_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_traceState_2465_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_messages_2466_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_infoState_2467_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_snapshotTasks_2468_);
v___x_2477_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_st_ref_put(v___y_2458_, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2473_);
return v___x_2479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object* v_mod_2524_, lean_object* v_isMeta_2525_, lean_object* v_hint_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v_isMeta_boxed_2530_; lean_object* v_res_2531_; 
v_isMeta_boxed_2530_ = lean_unbox(v_isMeta_2525_);
v_res_2531_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_mod_2524_, v_isMeta_boxed_2530_, v_hint_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object* v___x_2532_, lean_object* v_declName_2533_, lean_object* v_as_2534_, size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_b_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_usize_dec_lt(v_i_2536_, v_sz_2535_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_declName_2533_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_b_2537_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v_modules_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v_toImport_2548_; lean_object* v_module_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2543_ = l_Lean_Environment_header(v___x_2532_);
v_modules_2544_ = lean_ctor_get(v___x_2543_, 3);
lean_inc_ref(v_modules_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2546_ = lean_array_uget_borrowed(v_as_2534_, v_i_2536_);
v___x_2547_ = lean_array_get(v___x_2545_, v_modules_2544_, v_a_2546_);
lean_dec_ref(v_modules_2544_);
v_toImport_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc_ref(v_toImport_2548_);
lean_dec(v___x_2547_);
v_module_2549_ = lean_ctor_get(v_toImport_2548_, 0);
lean_inc(v_module_2549_);
lean_dec_ref(v_toImport_2548_);
v___x_2550_ = lean_box(0);
v___x_2551_ = 0;
lean_inc(v_declName_2533_);
v___x_2552_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2549_, v___x_2551_, v_declName_2533_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2552_) == 0)
{
size_t v___x_2553_; size_t v___x_2554_; 
lean_dec_ref_known(v___x_2552_, 1);
v___x_2553_ = ((size_t)1ULL);
v___x_2554_ = lean_usize_add(v_i_2536_, v___x_2553_);
v_i_2536_ = v___x_2554_;
v_b_2537_ = v___x_2550_;
goto _start;
}
else
{
lean_dec(v_declName_2533_);
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object* v___x_2556_, lean_object* v_declName_2557_, lean_object* v_as_2558_, lean_object* v_sz_2559_, lean_object* v_i_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
size_t v_sz_boxed_2565_; size_t v_i_boxed_2566_; lean_object* v_res_2567_; 
v_sz_boxed_2565_ = lean_unbox_usize(v_sz_2559_);
lean_dec(v_sz_2559_);
v_i_boxed_2566_ = lean_unbox_usize(v_i_2560_);
lean_dec(v_i_2560_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v___x_2556_, v_declName_2557_, v_as_2558_, v_sz_boxed_2565_, v_i_boxed_2566_, v_b_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec_ref(v_as_2558_);
lean_dec_ref(v___x_2556_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2568_, lean_object* v_x_2569_){
_start:
{
if (lean_obj_tag(v_x_2569_) == 0)
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_box(0);
return v___x_2570_;
}
else
{
lean_object* v_key_2571_; lean_object* v_value_2572_; lean_object* v_tail_2573_; uint8_t v___x_2574_; 
v_key_2571_ = lean_ctor_get(v_x_2569_, 0);
v_value_2572_ = lean_ctor_get(v_x_2569_, 1);
v_tail_2573_ = lean_ctor_get(v_x_2569_, 2);
v___x_2574_ = lean_name_eq(v_key_2571_, v_a_2568_);
if (v___x_2574_ == 0)
{
v_x_2569_ = v_tail_2573_;
goto _start;
}
else
{
lean_object* v___x_2576_; 
lean_inc(v_value_2572_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v_value_2572_);
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2577_, lean_object* v_x_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2577_, v_x_2578_);
lean_dec(v_x_2578_);
lean_dec(v_a_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object* v_m_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_buckets_2582_; lean_object* v___x_2583_; uint64_t v___y_2585_; 
v_buckets_2582_ = lean_ctor_get(v_m_2580_, 1);
v___x_2583_ = lean_array_get_size(v_buckets_2582_);
if (lean_obj_tag(v_a_2581_) == 0)
{
uint64_t v___x_2599_; 
v___x_2599_ = 1723ULL;
v___y_2585_ = v___x_2599_;
goto v___jp_2584_;
}
else
{
uint64_t v_hash_2600_; 
v_hash_2600_ = lean_ctor_get_uint64(v_a_2581_, sizeof(void*)*2);
v___y_2585_ = v_hash_2600_;
goto v___jp_2584_;
}
v___jp_2584_:
{
uint64_t v___x_2586_; uint64_t v___x_2587_; uint64_t v_fold_2588_; uint64_t v___x_2589_; uint64_t v___x_2590_; uint64_t v___x_2591_; size_t v___x_2592_; size_t v___x_2593_; size_t v___x_2594_; size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2586_ = 32ULL;
v___x_2587_ = lean_uint64_shift_right(v___y_2585_, v___x_2586_);
v_fold_2588_ = lean_uint64_xor(v___y_2585_, v___x_2587_);
v___x_2589_ = 16ULL;
v___x_2590_ = lean_uint64_shift_right(v_fold_2588_, v___x_2589_);
v___x_2591_ = lean_uint64_xor(v_fold_2588_, v___x_2590_);
v___x_2592_ = lean_uint64_to_usize(v___x_2591_);
v___x_2593_ = lean_usize_of_nat(v___x_2583_);
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_sub(v___x_2593_, v___x_2594_);
v___x_2596_ = lean_usize_land(v___x_2592_, v___x_2595_);
v___x_2597_ = lean_array_uget_borrowed(v_buckets_2582_, v___x_2596_);
v___x_2598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2581_, v___x_2597_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object* v_m_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_m_2601_);
return v_res_2603_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object* v_declName_2607_, uint8_t v_isMeta_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_env_2617_; lean_object* v___y_2619_; lean_object* v___x_2632_; 
v___x_2612_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0);
v___x_2613_ = lean_st_ref_get(v___y_2610_);
v_env_2617_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_ref(v_env_2617_);
lean_dec(v___x_2613_);
v___x_2632_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2617_, v_declName_2607_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_dec_ref(v_env_2617_);
lean_dec(v_declName_2607_);
goto v___jp_2614_;
}
else
{
lean_object* v_val_2633_; lean_object* v___x_2634_; lean_object* v_modules_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_val_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_Environment_header(v_env_2617_);
v_modules_2635_ = lean_ctor_get(v___x_2634_, 3);
lean_inc_ref(v_modules_2635_);
lean_dec_ref(v___x_2634_);
v___x_2636_ = lean_array_get_size(v_modules_2635_);
v___x_2637_ = lean_nat_dec_lt(v_val_2633_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_dec_ref(v_modules_2635_);
lean_dec(v_val_2633_);
lean_dec_ref(v_env_2617_);
lean_dec(v_declName_2607_);
goto v___jp_2614_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___y_2641_; 
v___x_2638_ = lean_array_fget(v_modules_2635_, v_val_2633_);
lean_dec(v_val_2633_);
lean_dec_ref(v_modules_2635_);
v___x_2639_ = lean_st_ref_get(v___y_2610_);
if (v_isMeta_2608_ == 0)
{
lean_dec(v___x_2639_);
v___y_2641_ = v_isMeta_2608_;
goto v___jp_2640_;
}
else
{
lean_object* v_env_2652_; uint8_t v___x_2653_; 
v_env_2652_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2639_);
lean_inc(v_declName_2607_);
v___x_2653_ = l_Lean_isMarkedMeta(v_env_2652_, v_declName_2607_);
if (v___x_2653_ == 0)
{
v___y_2641_ = v_isMeta_2608_;
goto v___jp_2640_;
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = 0;
v___y_2641_ = v___x_2654_;
goto v___jp_2640_;
}
}
v___jp_2640_:
{
lean_object* v_toImport_2642_; lean_object* v_module_2643_; lean_object* v___x_2644_; 
v_toImport_2642_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_toImport_2642_);
lean_dec(v___x_2638_);
v_module_2643_ = lean_ctor_get(v_toImport_2642_, 0);
lean_inc(v_module_2643_);
lean_dec_ref(v_toImport_2642_);
lean_inc(v_declName_2607_);
v___x_2644_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2643_, v___y_2641_, v_declName_2607_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = l_Lean_indirectModUseExt;
v___x_2646_ = lean_box(1);
v___x_2647_ = lean_box(0);
lean_inc_ref(v_env_2617_);
v___x_2648_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2612_, v___x_2645_, v_env_2617_, v___x_2646_, v___x_2647_);
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v___x_2648_, v_declName_2607_);
lean_dec(v___x_2648_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1));
v___y_2619_ = v___x_2650_;
goto v___jp_2618_;
}
else
{
lean_object* v_val_2651_; 
v_val_2651_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___x_2649_, 1);
v___y_2619_ = v_val_2651_;
goto v___jp_2618_;
}
}
else
{
lean_dec_ref(v_env_2617_);
lean_dec(v_declName_2607_);
return v___x_2644_;
}
}
}
}
v___jp_2614_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
v___jp_2618_:
{
lean_object* v___x_2620_; size_t v_sz_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2620_ = lean_box(0);
v_sz_2621_ = lean_array_size(v___y_2619_);
v___x_2622_ = ((size_t)0ULL);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v_env_2617_, v_declName_2607_, v___y_2619_, v_sz_2621_, v___x_2622_, v___x_2620_, v___y_2609_, v___y_2610_);
lean_dec_ref(v___y_2619_);
lean_dec_ref(v_env_2617_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2623_, 0);
lean_dec(v_unused_2631_);
v___x_2625_ = v___x_2623_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_dec(v___x_2623_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2620_);
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2620_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object* v_declName_2655_, lean_object* v_isMeta_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_isMeta_boxed_2660_; lean_object* v_res_2661_; 
v_isMeta_boxed_2660_ = lean_unbox(v_isMeta_2656_);
v_res_2661_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v_declName_2655_, v_isMeta_boxed_2660_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2661_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object* v_a_2662_, lean_object* v_x_2663_){
_start:
{
if (lean_obj_tag(v_x_2663_) == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
return v___x_2664_;
}
else
{
lean_object* v_head_2665_; lean_object* v_tail_2666_; uint8_t v___x_2667_; 
v_head_2665_ = lean_ctor_get(v_x_2663_, 0);
v_tail_2666_ = lean_ctor_get(v_x_2663_, 1);
v___x_2667_ = lean_name_eq(v_a_2662_, v_head_2665_);
if (v___x_2667_ == 0)
{
v_x_2663_ = v_tail_2666_;
goto _start;
}
else
{
return v___x_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object* v_a_2669_, lean_object* v_x_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v_a_2669_, v_x_2670_);
lean_dec(v_x_2670_);
lean_dec(v_a_2669_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object* v_t_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v_infoState_2677_; uint8_t v_enabled_2678_; 
v___x_2676_ = lean_st_ref_get(v___y_2674_);
v_infoState_2677_ = lean_ctor_get(v___x_2676_, 7);
lean_inc_ref(v_infoState_2677_);
lean_dec(v___x_2676_);
v_enabled_2678_ = lean_ctor_get_uint8(v_infoState_2677_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2677_);
if (v_enabled_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref(v_t_2673_);
v___x_2679_ = lean_box(0);
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
return v___x_2680_;
}
else
{
lean_object* v___x_2681_; lean_object* v_infoState_2682_; lean_object* v_env_2683_; lean_object* v_nextMacroScope_2684_; lean_object* v_ngen_2685_; lean_object* v_auxDeclNGen_2686_; lean_object* v_traceState_2687_; lean_object* v_cache_2688_; lean_object* v_messages_2689_; lean_object* v_snapshotTasks_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2712_; 
v___x_2681_ = lean_st_ref_take(v___y_2674_);
v_infoState_2682_ = lean_ctor_get(v___x_2681_, 7);
v_env_2683_ = lean_ctor_get(v___x_2681_, 0);
v_nextMacroScope_2684_ = lean_ctor_get(v___x_2681_, 1);
v_ngen_2685_ = lean_ctor_get(v___x_2681_, 2);
v_auxDeclNGen_2686_ = lean_ctor_get(v___x_2681_, 3);
v_traceState_2687_ = lean_ctor_get(v___x_2681_, 4);
v_cache_2688_ = lean_ctor_get(v___x_2681_, 5);
v_messages_2689_ = lean_ctor_get(v___x_2681_, 6);
v_snapshotTasks_2690_ = lean_ctor_get(v___x_2681_, 8);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2692_ = v___x_2681_;
v_isShared_2693_ = v_isSharedCheck_2712_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_snapshotTasks_2690_);
lean_inc(v_infoState_2682_);
lean_inc(v_messages_2689_);
lean_inc(v_cache_2688_);
lean_inc(v_traceState_2687_);
lean_inc(v_auxDeclNGen_2686_);
lean_inc(v_ngen_2685_);
lean_inc(v_nextMacroScope_2684_);
lean_inc(v_env_2683_);
lean_dec(v___x_2681_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2712_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
uint8_t v_enabled_2694_; lean_object* v_assignment_2695_; lean_object* v_lazyAssignment_2696_; lean_object* v_trees_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2711_; 
v_enabled_2694_ = lean_ctor_get_uint8(v_infoState_2682_, sizeof(void*)*3);
v_assignment_2695_ = lean_ctor_get(v_infoState_2682_, 0);
v_lazyAssignment_2696_ = lean_ctor_get(v_infoState_2682_, 1);
v_trees_2697_ = lean_ctor_get(v_infoState_2682_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_infoState_2682_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2699_ = v_infoState_2682_;
v_isShared_2700_ = v_isSharedCheck_2711_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_trees_2697_);
lean_inc(v_lazyAssignment_2696_);
lean_inc(v_assignment_2695_);
lean_dec(v_infoState_2682_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2711_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = l_Lean_PersistentArray_push___redArg(v_trees_2697_, v_t_2673_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 2, v___x_2702_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_assignment_2695_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_lazyAssignment_2696_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v___x_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, sizeof(void*)*3, v_enabled_2694_);
v___x_2704_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 7, v___x_2704_);
v___x_2706_ = v___x_2692_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_env_2683_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_nextMacroScope_2684_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_ngen_2685_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_auxDeclNGen_2686_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_traceState_2687_);
lean_ctor_set(v_reuseFailAlloc_2709_, 5, v_cache_2688_);
lean_ctor_set(v_reuseFailAlloc_2709_, 6, v_messages_2689_);
lean_ctor_set(v_reuseFailAlloc_2709_, 7, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2709_, 8, v_snapshotTasks_2690_);
v___x_2706_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_st_ref_put(v___y_2674_, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2701_);
return v___x_2708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2713_, v___y_2714_);
lean_dec(v___y_2714_);
return v_res_2716_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_unsigned_to_nat(32u);
v___x_2718_ = lean_mk_empty_array_with_capacity(v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2720_ = ((size_t)5ULL);
v___x_2721_ = lean_unsigned_to_nat(0u);
v___x_2722_ = lean_unsigned_to_nat(32u);
v___x_2723_ = lean_mk_empty_array_with_capacity(v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0);
v___x_2725_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___x_2723_);
lean_ctor_set(v___x_2725_, 2, v___x_2721_);
lean_ctor_set(v___x_2725_, 3, v___x_2721_);
lean_ctor_set_usize(v___x_2725_, 4, v___x_2720_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object* v_t_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_infoState_2731_; uint8_t v_enabled_2732_; 
v___x_2730_ = lean_st_ref_get(v___y_2728_);
v_infoState_2731_ = lean_ctor_get(v___x_2730_, 7);
lean_inc_ref(v_infoState_2731_);
lean_dec(v___x_2730_);
v_enabled_2732_ = lean_ctor_get_uint8(v_infoState_2731_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2731_);
if (v_enabled_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec_ref(v_t_2726_);
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1);
v___x_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_t_2726_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v___x_2736_, v___y_2728_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object* v_t_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v_t_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
if (lean_obj_tag(v_a_2743_) == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = l_List_reverse___redArg(v_a_2744_);
return v___x_2745_;
}
else
{
lean_object* v_head_2746_; lean_object* v_tail_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2756_; 
v_head_2746_ = lean_ctor_get(v_a_2743_, 0);
v_tail_2747_ = lean_ctor_get(v_a_2743_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2749_ = v_a_2743_;
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_tail_2747_);
lean_inc(v_head_2746_);
lean_dec(v_a_2743_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = l_Lean_mkLevelParam(v_head_2746_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v_a_2744_);
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_a_2744_);
v___x_2753_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
v_a_2743_ = v_tail_2747_;
v_a_2744_ = v___x_2753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object* v_constName_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v_env_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2761_ = lean_st_ref_get(v___y_2759_);
v_env_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc_ref(v_env_2762_);
lean_dec(v___x_2761_);
v___x_2763_ = 0;
lean_inc(v_constName_2757_);
v___x_2764_ = l_Lean_Environment_findConstVal_x3f(v_env_2762_, v_constName_2757_, v___x_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_2757_, v___y_2758_, v___y_2759_);
return v___x_2765_;
}
else
{
lean_object* v_val_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_constName_2757_);
v_val_2766_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2764_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_val_2766_);
lean_dec(v___x_2764_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 0);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_val_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object* v_constName_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; 
lean_inc(v_constName_2779_);
v___x_2783_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2795_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2795_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2795_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v_levelParams_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v_levelParams_2788_ = lean_ctor_get(v_a_2784_, 1);
lean_inc(v_levelParams_2788_);
lean_dec(v_a_2784_);
v___x_2789_ = lean_box(0);
v___x_2790_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(v_levelParams_2788_, v___x_2789_);
v___x_2791_ = l_Lean_mkConst(v_constName_2779_, v___x_2790_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2791_);
v___x_2793_ = v___x_2786_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_constName_2779_);
v_a_2796_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2783_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2783_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object* v_constName_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_constName_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object* v_stx_2809_, lean_object* v_n_2810_, lean_object* v_expectedType_x3f_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_n_2810_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = lean_box(0);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v_stx_2809_);
v___x_2819_ = l_Lean_LocalContext_empty;
v___x_2820_ = 0;
v___x_2821_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2821_, 0, v___x_2818_);
lean_ctor_set(v___x_2821_, 1, v___x_2819_);
lean_ctor_set(v___x_2821_, 2, v_expectedType_x3f_2811_);
lean_ctor_set(v___x_2821_, 3, v_a_2816_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*4, v___x_2820_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*4 + 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v___x_2822_, v___y_2812_, v___y_2813_);
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_expectedType_x3f_2811_);
lean_dec(v_stx_2809_);
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2815_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object* v_stx_2832_, lean_object* v_n_2833_, lean_object* v_expectedType_x3f_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_stx_2832_, v_n_2833_, v_expectedType_x3f_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
return v_res_2838_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2));
v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object* v_attrName_2845_, lean_object* v_extraKinds_2846_, uint8_t v_builtin_2847_, lean_object* v_stx_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v_env_2853_; lean_object* v___x_2854_; 
v___x_2852_ = lean_st_ref_get(v_a_2850_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
v___x_2854_ = l_Lean_Attribute_Builtin_getIdent(v_stx_2848_, v_a_2849_, v_a_2850_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2932_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2932_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2932_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___y_2861_; lean_object* v___y_2862_; 
v___x_2859_ = l_Lean_Syntax_getId(v_a_2855_);
if (v_builtin_2847_ == 0)
{
goto v___jp_2909_;
}
else
{
uint8_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = 0;
lean_inc(v___x_2859_);
lean_inc_ref(v_env_2853_);
v___x_2931_ = l_Lean_Environment_find_x3f(v_env_2853_, v___x_2859_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
goto v___jp_2909_;
}
else
{
lean_dec_ref_known(v___x_2931_, 1);
lean_dec_ref(v_env_2853_);
lean_dec(v_attrName_2845_);
v___y_2861_ = v_a_2849_;
v___y_2862_ = v_a_2850_;
goto v___jp_2860_;
}
}
v___jp_2860_:
{
lean_object* v___x_2863_; lean_object* v_env_2864_; uint8_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2863_ = lean_st_ref_get(v___y_2862_);
v_env_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_ref(v_env_2864_);
lean_dec(v___x_2863_);
v___x_2865_ = 1;
lean_inc(v___x_2859_);
v___x_2866_ = l_Lean_Environment_contains(v_env_2864_, v___x_2859_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2868_; 
lean_dec(v_a_2855_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2859_);
v___x_2868_ = v___x_2857_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2859_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
else
{
uint8_t v___x_2870_; lean_object* v___x_2871_; 
lean_del_object(v___x_2857_);
v___x_2870_ = 0;
lean_inc(v___x_2859_);
v___x_2871_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v___x_2859_, v___x_2870_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2871_, 0);
lean_dec(v_unused_2900_);
v___x_2873_ = v___x_2871_;
v_isShared_2874_ = v_isSharedCheck_2899_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v___x_2871_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2899_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v_infoState_2876_; uint8_t v_enabled_2877_; 
v___x_2875_ = lean_st_ref_get(v___y_2862_);
v_infoState_2876_ = lean_ctor_get(v___x_2875_, 7);
lean_inc_ref(v_infoState_2876_);
lean_dec(v___x_2875_);
v_enabled_2877_ = lean_ctor_get_uint8(v_infoState_2876_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2876_);
if (v_enabled_2877_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_a_2855_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2859_);
v___x_2879_ = v___x_2873_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2859_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_del_object(v___x_2873_);
v___x_2881_ = lean_box(0);
lean_inc(v___x_2859_);
v___x_2882_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_a_2855_, v___x_2859_, v___x_2881_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v___x_2882_, 0);
lean_dec(v_unused_2890_);
v___x_2884_ = v___x_2882_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v___x_2882_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2859_);
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2859_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v___x_2859_);
v_a_2891_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2882_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2882_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v___x_2859_);
lean_dec(v_a_2855_);
v_a_2901_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2871_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2871_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
v___jp_2909_:
{
uint8_t v___x_2910_; 
lean_inc(v___x_2859_);
v___x_2910_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2853_, v___x_2859_);
if (v___x_2910_ == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v___x_2859_, v_extraKinds_2846_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_del_object(v___x_2857_);
lean_dec(v_a_2855_);
v___x_2912_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1);
v___x_2913_ = l_Lean_MessageData_ofName(v_attrName_2845_);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_MessageData_ofName(v___x_2859_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_2920_, v_a_2849_, v_a_2850_);
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_dec(v_attrName_2845_);
v___y_2861_ = v_a_2849_;
v___y_2862_ = v_a_2850_;
goto v___jp_2860_;
}
}
else
{
lean_dec(v_attrName_2845_);
v___y_2861_ = v_a_2849_;
v___y_2862_ = v_a_2850_;
goto v___jp_2860_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v_env_2853_);
lean_dec(v_attrName_2845_);
v_a_2933_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2854_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2854_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object* v_attrName_2941_, lean_object* v_extraKinds_2942_, lean_object* v_builtin_2943_, lean_object* v_stx_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
uint8_t v_builtin_boxed_2948_; lean_object* v_res_2949_; 
v_builtin_boxed_2948_ = lean_unbox(v_builtin_2943_);
v_res_2949_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(v_attrName_2941_, v_extraKinds_2942_, v_builtin_boxed_2948_, v_stx_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_extraKinds_2942_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object* v_00_u03b2_2950_, lean_object* v_m_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2951_, v_a_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2954_, lean_object* v_m_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(v_00_u03b2_2954_, v_m_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_m_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object* v_t_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2958_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object* v_t_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(v_t_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2968_, lean_object* v_x_2969_, lean_object* v_x_2970_){
_start:
{
uint8_t v___x_2971_; 
v___x_2971_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2969_, v_x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
uint8_t v_res_2975_; lean_object* v_r_2976_; 
v_res_2975_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(v_00_u03b2_2972_, v_x_2973_, v_x_2974_);
lean_dec_ref(v_x_2974_);
lean_dec_ref(v_x_2973_);
v_r_2976_ = lean_box(v_res_2975_);
return v_r_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2977_, lean_object* v_a_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2978_, v_x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2981_, lean_object* v_a_2982_, lean_object* v_x_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(v_00_u03b2_2981_, v_a_2982_, v_x_2983_);
lean_dec(v_x_2983_);
lean_dec(v_a_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2985_, lean_object* v_x_2986_, size_t v_x_2987_, lean_object* v_x_2988_){
_start:
{
uint8_t v___x_2989_; 
v___x_2989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2986_, v_x_2987_, v_x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
size_t v_x_6112__boxed_2994_; uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_x_6112__boxed_2994_ = lean_unbox_usize(v_x_2992_);
lean_dec(v_x_2992_);
v_res_2995_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2990_, v_x_2991_, v_x_6112__boxed_2994_, v_x_2993_);
lean_dec_ref(v_x_2993_);
lean_dec_ref(v_x_2991_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_2997_, lean_object* v_keys_2998_, lean_object* v_vals_2999_, lean_object* v_heq_3000_, lean_object* v_i_3001_, lean_object* v_k_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2998_, v_i_3001_, v_k_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_keys_3005_, lean_object* v_vals_3006_, lean_object* v_heq_3007_, lean_object* v_i_3008_, lean_object* v_k_3009_){
_start:
{
uint8_t v_res_3010_; lean_object* v_r_3011_; 
v_res_3010_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_3004_, v_keys_3005_, v_vals_3006_, v_heq_3007_, v_i_3008_, v_k_3009_);
lean_dec_ref(v_k_3009_);
lean_dec_ref(v_vals_3006_);
lean_dec_ref(v_keys_3005_);
v_r_3011_ = lean_box(v_res_3010_);
return v_r_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(uint8_t v_builtin_3012_, lean_object* v_declName_3013_, lean_object* v_key_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_builtin_3020_, lean_object* v_declName_3021_, lean_object* v_key_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
uint8_t v_builtin_boxed_3026_; lean_object* v_res_3027_; 
v_builtin_boxed_3026_ = lean_unbox(v_builtin_3020_);
v_res_3027_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(v_builtin_boxed_3026_, v_declName_3021_, v_key_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v_key_3022_);
lean_dec(v_declName_3021_);
return v_res_3027_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_box(0);
v___x_3040_ = l_Lean_Fmt_headerKind;
v___x_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
return v___x_3041_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3043_ = l_Lean_Fmt_cmdsKind;
v___x_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v___x_3042_);
return v___x_3044_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3046_ = l_Lean_Fmt_moduleKind;
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3049_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3050_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed), 7, 2);
lean_closure_set(v___x_3050_, 0, v___x_3049_);
lean_closure_set(v___x_3050_, 1, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___f_3051_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3052_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3053_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3054_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3055_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3056_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3055_);
lean_ctor_set(v___x_3057_, 2, v___x_3054_);
lean_ctor_set(v___x_3057_, 3, v___x_3053_);
lean_ctor_set(v___x_3057_, 4, v___x_3052_);
lean_ctor_set(v___x_3057_, 5, v___f_3051_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3066_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3064_, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object* v_constName_3074_, lean_object* v_env_3075_, lean_object* v_opts_3076_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
v___x_3078_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3075_, v_opts_3076_, v___x_3077_, v_constName_3074_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object* v_constName_3079_, lean_object* v_env_3080_, lean_object* v_opts_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(v_constName_3079_, v_env_3080_, v_opts_3081_);
lean_dec_ref(v_opts_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object* v_constName_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_env_3086_; lean_object* v_opts_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_env_3086_ = lean_ctor_get(v_a_3084_, 0);
v_opts_3087_ = lean_ctor_get(v_a_3084_, 1);
v___x_3088_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
lean_inc_ref(v_env_3086_);
v___x_3089_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3086_, v_opts_3087_, v___x_3088_, v_constName_3083_);
v___x_3090_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object* v_constName_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_constName_3091_, v_a_3092_);
lean_dec_ref(v_a_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_));
v___x_3099_ = lean_st_mk_ref(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object* v_f_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3105_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3106_ = lean_st_ref_take(v___x_3105_);
v___x_3107_ = lean_array_push(v___x_3106_, v_f_3103_);
v___x_3108_ = lean_st_ref_put(v___x_3105_, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object* v_f_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Fmt_addBuiltinStickyTermFn(v_f_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3113_){
_start:
{
lean_object* v_fst_3114_; 
v_fst_3114_ = lean_ctor_get(v_x_3113_, 0);
lean_inc(v_fst_3114_);
return v_fst_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3115_);
lean_dec_ref(v_x_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_box(0);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3119_);
lean_dec_ref(v_x_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3121_, lean_object* v_s_3122_){
_start:
{
lean_object* v_fst_3123_; lean_object* v___x_3124_; 
v_fst_3123_ = lean_ctor_get(v_s_3122_, 0);
lean_inc_n(v_fst_3123_, 3);
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v_fst_3123_);
lean_ctor_set(v___x_3124_, 1, v_fst_3123_);
lean_ctor_set(v___x_3124_, 2, v_fst_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3125_, lean_object* v_s_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3125_, v_s_3126_);
lean_dec_ref(v_s_3126_);
lean_dec_ref(v_x_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v_fst_3130_; lean_object* v_snd_3131_; lean_object* v_fst_3132_; lean_object* v_snd_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3142_; 
v_fst_3130_ = lean_ctor_get(v_x_3128_, 0);
lean_inc(v_fst_3130_);
v_snd_3131_ = lean_ctor_get(v_x_3128_, 1);
lean_inc(v_snd_3131_);
lean_dec_ref(v_x_3128_);
v_fst_3132_ = lean_ctor_get(v_x_3129_, 0);
v_snd_3133_ = lean_ctor_get(v_x_3129_, 1);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_x_3129_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3135_ = v_x_3129_;
v_isShared_3136_ = v_isSharedCheck_3142_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_snd_3133_);
lean_inc(v_fst_3132_);
lean_dec(v_x_3129_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3142_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3137_ = lean_array_push(v_fst_3130_, v_fst_3132_);
v___x_3138_ = lean_array_push(v_snd_3131_, v_snd_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 1, v___x_3138_);
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3140_ = v___x_3135_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3143_, lean_object* v___x_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3146_ = lean_st_ref_get(v___x_3143_);
v___x_3147_ = lean_mk_empty_array_with_capacity(v___x_3144_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3150_, v___x_3151_);
lean_dec(v___x_3151_);
lean_dec(v___x_3150_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(lean_object* v_as_3154_, size_t v_i_3155_, size_t v_stop_3156_, lean_object* v_b_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_usize_dec_eq(v_i_3155_, v_stop_3156_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_array_uget_borrowed(v_as_3154_, v_i_3155_);
lean_inc(v___x_3161_);
v___x_3162_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v___x_3161_, v___y_3158_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = lean_array_push(v_b_3157_, v_a_3163_);
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_add(v_i_3155_, v___x_3165_);
v_i_3155_ = v___x_3166_;
v_b_3157_ = v___x_3164_;
goto _start;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v_b_3157_);
v_a_3168_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3162_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3162_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3157_);
return v___x_3176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_3177_, lean_object* v_i_3178_, lean_object* v_stop_3179_, lean_object* v_b_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
size_t v_i_boxed_3183_; size_t v_stop_boxed_3184_; lean_object* v_res_3185_; 
v_i_boxed_3183_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_stop_boxed_3184_ = lean_unbox_usize(v_stop_3179_);
lean_dec(v_stop_3179_);
v_res_3185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v_as_3177_, v_i_boxed_3183_, v_stop_boxed_3184_, v_b_3180_, v___y_3181_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_as_3177_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(lean_object* v_as_3186_, size_t v_i_3187_, size_t v_stop_3188_, lean_object* v_b_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_a_3193_; lean_object* v___y_3198_; uint8_t v___x_3200_; 
v___x_3200_ = lean_usize_dec_eq(v_i_3187_, v_stop_3188_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_array_uget_borrowed(v_as_3186_, v_i_3187_);
v___x_3203_ = lean_array_get_size(v___x_3202_);
v___x_3204_ = lean_nat_dec_lt(v___x_3201_, v___x_3203_);
if (v___x_3204_ == 0)
{
v_a_3193_ = v_b_3189_;
goto v___jp_3192_;
}
else
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_nat_dec_le(v___x_3203_, v___x_3203_);
if (v___x_3205_ == 0)
{
if (v___x_3204_ == 0)
{
v_a_3193_ = v_b_3189_;
goto v___jp_3192_;
}
else
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((size_t)0ULL);
v___x_3207_ = lean_usize_of_nat(v___x_3203_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v___x_3202_, v___x_3206_, v___x_3207_, v_b_3189_, v___y_3190_);
v___y_3198_ = v___x_3208_;
goto v___jp_3197_;
}
}
else
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = lean_usize_of_nat(v___x_3203_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v___x_3202_, v___x_3209_, v___x_3210_, v_b_3189_, v___y_3190_);
v___y_3198_ = v___x_3211_;
goto v___jp_3197_;
}
}
}
else
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_b_3189_);
return v___x_3212_;
}
v___jp_3192_:
{
size_t v___x_3194_; size_t v___x_3195_; 
v___x_3194_ = ((size_t)1ULL);
v___x_3195_ = lean_usize_add(v_i_3187_, v___x_3194_);
v_i_3187_ = v___x_3195_;
v_b_3189_ = v_a_3193_;
goto _start;
}
v___jp_3197_:
{
if (lean_obj_tag(v___y_3198_) == 0)
{
lean_object* v_a_3199_; 
v_a_3199_ = lean_ctor_get(v___y_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___y_3198_, 1);
v_a_3193_ = v_a_3199_;
goto v___jp_3192_;
}
else
{
return v___y_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_3213_, lean_object* v_i_3214_, lean_object* v_stop_3215_, lean_object* v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
size_t v_i_boxed_3219_; size_t v_stop_boxed_3220_; lean_object* v_res_3221_; 
v_i_boxed_3219_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_stop_boxed_3220_ = lean_unbox_usize(v_stop_3215_);
lean_dec(v_stop_3215_);
v_res_3221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3213_, v_i_boxed_3219_, v_stop_boxed_3220_, v_b_3216_, v___y_3217_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v_as_3213_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v_as_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_a_3228_; lean_object* v___y_3233_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3243_ = lean_st_ref_get(v___x_3223_);
v___x_3244_ = lean_array_get_size(v_as_3224_);
v___x_3245_ = lean_nat_dec_lt(v___x_3222_, v___x_3244_);
if (v___x_3245_ == 0)
{
v_a_3228_ = v___x_3243_;
goto v___jp_3227_;
}
else
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_nat_dec_le(v___x_3244_, v___x_3244_);
if (v___x_3246_ == 0)
{
if (v___x_3245_ == 0)
{
v_a_3228_ = v___x_3243_;
goto v___jp_3227_;
}
else
{
size_t v___x_3247_; size_t v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = ((size_t)0ULL);
v___x_3248_ = lean_usize_of_nat(v___x_3244_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3224_, v___x_3247_, v___x_3248_, v___x_3243_, v___y_3225_);
v___y_3233_ = v___x_3249_;
goto v___jp_3232_;
}
}
else
{
size_t v___x_3250_; size_t v___x_3251_; lean_object* v___x_3252_; 
v___x_3250_ = ((size_t)0ULL);
v___x_3251_ = lean_usize_of_nat(v___x_3244_);
v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3224_, v___x_3250_, v___x_3251_, v___x_3243_, v___y_3225_);
v___y_3233_ = v___x_3252_;
goto v___jp_3232_;
}
}
v___jp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_mk_empty_array_with_capacity(v___x_3222_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v_a_3228_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
v___jp_3232_:
{
if (lean_obj_tag(v___y_3233_) == 0)
{
lean_object* v_a_3234_; 
v_a_3234_ = lean_ctor_get(v___y_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___y_3233_, 1);
v_a_3228_ = v_a_3234_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
v_a_3235_ = lean_ctor_get(v___y_3233_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___y_3233_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___y_3233_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___y_3233_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v_as_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3253_, v___x_3254_, v_as_3255_, v___y_3256_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v_as_3255_);
lean_dec(v___x_3254_);
lean_dec(v___x_3253_);
return v_res_3258_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; 
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_3269_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_3269_, 0, v___x_3268_);
lean_closure_set(v___f_3269_, 1, v___x_3267_);
return v___f_3269_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___f_3272_; 
v___x_3270_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3271_ = lean_unsigned_to_nat(0u);
v___f_3272_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_3272_, 0, v___x_3271_);
lean_closure_set(v___f_3272_, 1, v___x_3270_);
return v___f_3272_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___f_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3273_ = lean_box(0);
v___x_3274_ = lean_box(2);
v___f_3275_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3276_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3277_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3278_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___f_3279_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3281_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___f_3279_);
lean_ctor_set(v___x_3281_, 2, v___f_3278_);
lean_ctor_set(v___x_3281_, 3, v___f_3277_);
lean_ctor_set(v___x_3281_, 4, v___f_3276_);
lean_ctor_set(v___x_3281_, 5, v___f_3275_);
lean_ctor_set(v___x_3281_, 6, v___x_3274_);
lean_ctor_set(v___x_3281_, 7, v___x_3273_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___f_3282_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3283_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___f_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3287_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_a_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_name_3290_, lean_object* v_decl_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3295_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3296_ = l_Lean_MessageData_ofName(v_name_3290_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3299_, v___y_3292_, v___y_3293_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_name_3301_, lean_object* v_decl_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_name_3301_, v_decl_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_decl_3302_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3308_, lean_object* v___x_3309_, lean_object* v___x_3310_, lean_object* v___x_3311_, lean_object* v_name_3312_, lean_object* v_decl_3313_, lean_object* v_stx_3314_, uint8_t v_kind_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3314_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_dec_ref_known(v___x_3381_, 1);
if (v_builtin_3308_ == 0)
{
lean_object* v___x_3382_; 
lean_inc(v_decl_3313_);
lean_inc(v_name_3312_);
v___x_3382_ = l_Lean_ensureAttrDeclIsMeta(v_name_3312_, v_decl_3313_, v_kind_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_dec_ref_known(v___x_3382_, 1);
goto v___jp_3377_;
}
else
{
lean_dec(v_decl_3313_);
lean_dec(v_name_3312_);
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v___x_3309_);
return v___x_3382_;
}
}
else
{
goto v___jp_3377_;
}
}
else
{
lean_dec(v_decl_3313_);
lean_dec(v_name_3312_);
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v___x_3309_);
return v___x_3381_;
}
v___jp_3319_:
{
if (v_builtin_3308_ == 0)
{
lean_object* v___x_3322_; lean_object* v_env_3323_; lean_object* v___x_3324_; lean_object* v_toCold_3325_; lean_object* v_env_3326_; lean_object* v_ref_3327_; lean_object* v_options_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
v___x_3322_ = lean_st_ref_get(v___y_3321_);
v_env_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc_ref(v_env_3323_);
lean_dec(v___x_3322_);
v___x_3324_ = lean_st_ref_get(v___y_3321_);
v_toCold_3325_ = lean_ctor_get(v___y_3320_, 0);
v_env_3326_ = lean_ctor_get(v___x_3324_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3324_);
v_ref_3327_ = lean_ctor_get(v___y_3320_, 2);
v_options_3328_ = lean_ctor_get(v_toCold_3325_, 2);
lean_inc_ref(v_options_3328_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_env_3326_);
lean_ctor_set(v___x_3329_, 1, v_options_3328_);
lean_inc(v_decl_3313_);
v___x_3330_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_decl_3313_, v___x_3329_);
lean_dec_ref_known(v___x_3329_, 2);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v_toEnvExtension_3333_; lean_object* v_asyncMode_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3333_ = lean_ctor_get(v___x_3332_, 0);
v_asyncMode_3334_ = lean_ctor_get(v_toEnvExtension_3333_, 2);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_decl_3313_);
lean_ctor_set(v___x_3335_, 1, v_a_3331_);
v___x_3336_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3332_, v_env_3323_, v___x_3335_, v_asyncMode_3334_, v___x_3309_);
v___x_3337_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3336_, v___y_3321_);
return v___x_3337_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v_env_3323_);
lean_dec(v_decl_3313_);
lean_dec(v___x_3309_);
v_a_3338_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3340_ = v___x_3330_;
v_isShared_3341_ = v_isSharedCheck_3349_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3330_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3349_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3342_ = lean_io_error_to_string(v_a_3338_);
v___x_3343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
v___x_3344_ = l_Lean_MessageData_ofFormat(v___x_3343_);
lean_inc(v_ref_3327_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3327_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3345_);
v___x_3347_ = v___x_3340_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v___x_3309_);
v___x_3350_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3351_ = l_Lean_Name_mkStr3(v___x_3310_, v___x_3311_, v___x_3350_);
v___x_3352_ = lean_box(0);
v___x_3353_ = l_Lean_mkConst(v___x_3351_, v___x_3352_);
lean_inc(v_decl_3313_);
v___x_3354_ = l_Lean_mkConst(v_decl_3313_, v___x_3352_);
v___x_3355_ = l_Lean_Expr_app___override(v___x_3353_, v___x_3354_);
v___x_3356_ = l_Lean_declareBuiltin(v_decl_3313_, v___x_3355_, v___y_3320_, v___y_3321_);
return v___x_3356_;
}
}
v___jp_3357_:
{
lean_object* v___x_3360_; 
lean_inc(v_decl_3313_);
v___x_3360_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_3313_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = l_Lean_ConstantInfo_type(v_a_3361_);
lean_dec(v_a_3361_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0));
lean_inc_ref(v___x_3311_);
lean_inc_ref(v___x_3310_);
v___x_3364_ = l_Lean_Name_mkStr3(v___x_3310_, v___x_3311_, v___x_3363_);
v___x_3365_ = l_Lean_Expr_isConstOf(v___x_3362_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v___x_3309_);
v___x_3366_ = lean_box(0);
v___x_3367_ = l_Lean_mkConst(v___x_3364_, v___x_3366_);
v___x_3368_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_name_3312_, v_decl_3313_, v___x_3362_, v___x_3367_, v___y_3358_, v___y_3359_);
return v___x_3368_;
}
else
{
lean_dec(v___x_3364_);
lean_dec_ref(v___x_3362_);
lean_dec(v_name_3312_);
v___y_3320_ = v___y_3358_;
v___y_3321_ = v___y_3359_;
goto v___jp_3319_;
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v_decl_3313_);
lean_dec(v_name_3312_);
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v___x_3309_);
v_a_3369_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3360_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3360_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
v___jp_3377_:
{
uint8_t v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = 0;
v___x_3379_ = l_Lean_instBEqAttributeKind_beq(v_kind_3315_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec(v_decl_3313_);
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___x_3310_);
lean_dec(v___x_3309_);
v___x_3380_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_3312_, v_kind_3315_, v___y_3316_, v___y_3317_);
return v___x_3380_;
}
else
{
v___y_3358_ = v___y_3316_;
v___y_3359_ = v___y_3317_;
goto v___jp_3357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3383_, lean_object* v___x_3384_, lean_object* v___x_3385_, lean_object* v___x_3386_, lean_object* v_name_3387_, lean_object* v_decl_3388_, lean_object* v_stx_3389_, lean_object* v_kind_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_builtin_boxed_3394_; uint8_t v_kind_boxed_3395_; lean_object* v_res_3396_; 
v_builtin_boxed_3394_ = lean_unbox(v_builtin_3383_);
v_kind_boxed_3395_ = lean_unbox(v_kind_3390_);
v_res_3396_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3394_, v___x_3384_, v___x_3385_, v___x_3386_, v_name_3387_, v_decl_3388_, v_stx_3389_, v_kind_boxed_3395_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3411_, lean_object* v_name_3412_){
_start:
{
lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___f_3419_; lean_object* v___x_3420_; lean_object* v___y_3422_; 
lean_inc_n(v_name_3412_, 2);
v___f_3414_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3414_, 0, v_name_3412_);
v___x_3415_ = lean_box(0);
v___x_3416_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0));
v___x_3417_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1));
v___x_3418_ = lean_box(v_builtin_3411_);
v___f_3419_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_3419_, 0, v___x_3418_);
lean_closure_set(v___f_3419_, 1, v___x_3415_);
lean_closure_set(v___f_3419_, 2, v___x_3416_);
lean_closure_set(v___f_3419_, 3, v___x_3417_);
lean_closure_set(v___f_3419_, 4, v_name_3412_);
v___x_3420_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
if (v_builtin_3411_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___y_3422_ = v___x_3429_;
goto v___jp_3421_;
}
else
{
lean_object* v___x_3430_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___y_3422_ = v___x_3430_;
goto v___jp_3421_;
}
v___jp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
lean_inc_ref(v___y_3422_);
v___x_3424_ = lean_string_append(v___y_3422_, v___x_3423_);
v___x_3425_ = 1;
v___x_3426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3426_, 0, v___x_3420_);
lean_ctor_set(v___x_3426_, 1, v_name_3412_);
lean_ctor_set(v___x_3426_, 2, v___x_3424_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*3, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___f_3419_);
lean_ctor_set(v___x_3427_, 2, v___f_3414_);
v___x_3428_ = l_Lean_registerBuiltinAttribute(v___x_3427_);
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3431_, lean_object* v_name_3432_, lean_object* v___y_3433_){
_start:
{
uint8_t v_builtin_boxed_3434_; lean_object* v_res_3435_; 
v_builtin_boxed_3434_ = lean_unbox(v_builtin_3431_);
v_res_3435_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3434_, v_name_3432_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = 1;
v___x_3444_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3445_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3443_, v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref_known(v___x_3445_, 1);
v___x_3446_ = 0;
v___x_3447_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3448_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3446_, v___x_3447_);
return v___x_3448_;
}
else
{
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
return v_res_3450_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object* v_t_3451_, lean_object* v_as_3452_, size_t v_i_3453_, size_t v_stop_3454_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_eq(v_i_3453_, v_stop_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_157__overap_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_157__overap_3456_ = lean_array_uget_borrowed(v_as_3452_, v_i_3453_);
lean_inc(v___x_157__overap_3456_);
lean_inc(v_t_3451_);
v___x_3457_ = lean_apply_1(v___x_157__overap_3456_, v_t_3451_);
v___x_3458_ = lean_unbox(v___x_3457_);
if (v___x_3458_ == 0)
{
size_t v___x_3459_; size_t v___x_3460_; 
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3453_, v___x_3459_);
v_i_3453_ = v___x_3460_;
goto _start;
}
else
{
uint8_t v___x_3462_; 
lean_dec(v_t_3451_);
v___x_3462_ = lean_unbox(v___x_3457_);
return v___x_3462_;
}
}
else
{
uint8_t v___x_3463_; 
lean_dec(v_t_3451_);
v___x_3463_ = 0;
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object* v_t_3464_, lean_object* v_as_3465_, lean_object* v_i_3466_, lean_object* v_stop_3467_){
_start:
{
size_t v_i_boxed_3468_; size_t v_stop_boxed_3469_; uint8_t v_res_3470_; lean_object* v_r_3471_; 
v_i_boxed_3468_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_stop_boxed_3469_ = lean_unbox_usize(v_stop_3467_);
lean_dec(v_stop_3467_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3464_, v_as_3465_, v_i_boxed_3468_, v_stop_boxed_3469_);
lean_dec_ref(v_as_3465_);
v_r_3471_ = lean_box(v_res_3470_);
return v_r_3471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object* v_env_3472_, lean_object* v_t_3473_){
_start:
{
lean_object* v___x_3474_; lean_object* v_toEnvExtension_3475_; lean_object* v_asyncMode_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_snd_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3474_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3475_ = lean_ctor_get(v___x_3474_, 0);
v_asyncMode_3476_ = lean_ctor_get(v_toEnvExtension_3475_, 2);
v___x_3477_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_3478_ = lean_box(0);
v___x_3479_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3477_, v___x_3474_, v_env_3472_, v_asyncMode_3476_, v___x_3478_);
v_snd_3480_ = lean_ctor_get(v___x_3479_, 1);
lean_inc(v_snd_3480_);
lean_dec(v___x_3479_);
v___x_3481_ = lean_unsigned_to_nat(0u);
v___x_3482_ = lean_array_get_size(v_snd_3480_);
v___x_3483_ = lean_nat_dec_lt(v___x_3481_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_dec(v_snd_3480_);
lean_dec(v_t_3473_);
return v___x_3483_;
}
else
{
if (v___x_3483_ == 0)
{
lean_dec(v_snd_3480_);
lean_dec(v_t_3473_);
return v___x_3483_;
}
else
{
size_t v___x_3484_; size_t v___x_3485_; uint8_t v___x_3486_; 
v___x_3484_ = ((size_t)0ULL);
v___x_3485_ = lean_usize_of_nat(v___x_3482_);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3473_, v_snd_3480_, v___x_3484_, v___x_3485_);
lean_dec(v_snd_3480_);
return v___x_3486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object* v_env_3487_, lean_object* v_t_3488_){
_start:
{
uint8_t v_res_3489_; lean_object* v_r_3490_; 
v_res_3489_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_3487_, v_t_3488_);
v_r_3490_ = lean_box(v_res_3489_);
return v_r_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(uint8_t v_x_3491_){
_start:
{
switch(v_x_3491_)
{
case 0:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_unsigned_to_nat(0u);
return v___x_3492_;
}
case 1:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_unsigned_to_nat(1u);
return v___x_3493_;
}
default: 
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_unsigned_to_nat(2u);
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___boxed(lean_object* v_x_3495_){
_start:
{
uint8_t v_x_boxed_3496_; lean_object* v_res_3497_; 
v_x_boxed_3496_ = lean_unbox(v_x_3495_);
v_res_3497_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_x_boxed_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object* v_k_3498_){
_start:
{
lean_inc(v_k_3498_);
return v_k_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object* v_k_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(v_k_3499_);
lean_dec(v_k_3499_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object* v_motive_3501_, lean_object* v_ctorIdx_3502_, uint8_t v_t_3503_, lean_object* v_h_3504_, lean_object* v_k_3505_){
_start:
{
lean_inc(v_k_3505_);
return v_k_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object* v_motive_3506_, lean_object* v_ctorIdx_3507_, lean_object* v_t_3508_, lean_object* v_h_3509_, lean_object* v_k_3510_){
_start:
{
uint8_t v_t_boxed_3511_; lean_object* v_res_3512_; 
v_t_boxed_3511_ = lean_unbox(v_t_3508_);
v_res_3512_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim(v_motive_3506_, v_ctorIdx_3507_, v_t_boxed_3511_, v_h_3509_, v_k_3510_);
lean_dec(v_k_3510_);
lean_dec(v_ctorIdx_3507_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object* v_left_3513_){
_start:
{
lean_inc(v_left_3513_);
return v_left_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object* v_left_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(v_left_3514_);
lean_dec(v_left_3514_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object* v_motive_3516_, uint8_t v_t_3517_, lean_object* v_h_3518_, lean_object* v_left_3519_){
_start:
{
lean_inc(v_left_3519_);
return v_left_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object* v_motive_3520_, lean_object* v_t_3521_, lean_object* v_h_3522_, lean_object* v_left_3523_){
_start:
{
uint8_t v_t_boxed_3524_; lean_object* v_res_3525_; 
v_t_boxed_3524_ = lean_unbox(v_t_3521_);
v_res_3525_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim(v_motive_3520_, v_t_boxed_3524_, v_h_3522_, v_left_3523_);
lean_dec(v_left_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object* v_right_3526_){
_start:
{
lean_inc(v_right_3526_);
return v_right_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object* v_right_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(v_right_3527_);
lean_dec(v_right_3527_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object* v_motive_3529_, uint8_t v_t_3530_, lean_object* v_h_3531_, lean_object* v_right_3532_){
_start:
{
lean_inc(v_right_3532_);
return v_right_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object* v_motive_3533_, lean_object* v_t_3534_, lean_object* v_h_3535_, lean_object* v_right_3536_){
_start:
{
uint8_t v_t_boxed_3537_; lean_object* v_res_3538_; 
v_t_boxed_3537_ = lean_unbox(v_t_3534_);
v_res_3538_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim(v_motive_3533_, v_t_boxed_3537_, v_h_3535_, v_right_3536_);
lean_dec(v_right_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object* v_middle_3539_){
_start:
{
lean_inc(v_middle_3539_);
return v_middle_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object* v_middle_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(v_middle_3540_);
lean_dec(v_middle_3540_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object* v_motive_3542_, uint8_t v_t_3543_, lean_object* v_h_3544_, lean_object* v_middle_3545_){
_start:
{
lean_inc(v_middle_3545_);
return v_middle_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object* v_motive_3546_, lean_object* v_t_3547_, lean_object* v_h_3548_, lean_object* v_middle_3549_){
_start:
{
uint8_t v_t_boxed_3550_; lean_object* v_res_3551_; 
v_t_boxed_3550_ = lean_unbox(v_t_3547_);
v_res_3551_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim(v_motive_3546_, v_t_boxed_3550_, v_h_3548_, v_middle_3549_);
lean_dec(v_middle_3549_);
return v_res_3551_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default(void){
_start:
{
uint8_t v___x_3552_; 
v___x_3552_ = 0;
return v___x_3552_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity(void){
_start:
{
uint8_t v___x_3553_; 
v___x_3553_ = 0;
return v___x_3553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t v_x_3554_, uint8_t v_y_3555_){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3556_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_x_3554_);
v___x_3557_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_y_3555_);
v___x_3558_ = lean_nat_dec_eq(v___x_3556_, v___x_3557_);
lean_dec(v___x_3557_);
lean_dec(v___x_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object* v_x_3559_, lean_object* v_y_3560_){
_start:
{
uint8_t v_x_21__boxed_3561_; uint8_t v_y_22__boxed_3562_; uint8_t v_res_3563_; lean_object* v_r_3564_; 
v_x_21__boxed_3561_ = lean_unbox(v_x_3559_);
v_y_22__boxed_3562_ = lean_unbox(v_y_3560_);
v_res_3563_ = l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(v_x_21__boxed_3561_, v_y_22__boxed_3562_);
v_r_3564_ = lean_box(v_res_3563_);
return v_r_3564_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v_prec_3573_; lean_object* v_lhsPrec_3574_; lean_object* v_rhsPrec_3575_; lean_object* v_prec_3576_; lean_object* v_lhsPrec_3577_; lean_object* v_rhsPrec_3578_; uint8_t v___x_3579_; 
v_prec_3573_ = lean_ctor_get(v_x_3571_, 0);
v_lhsPrec_3574_ = lean_ctor_get(v_x_3571_, 1);
v_rhsPrec_3575_ = lean_ctor_get(v_x_3571_, 2);
v_prec_3576_ = lean_ctor_get(v_x_3572_, 0);
v_lhsPrec_3577_ = lean_ctor_get(v_x_3572_, 1);
v_rhsPrec_3578_ = lean_ctor_get(v_x_3572_, 2);
v___x_3579_ = lean_nat_dec_eq(v_prec_3573_, v_prec_3576_);
if (v___x_3579_ == 0)
{
return v___x_3579_;
}
else
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_nat_dec_eq(v_lhsPrec_3574_, v_lhsPrec_3577_);
if (v___x_3580_ == 0)
{
return v___x_3580_;
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_nat_dec_eq(v_rhsPrec_3575_, v_rhsPrec_3578_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
uint8_t v_res_3584_; lean_object* v_r_3585_; 
v_res_3584_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_x_3582_, v_x_3583_);
lean_dec_ref(v_x_3583_);
lean_dec_ref(v_x_3582_);
v_r_3585_ = lean_box(v_res_3584_);
return v_r_3585_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = lean_box(0);
v___x_3589_ = lean_unsigned_to_nat(16u);
v___x_3590_ = lean_mk_array(v___x_3589_, v___x_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v___x_3591_);
return v___x_3593_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; lean_object* v___x_3597_; 
v___x_3594_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1);
v___x_3595_ = lean_box(0);
v___x_3596_ = 0;
v___x_3597_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3594_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*2, v___x_3596_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*2 + 1, v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default(void){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2);
return v___x_3598_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation(void){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Lean_Fmt_instInhabitedInfixOperation_default;
return v___x_3599_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
if (lean_obj_tag(v_x_3600_) == 0)
{
if (lean_obj_tag(v_x_3601_) == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = 1;
return v___x_3602_;
}
else
{
uint8_t v___x_3603_; 
v___x_3603_ = 0;
return v___x_3603_;
}
}
else
{
if (lean_obj_tag(v_x_3601_) == 0)
{
uint8_t v___x_3604_; 
v___x_3604_ = 0;
return v___x_3604_;
}
else
{
lean_object* v_val_3605_; lean_object* v_val_3606_; uint8_t v___x_3607_; 
v_val_3605_ = lean_ctor_get(v_x_3600_, 0);
v_val_3606_ = lean_ctor_get(v_x_3601_, 0);
v___x_3607_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_3605_, v_val_3606_);
return v___x_3607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
uint8_t v_res_3610_; lean_object* v_r_3611_; 
v_res_3610_ = l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_x_3608_, v_x_3609_);
lean_dec(v_x_3609_);
lean_dec(v_x_3608_);
v_r_3611_ = lean_box(v_res_3610_);
return v_r_3611_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
if (lean_obj_tag(v_x_3612_) == 0)
{
if (lean_obj_tag(v_x_3613_) == 0)
{
uint8_t v___x_3614_; 
v___x_3614_ = 1;
return v___x_3614_;
}
else
{
uint8_t v___x_3615_; 
v___x_3615_ = 0;
return v___x_3615_;
}
}
else
{
if (lean_obj_tag(v_x_3613_) == 0)
{
uint8_t v___x_3616_; 
v___x_3616_ = 0;
return v___x_3616_;
}
else
{
uint8_t v___x_3617_; 
v___x_3617_ = 1;
return v___x_3617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_x_3618_, lean_object* v_x_3619_){
_start:
{
uint8_t v_res_3620_; lean_object* v_r_3621_; 
v_res_3620_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v_x_3618_, v_x_3619_);
lean_dec(v_x_3619_);
lean_dec(v_x_3618_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_m_u2082_3625_, lean_object* v___x_3626_, lean_object* v___x_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___y_3633_; uint8_t v___x_3646_; 
v___x_3630_ = lean_box(0);
v___x_3631_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v___x_3646_ = lean_nat_dec_eq(v___x_3626_, v___x_3627_);
if (v___x_3646_ == 0)
{
uint8_t v___x_3647_; 
v___x_3647_ = 1;
v___y_3633_ = v___x_3647_;
goto v___jp_3632_;
}
else
{
uint8_t v___x_3648_; 
v___x_3648_ = 0;
v___y_3633_ = v___x_3648_;
goto v___jp_3632_;
}
v___jp_3632_:
{
if (lean_obj_tag(v_a_3628_) == 0)
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_a_3629_);
return v___x_3634_;
}
else
{
lean_object* v_key_3635_; lean_object* v_value_3636_; lean_object* v_tail_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
lean_dec_ref(v_a_3629_);
v_key_3635_ = lean_ctor_get(v_a_3628_, 0);
v_value_3636_ = lean_ctor_get(v_a_3628_, 1);
v_tail_3637_ = lean_ctor_get(v_a_3628_, 2);
v___x_3638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_u2082_3625_, v_key_3635_);
lean_inc(v_value_3636_);
v___x_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_value_3636_);
v___x_3640_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v___x_3638_, v___x_3639_);
lean_dec_ref_known(v___x_3639_, 1);
lean_dec(v___x_3638_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3641_ = lean_box(v___y_3633_);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3630_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
else
{
v_a_3628_ = v_tail_3637_;
v_a_3629_ = v___x_3631_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_m_u2082_3649_, lean_object* v___x_3650_, lean_object* v___x_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3649_, v___x_3650_, v___x_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3652_);
lean_dec(v___x_3651_);
lean_dec(v___x_3650_);
lean_dec_ref(v_m_u2082_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_m_u2082_3655_, lean_object* v___x_3656_, lean_object* v___x_3657_, lean_object* v_as_3658_, size_t v_sz_3659_, size_t v_i_3660_, lean_object* v_b_3661_){
_start:
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_usize_dec_lt(v_i_3660_, v_sz_3659_);
if (v___x_3662_ == 0)
{
return v_b_3661_;
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3664_; 
v_a_3663_ = lean_array_uget_borrowed(v_as_3658_, v_i_3660_);
v___x_3664_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3655_, v___x_3656_, v___x_3657_, v_a_3663_, v_b_3661_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
return v_a_3665_;
}
else
{
lean_object* v_a_3666_; size_t v___x_3667_; size_t v___x_3668_; 
v_a_3666_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3667_ = ((size_t)1ULL);
v___x_3668_ = lean_usize_add(v_i_3660_, v___x_3667_);
v_i_3660_ = v___x_3668_;
v_b_3661_ = v_a_3666_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_m_u2082_3670_, lean_object* v___x_3671_, lean_object* v___x_3672_, lean_object* v_as_3673_, lean_object* v_sz_3674_, lean_object* v_i_3675_, lean_object* v_b_3676_){
_start:
{
size_t v_sz_boxed_3677_; size_t v_i_boxed_3678_; lean_object* v_res_3679_; 
v_sz_boxed_3677_ = lean_unbox_usize(v_sz_3674_);
lean_dec(v_sz_3674_);
v_i_boxed_3678_ = lean_unbox_usize(v_i_3675_);
lean_dec(v_i_3675_);
v_res_3679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3670_, v___x_3671_, v___x_3672_, v_as_3673_, v_sz_boxed_3677_, v_i_boxed_3678_, v_b_3676_);
lean_dec_ref(v_as_3673_);
lean_dec(v___x_3672_);
lean_dec(v___x_3671_);
lean_dec_ref(v_m_u2082_3670_);
return v_res_3679_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object* v_m_u2081_3680_, lean_object* v_m_u2082_3681_){
_start:
{
lean_object* v_size_3682_; lean_object* v_buckets_3683_; lean_object* v_size_3684_; uint8_t v___x_3685_; 
v_size_3682_ = lean_ctor_get(v_m_u2081_3680_, 0);
v_buckets_3683_ = lean_ctor_get(v_m_u2081_3680_, 1);
v_size_3684_ = lean_ctor_get(v_m_u2082_3681_, 0);
v___x_3685_ = lean_nat_dec_eq(v_size_3682_, v_size_3684_);
if (v___x_3685_ == 0)
{
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; size_t v_sz_3687_; size_t v___x_3688_; lean_object* v___x_3689_; lean_object* v_fst_3690_; 
v___x_3686_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v_sz_3687_ = lean_array_size(v_buckets_3683_);
v___x_3688_ = ((size_t)0ULL);
v___x_3689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3681_, v_size_3682_, v_size_3684_, v_buckets_3683_, v_sz_3687_, v___x_3688_, v___x_3686_);
v_fst_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_fst_3690_);
lean_dec_ref(v___x_3689_);
if (lean_obj_tag(v_fst_3690_) == 0)
{
return v___x_3685_;
}
else
{
lean_object* v_val_3691_; uint8_t v___x_3692_; 
v_val_3691_ = lean_ctor_get(v_fst_3690_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_fst_3690_, 1);
v___x_3692_ = lean_unbox(v_val_3691_);
lean_dec(v_val_3691_);
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_m_u2081_3693_, lean_object* v_m_u2082_3694_){
_start:
{
uint8_t v_res_3695_; lean_object* v_r_3696_; 
v_res_3695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3693_, v_m_u2082_3694_);
lean_dec_ref(v_m_u2082_3694_);
lean_dec_ref(v_m_u2081_3693_);
v_r_3696_ = lean_box(v_res_3695_);
return v_r_3696_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object* v_m_u2081_3697_, lean_object* v_m_u2082_3698_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3697_, v_m_u2082_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object* v_m_u2081_3700_, lean_object* v_m_u2082_3701_){
_start:
{
uint8_t v_res_3702_; lean_object* v_r_3703_; 
v_res_3702_ = l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(v_m_u2081_3700_, v_m_u2082_3701_);
lean_dec_ref(v_m_u2082_3701_);
lean_dec_ref(v_m_u2081_3700_);
v_r_3703_ = lean_box(v_res_3702_);
return v_r_3703_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object* v_m_u2081_3704_, lean_object* v_m_u2082_3705_){
_start:
{
uint8_t v___x_3706_; 
v___x_3706_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3704_, v_m_u2082_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object* v_m_u2081_3707_, lean_object* v_m_u2082_3708_){
_start:
{
uint8_t v_res_3709_; lean_object* v_r_3710_; 
v_res_3709_ = l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(v_m_u2081_3707_, v_m_u2082_3708_);
lean_dec_ref(v_m_u2082_3708_);
lean_dec_ref(v_m_u2081_3707_);
v_r_3710_ = lean_box(v_res_3709_);
return v_r_3710_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object* v_m_u2081_3711_, lean_object* v_m_u2082_3712_){
_start:
{
uint8_t v___x_3713_; 
v___x_3713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3711_, v_m_u2082_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object* v_m_u2081_3714_, lean_object* v_m_u2082_3715_){
_start:
{
uint8_t v_res_3716_; lean_object* v_r_3717_; 
v_res_3716_ = l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(v_m_u2081_3714_, v_m_u2082_3715_);
lean_dec_ref(v_m_u2082_3715_);
lean_dec_ref(v_m_u2081_3714_);
v_r_3717_ = lean_box(v_res_3716_);
return v_r_3717_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object* v_x_3718_, lean_object* v_x_3719_){
_start:
{
uint8_t v_sparse_3720_; uint8_t v_separateFinalOperand_3721_; lean_object* v_precs_x3f_3722_; lean_object* v_extendedChainKinds_3723_; uint8_t v_sparse_3724_; uint8_t v_separateFinalOperand_3725_; lean_object* v_precs_x3f_3726_; lean_object* v_extendedChainKinds_3727_; 
v_sparse_3720_ = lean_ctor_get_uint8(v_x_3718_, sizeof(void*)*2);
v_separateFinalOperand_3721_ = lean_ctor_get_uint8(v_x_3718_, sizeof(void*)*2 + 1);
v_precs_x3f_3722_ = lean_ctor_get(v_x_3718_, 0);
v_extendedChainKinds_3723_ = lean_ctor_get(v_x_3718_, 1);
v_sparse_3724_ = lean_ctor_get_uint8(v_x_3719_, sizeof(void*)*2);
v_separateFinalOperand_3725_ = lean_ctor_get_uint8(v_x_3719_, sizeof(void*)*2 + 1);
v_precs_x3f_3726_ = lean_ctor_get(v_x_3719_, 0);
v_extendedChainKinds_3727_ = lean_ctor_get(v_x_3719_, 1);
if (v_sparse_3724_ == 0)
{
if (v_sparse_3720_ == 0)
{
goto v___jp_3731_;
}
else
{
return v_sparse_3724_;
}
}
else
{
if (v_sparse_3720_ == 0)
{
return v_sparse_3720_;
}
else
{
goto v___jp_3731_;
}
}
v___jp_3728_:
{
uint8_t v___x_3729_; 
v___x_3729_ = l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_precs_x3f_3722_, v_precs_x3f_3726_);
if (v___x_3729_ == 0)
{
return v___x_3729_;
}
else
{
uint8_t v___x_3730_; 
v___x_3730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_extendedChainKinds_3723_, v_extendedChainKinds_3727_);
return v___x_3730_;
}
}
v___jp_3731_:
{
if (v_separateFinalOperand_3725_ == 0)
{
if (v_separateFinalOperand_3721_ == 0)
{
goto v___jp_3728_;
}
else
{
return v_separateFinalOperand_3725_;
}
}
else
{
if (v_separateFinalOperand_3721_ == 0)
{
return v_separateFinalOperand_3721_;
}
else
{
goto v___jp_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object* v_x_3732_, lean_object* v_x_3733_){
_start:
{
uint8_t v_res_3734_; lean_object* v_r_3735_; 
v_res_3734_ = l_Lean_Fmt_instBEqInfixOperation_beq(v_x_3732_, v_x_3733_);
lean_dec_ref(v_x_3733_);
lean_dec_ref(v_x_3732_);
v_r_3735_ = lean_box(v_res_3734_);
return v_r_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3767_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3768_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3766_, v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2____boxed(lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3799_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3800_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3801_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3799_, v___x_3800_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2____boxed(lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx(lean_object* v_x_3804_){
_start:
{
if (lean_obj_tag(v_x_3804_) == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_unsigned_to_nat(0u);
return v___x_3805_;
}
else
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_unsigned_to_nat(1u);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___boxed(lean_object* v_x_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_Fmt_QuantifierBinders_ctorIdx(v_x_3807_);
lean_dec_ref(v_x_3807_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object* v_t_3809_, lean_object* v_k_3810_){
_start:
{
if (lean_obj_tag(v_t_3809_) == 0)
{
lean_object* v_group_3811_; lean_object* v___x_3812_; 
v_group_3811_ = lean_ctor_get(v_t_3809_, 0);
lean_inc_ref(v_group_3811_);
lean_dec_ref_known(v_t_3809_, 1);
v___x_3812_ = lean_apply_1(v_k_3810_, v_group_3811_);
return v___x_3812_;
}
else
{
lean_object* v_lhs_3813_; lean_object* v_rhs_3814_; lean_object* v___x_3815_; 
v_lhs_3813_ = lean_ctor_get(v_t_3809_, 0);
lean_inc(v_lhs_3813_);
v_rhs_3814_ = lean_ctor_get(v_t_3809_, 1);
lean_inc(v_rhs_3814_);
lean_dec_ref_known(v_t_3809_, 2);
v___x_3815_ = lean_apply_2(v_k_3810_, v_lhs_3813_, v_rhs_3814_);
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object* v_motive_3816_, lean_object* v_ctorIdx_3817_, lean_object* v_t_3818_, lean_object* v_h_3819_, lean_object* v_k_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3818_, v_k_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object* v_motive_3822_, lean_object* v_ctorIdx_3823_, lean_object* v_t_3824_, lean_object* v_h_3825_, lean_object* v_k_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_Fmt_QuantifierBinders_ctorElim(v_motive_3822_, v_ctorIdx_3823_, v_t_3824_, v_h_3825_, v_k_3826_);
lean_dec(v_ctorIdx_3823_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object* v_t_3828_, lean_object* v_binders_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3828_, v_binders_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object* v_motive_3831_, lean_object* v_t_3832_, lean_object* v_h_3833_, lean_object* v_binders_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3832_, v_binders_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object* v_t_3836_, lean_object* v_pred_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3836_, v_pred_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object* v_motive_3839_, lean_object* v_t_3840_, lean_object* v_h_3841_, lean_object* v_pred_3842_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3840_, v_pred_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3873_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3874_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3872_, v___x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2____boxed(lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
return v_res_3876_;
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
