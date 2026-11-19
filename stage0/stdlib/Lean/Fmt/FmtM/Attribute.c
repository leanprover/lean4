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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
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
v___x_279_ = l_ShareCommon_mkStateImpl(v___x_278_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_802_, lean_object* v_declHint_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_env_808_; uint8_t v___x_809_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_st_ref_get(v___y_804_);
v_env_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc_ref(v_env_808_);
lean_dec(v___x_807_);
v___x_809_ = l_Lean_Name_isAnonymous(v_declHint_803_);
if (v___x_809_ == 0)
{
uint8_t v_isExporting_810_; 
v_isExporting_810_ = lean_ctor_get_uint8(v_env_808_, sizeof(void*)*13);
if (v_isExporting_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v_env_808_);
lean_dec(v_declHint_803_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_msg_802_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
lean_inc_ref(v_env_808_);
v___x_812_ = l_Lean_Environment_setExporting(v_env_808_, v___x_809_);
lean_inc(v_declHint_803_);
lean_inc_ref(v___x_812_);
v___x_813_ = l_Lean_Environment_contains(v___x_812_, v_declHint_803_, v_isExporting_810_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
lean_dec_ref(v___x_812_);
lean_dec_ref(v_env_808_);
lean_dec(v_declHint_803_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_msg_802_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_c_820_; lean_object* v___x_821_; 
v___x_815_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_816_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_817_ = l_Lean_Options_empty;
lean_inc_ref(v___x_812_);
v___x_818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_818_, 0, v___x_812_);
lean_ctor_set(v___x_818_, 1, v___x_815_);
lean_ctor_set(v___x_818_, 2, v___x_816_);
lean_ctor_set(v___x_818_, 3, v___x_817_);
lean_inc(v_declHint_803_);
v___x_819_ = l_Lean_MessageData_ofConstName(v_declHint_803_, v___x_809_);
v_c_820_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_820_, 0, v___x_818_);
lean_ctor_set(v_c_820_, 1, v___x_819_);
v___x_821_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_812_, v_declHint_803_);
lean_dec_ref(v___x_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v_env_808_);
lean_dec(v_declHint_803_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_c_820_);
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_MessageData_note(v___x_825_);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v_msg_802_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_863_; 
v_val_829_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_863_ == 0)
{
v___x_831_ = v___x_821_;
v_isShared_832_ = v_isSharedCheck_863_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v___x_821_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_863_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v_moduleNames_834_; lean_object* v_mod_835_; uint8_t v___x_836_; 
v___x_833_ = l_Lean_Environment_header(v_env_808_);
lean_dec_ref(v_env_808_);
v_moduleNames_834_ = lean_ctor_get(v___x_833_, 4);
lean_inc_ref(v_moduleNames_834_);
lean_dec_ref(v___x_833_);
v_mod_835_ = lean_array_get(v___x_806_, v_moduleNames_834_, v_val_829_);
lean_dec(v_val_829_);
lean_dec_ref(v_moduleNames_834_);
v___x_836_ = l_Lean_isPrivateName(v_declHint_803_);
lean_dec(v_declHint_803_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_c_820_);
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_MessageData_ofName(v_mod_835_);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_MessageData_note(v___x_844_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v_msg_802_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_846_);
v___x_848_ = v___x_831_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_c_820_);
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_MessageData_ofName(v_mod_835_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_note(v___x_857_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v_msg_802_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_859_);
v___x_861_ = v___x_831_;
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
lean_object* v___x_864_; 
lean_dec_ref(v_env_808_);
lean_dec(v_declHint_803_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v_msg_802_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_865_, v_declHint_866_, v___y_867_);
lean_dec(v___y_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_870_, lean_object* v_declHint_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
v___x_875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_870_, v_declHint_871_, v___y_873_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_885_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = l_Lean_unknownIdentifierMessageTag;
v___x_881_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_886_, lean_object* v_declHint_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_886_, v_declHint_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_892_, lean_object* v_msg_893_, lean_object* v_declHint_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_900_; 
v___x_898_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_893_, v_declHint_894_, v___y_895_, v___y_896_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v___x_900_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_892_, v_a_899_, v___y_895_, v___y_896_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_901_, lean_object* v_msg_902_, lean_object* v_declHint_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_901_, v_msg_902_, v_declHint_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v_ref_901_);
return v_res_907_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_914_, lean_object* v_constName_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_919_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_920_ = 0;
lean_inc(v_constName_915_);
v___x_921_ = l_Lean_MessageData_ofConstName(v_constName_915_, v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_919_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_914_, v___x_924_, v_constName_915_, v___y_916_, v___y_917_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_926_, lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_926_, v_constName_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_ref_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_ref_936_; lean_object* v___x_937_; 
v_ref_936_ = lean_ctor_get(v___y_933_, 2);
v___x_937_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_936_, v_constName_932_, v___y_933_, v___y_934_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(lean_object* v_constName_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v_env_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
v___x_947_ = lean_st_ref_get(v___y_945_);
v_env_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_947_);
v___x_949_ = 0;
lean_inc(v_constName_943_);
v___x_950_ = l_Lean_Environment_find_x3f(v_env_948_, v_constName_943_, v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_943_, v___y_944_, v___y_945_);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_constName_943_);
v_val_952_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_950_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 0);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_constName_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_974_, uint8_t v_kind_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___y_985_; 
v___x_979_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_980_ = l_Lean_MessageData_ofName(v_name_974_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
switch(v_kind_975_)
{
case 0:
{
lean_object* v___x_992_; 
v___x_992_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___y_985_ = v___x_992_;
goto v___jp_984_;
}
case 1:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5));
v___y_985_ = v___x_993_;
goto v___jp_984_;
}
default: 
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_985_ = v___x_994_;
goto v___jp_984_;
}
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_inc_ref(v___y_985_);
v___x_986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_986_, 0, v___y_985_);
v___x_987_ = l_Lean_MessageData_ofFormat(v___x_986_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_983_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_990_, v___y_976_, v___y_977_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_995_, lean_object* v_kind_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v_kind_boxed_1000_; lean_object* v_res_1001_; 
v_kind_boxed_1000_ = lean_unbox(v_kind_996_);
v_res_1001_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_995_, v_kind_boxed_1000_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1001_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_1017_, lean_object* v_declName_1018_, lean_object* v_givenType_1019_, lean_object* v_expectedType_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1024_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_1025_ = l_Lean_MessageData_ofName(v_attrName_1017_);
lean_inc_ref(v___x_1025_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = 0;
v___x_1030_ = l_Lean_MessageData_ofConstName(v_declName_1018_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1028_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_indentExpr(v_givenType_1019_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1025_);
v___x_1039_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_indentExpr(v_expectedType_1020_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1042_, v___y_1021_, v___y_1022_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_1044_, lean_object* v_declName_1045_, lean_object* v_givenType_1046_, lean_object* v_expectedType_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1044_, v_declName_1045_, v_givenType_1046_, v_expectedType_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_decl_1056_, lean_object* v_stx_1057_, uint8_t v_kind_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1057_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___x_1122_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
lean_inc(v_decl_1056_);
lean_inc(v___x_1055_);
v___x_1122_ = l_Lean_ensureAttrDeclIsMeta(v___x_1055_, v_decl_1056_, v_kind_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1122_) == 0)
{
uint8_t v___x_1123_; uint8_t v___x_1124_; 
lean_dec_ref_known(v___x_1122_, 1);
v___x_1123_ = 0;
v___x_1124_ = l_Lean_instBEqAttributeKind_beq(v_kind_1058_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_a_1063_);
lean_dec(v_decl_1056_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v___x_1125_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_1055_, v_kind_1058_, v___y_1059_, v___y_1060_);
return v___x_1125_;
}
else
{
v___y_1103_ = v___y_1059_;
v___y_1104_ = v___y_1060_;
goto v___jp_1102_;
}
}
else
{
lean_dec(v_a_1063_);
lean_dec(v_decl_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
return v___x_1122_;
}
v___jp_1064_:
{
lean_object* v___x_1067_; lean_object* v_env_1068_; lean_object* v_ref_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1067_ = lean_st_ref_get(v___y_1066_);
v_env_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_env_1068_);
lean_dec(v___x_1067_);
v_ref_1069_ = lean_ctor_get(v___y_1065_, 2);
v___x_1070_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1065_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_env_1068_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
lean_inc(v_decl_1056_);
v___x_1072_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_decl_1056_, v___x_1071_);
lean_dec_ref_known(v___x_1071_, 2);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_env_1076_; lean_object* v___x_1077_; lean_object* v_toEnvExtension_1078_; lean_object* v_addEntryFn_1079_; lean_object* v_asyncMode_1080_; uint8_t v_logWrites_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; uint8_t v___x_1084_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1063_);
lean_ctor_set(v___x_1074_, 1, v_a_1073_);
v___x_1075_ = lean_st_ref_get(v___y_1066_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_1078_ = lean_ctor_get(v___x_1077_, 0);
v_addEntryFn_1079_ = lean_ctor_get(v___x_1077_, 3);
v_asyncMode_1080_ = lean_ctor_get(v_toEnvExtension_1078_, 2);
v_logWrites_1081_ = lean_ctor_get_uint8(v_toEnvExtension_1078_, sizeof(void*)*6);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_decl_1056_);
lean_ctor_set(v___x_1082_, 1, v___x_1074_);
lean_inc(v_addEntryFn_1079_);
v___f_1083_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1083_, 0, v_addEntryFn_1079_);
lean_closure_set(v___f_1083_, 1, v___x_1082_);
v___x_1084_ = 1;
if (v_logWrites_1081_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc_ref(v_toEnvExtension_1078_);
v___x_1085_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1078_, v_env_1076_, v___f_1083_, v_asyncMode_1080_, v___x_1052_, v___x_1084_);
v___x_1086_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1085_, v___y_1066_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc_ref_n(v_toEnvExtension_1078_, 2);
v___x_1087_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1078_, v_env_1076_);
lean_dec_ref(v_env_1076_);
v___x_1088_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1078_, v___x_1087_, v___f_1083_, v_asyncMode_1080_, v___x_1052_, v___x_1084_);
v___x_1089_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1088_, v___y_1066_);
return v___x_1089_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_a_1063_);
lean_dec(v_decl_1056_);
lean_dec(v___x_1052_);
v_a_1090_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1092_ = v___x_1072_;
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1072_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1094_ = lean_io_error_to_string(v_a_1090_);
v___x_1095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
v___x_1096_ = l_Lean_MessageData_ofFormat(v___x_1095_);
lean_inc(v_ref_1069_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_ref_1069_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1097_);
v___x_1099_ = v___x_1092_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
v___jp_1102_:
{
lean_object* v___x_1105_; 
lean_inc(v_decl_1056_);
v___x_1105_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_1056_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l_Lean_ConstantInfo_type(v_a_1106_);
lean_dec(v_a_1106_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2));
v___x_1109_ = l_Lean_Name_mkStr3(v___x_1053_, v___x_1054_, v___x_1108_);
v___x_1110_ = l_Lean_Expr_isConstOf(v___x_1107_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v_a_1063_);
lean_dec(v___x_1052_);
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Lean_mkConst(v___x_1109_, v___x_1111_);
v___x_1113_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_1055_, v_decl_1056_, v___x_1107_, v___x_1112_, v___y_1103_, v___y_1104_);
return v___x_1113_;
}
else
{
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec(v___x_1055_);
v___y_1065_ = v___y_1103_;
v___y_1066_ = v___y_1104_;
goto v___jp_1064_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_a_1063_);
lean_dec(v_decl_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_decl_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
v_a_1126_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1062_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1062_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1134_, lean_object* v___x_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v_decl_1138_, lean_object* v_stx_1139_, lean_object* v_kind_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v_kind_boxed_1144_; lean_object* v_res_1145_; 
v_kind_boxed_1144_ = lean_unbox(v_kind_1140_);
v_res_1145_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1134_, v___x_1135_, v___x_1136_, v___x_1137_, v_decl_1138_, v_stx_1139_, v_kind_boxed_1144_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1145_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1152_, lean_object* v_decl_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1157_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1158_ = l_Lean_MessageData_ofName(v___x_1152_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1161_, v___y_1154_, v___y_1155_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1163_, lean_object* v_decl_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1163_, v_decl_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_decl_1164_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1225_ = l_Lean_registerBuiltinAttribute(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_1229_, v___y_1230_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(v_00_u03b1_1234_, v_msg_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1240_, lean_object* v_attrName_1241_, lean_object* v_declName_1242_, lean_object* v_givenType_1243_, lean_object* v_expectedType_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1241_, v_declName_1242_, v_givenType_1243_, v_expectedType_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_attrName_1250_, lean_object* v_declName_1251_, lean_object* v_givenType_1252_, lean_object* v_expectedType_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(v_00_u03b1_1249_, v_attrName_1250_, v_declName_1251_, v_givenType_1252_, v_expectedType_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1258_, lean_object* v_name_1259_, uint8_t v_kind_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_1259_, v_kind_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_name_1266_, lean_object* v_kind_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v_kind_boxed_1271_; lean_object* v_res_1272_; 
v_kind_boxed_1271_ = lean_unbox(v_kind_1267_);
v_res_1272_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(v_00_u03b1_1265_, v_name_1266_, v_kind_boxed_1271_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1273_, lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_constName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1279_, v_constName_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1285_, lean_object* v_ref_1286_, lean_object* v_constName_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1286_, v_constName_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_constName_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1292_, v_ref_1293_, v_constName_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v_ref_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1299_, lean_object* v_ref_1300_, lean_object* v_msg_1301_, lean_object* v_declHint_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1300_, v_msg_1301_, v_declHint_1302_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_ref_1308_, lean_object* v_msg_1309_, lean_object* v_declHint_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1307_, v_ref_1308_, v_msg_1309_, v_declHint_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_ref_1308_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1315_, lean_object* v_declHint_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1315_, v_declHint_1316_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1321_, lean_object* v_declHint_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1321_, v_declHint_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1327_, lean_object* v_ref_1328_, lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1328_, v_msg_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_ref_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1334_, v_ref_1335_, v_msg_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v_ref_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(uint8_t v_x_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_box(v_x_1341_);
v___x_1343_ = lean_obj_tag_nat(v___x_1342_);
lean_dec(v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl___boxed(lean_object* v_x_1344_){
_start:
{
uint8_t v_x_4__boxed_1345_; lean_object* v_res_1346_; 
v_x_4__boxed_1345_ = lean_unbox(v_x_1344_);
v_res_1346_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(v_x_4__boxed_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object* v_k_1347_){
_start:
{
lean_inc(v_k_1347_);
return v_k_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object* v_k_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(v_k_1348_);
lean_dec(v_k_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object* v_motive_1350_, lean_object* v_ctorIdx_1351_, uint8_t v_t_1352_, lean_object* v_h_1353_, lean_object* v_k_1354_){
_start:
{
lean_inc(v_k_1354_);
return v_k_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object* v_motive_1355_, lean_object* v_ctorIdx_1356_, lean_object* v_t_1357_, lean_object* v_h_1358_, lean_object* v_k_1359_){
_start:
{
uint8_t v_t_boxed_1360_; lean_object* v_res_1361_; 
v_t_boxed_1360_ = lean_unbox(v_t_1357_);
v_res_1361_ = l_Lean_Fmt_Comment_Whitespace_ctorElim(v_motive_1355_, v_ctorIdx_1356_, v_t_boxed_1360_, v_h_1358_, v_k_1359_);
lean_dec(v_k_1359_);
lean_dec(v_ctorIdx_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object* v_leading_1362_){
_start:
{
lean_inc(v_leading_1362_);
return v_leading_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object* v_leading_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(v_leading_1363_);
lean_dec(v_leading_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object* v_motive_1365_, uint8_t v_t_1366_, lean_object* v_h_1367_, lean_object* v_leading_1368_){
_start:
{
lean_inc(v_leading_1368_);
return v_leading_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object* v_motive_1369_, lean_object* v_t_1370_, lean_object* v_h_1371_, lean_object* v_leading_1372_){
_start:
{
uint8_t v_t_boxed_1373_; lean_object* v_res_1374_; 
v_t_boxed_1373_ = lean_unbox(v_t_1370_);
v_res_1374_ = l_Lean_Fmt_Comment_Whitespace_leading_elim(v_motive_1369_, v_t_boxed_1373_, v_h_1371_, v_leading_1372_);
lean_dec(v_leading_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object* v_trailing_1375_){
_start:
{
lean_inc(v_trailing_1375_);
return v_trailing_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object* v_trailing_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(v_trailing_1376_);
lean_dec(v_trailing_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object* v_motive_1378_, uint8_t v_t_1379_, lean_object* v_h_1380_, lean_object* v_trailing_1381_){
_start:
{
lean_inc(v_trailing_1381_);
return v_trailing_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object* v_motive_1382_, lean_object* v_t_1383_, lean_object* v_h_1384_, lean_object* v_trailing_1385_){
_start:
{
uint8_t v_t_boxed_1386_; lean_object* v_res_1387_; 
v_t_boxed_1386_ = lean_unbox(v_t_1383_);
v_res_1387_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim(v_motive_1382_, v_t_boxed_1386_, v_h_1384_, v_trailing_1385_);
lean_dec(v_trailing_1385_);
return v_res_1387_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default(void){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = 0;
return v___x_1388_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace(void){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = 0;
return v___x_1389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqWhitespace_beq(uint8_t v_x_1390_, uint8_t v_y_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1392_ = lean_box(v_x_1390_);
v___x_1393_ = lean_obj_tag_nat(v___x_1392_);
lean_dec(v___x_1392_);
v___x_1394_ = lean_box(v_y_1391_);
v___x_1395_ = lean_obj_tag_nat(v___x_1394_);
lean_dec(v___x_1394_);
v___x_1396_ = lean_nat_dec_eq(v___x_1393_, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed(lean_object* v_x_1397_, lean_object* v_y_1398_){
_start:
{
uint8_t v_x_24__boxed_1399_; uint8_t v_y_25__boxed_1400_; uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_x_24__boxed_1399_ = lean_unbox(v_x_1397_);
v_y_25__boxed_1400_ = lean_unbox(v_y_1398_);
v_res_1401_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_x_24__boxed_1399_, v_y_25__boxed_1400_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(2u);
v___x_1412_ = lean_nat_to_int(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_to_int(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t v_x_1415_, lean_object* v_prec_1416_){
_start:
{
lean_object* v___y_1418_; lean_object* v___y_1425_; 
if (v_x_1415_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(1024u);
v___x_1432_ = lean_nat_dec_le(v___x_1431_, v_prec_1416_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1418_ = v___x_1433_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1418_ = v___x_1434_;
goto v___jp_1417_;
}
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_unsigned_to_nat(1024u);
v___x_1436_ = lean_nat_dec_le(v___x_1435_, v_prec_1416_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1425_ = v___x_1437_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1425_ = v___x_1438_;
goto v___jp_1424_;
}
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1));
lean_inc(v___y_1418_);
v___x_1420_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___y_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = 0;
v___x_1422_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*1, v___x_1421_);
v___x_1423_ = l_Repr_addAppParen(v___x_1422_, v_prec_1416_);
return v___x_1423_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1426_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3));
lean_inc(v___y_1425_);
v___x_1427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = 0;
v___x_1429_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*1, v___x_1428_);
v___x_1430_ = l_Repr_addAppParen(v___x_1429_, v_prec_1416_);
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object* v_x_1439_, lean_object* v_prec_1440_){
_start:
{
uint8_t v_x_117__boxed_1441_; lean_object* v_res_1442_; 
v_x_117__boxed_1441_ = lean_unbox(v_x_1439_);
v_res_1442_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_x_117__boxed_1441_, v_prec_1440_);
lean_dec(v_prec_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl(uint8_t v_x_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(v_x_1445_);
v___x_1447_ = lean_obj_tag_nat(v___x_1446_);
lean_dec(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl___boxed(lean_object* v_x_1448_){
_start:
{
uint8_t v_x_4__boxed_1449_; lean_object* v_res_1450_; 
v_x_4__boxed_1449_ = lean_unbox(v_x_1448_);
v_res_1450_ = l_Lean_Fmt_Comment_Placement_ctorIdx___impl(v_x_4__boxed_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object* v_k_1451_){
_start:
{
lean_inc(v_k_1451_);
return v_k_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object* v_k_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Fmt_Comment_Placement_ctorElim___redArg(v_k_1452_);
lean_dec(v_k_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object* v_motive_1454_, lean_object* v_ctorIdx_1455_, uint8_t v_t_1456_, lean_object* v_h_1457_, lean_object* v_k_1458_){
_start:
{
lean_inc(v_k_1458_);
return v_k_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object* v_motive_1459_, lean_object* v_ctorIdx_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_k_1463_){
_start:
{
uint8_t v_t_boxed_1464_; lean_object* v_res_1465_; 
v_t_boxed_1464_ = lean_unbox(v_t_1461_);
v_res_1465_ = l_Lean_Fmt_Comment_Placement_ctorElim(v_motive_1459_, v_ctorIdx_1460_, v_t_boxed_1464_, v_h_1462_, v_k_1463_);
lean_dec(v_k_1463_);
lean_dec(v_ctorIdx_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object* v_afterToken_1466_){
_start:
{
lean_inc(v_afterToken_1466_);
return v_afterToken_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object* v_afterToken_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(v_afterToken_1467_);
lean_dec(v_afterToken_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object* v_motive_1469_, uint8_t v_t_1470_, lean_object* v_h_1471_, lean_object* v_afterToken_1472_){
_start:
{
lean_inc(v_afterToken_1472_);
return v_afterToken_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object* v_motive_1473_, lean_object* v_t_1474_, lean_object* v_h_1475_, lean_object* v_afterToken_1476_){
_start:
{
uint8_t v_t_boxed_1477_; lean_object* v_res_1478_; 
v_t_boxed_1477_ = lean_unbox(v_t_1474_);
v_res_1478_ = l_Lean_Fmt_Comment_Placement_afterToken_elim(v_motive_1473_, v_t_boxed_1477_, v_h_1475_, v_afterToken_1476_);
lean_dec(v_afterToken_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object* v_onLineBeforeToken_1479_){
_start:
{
lean_inc(v_onLineBeforeToken_1479_);
return v_onLineBeforeToken_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object* v_onLineBeforeToken_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(v_onLineBeforeToken_1480_);
lean_dec(v_onLineBeforeToken_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object* v_motive_1482_, uint8_t v_t_1483_, lean_object* v_h_1484_, lean_object* v_onLineBeforeToken_1485_){
_start:
{
lean_inc(v_onLineBeforeToken_1485_);
return v_onLineBeforeToken_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object* v_motive_1486_, lean_object* v_t_1487_, lean_object* v_h_1488_, lean_object* v_onLineBeforeToken_1489_){
_start:
{
uint8_t v_t_boxed_1490_; lean_object* v_res_1491_; 
v_t_boxed_1490_ = lean_unbox(v_t_1487_);
v_res_1491_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(v_motive_1486_, v_t_boxed_1490_, v_h_1488_, v_onLineBeforeToken_1489_);
lean_dec(v_onLineBeforeToken_1489_);
return v_res_1491_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default(void){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = 0;
return v___x_1492_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement(void){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t v_x_1494_, uint8_t v_y_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1496_ = lean_box(v_x_1494_);
v___x_1497_ = lean_obj_tag_nat(v___x_1496_);
lean_dec(v___x_1496_);
v___x_1498_ = lean_box(v_y_1495_);
v___x_1499_ = lean_obj_tag_nat(v___x_1498_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_nat_dec_eq(v___x_1497_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object* v_x_1501_, lean_object* v_y_1502_){
_start:
{
uint8_t v_x_24__boxed_1503_; uint8_t v_y_25__boxed_1504_; uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_x_24__boxed_1503_ = lean_unbox(v_x_1501_);
v_y_25__boxed_1504_ = lean_unbox(v_y_1502_);
v_res_1505_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_x_24__boxed_1503_, v_y_25__boxed_1504_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t v_x_1515_, lean_object* v_prec_1516_){
_start:
{
lean_object* v___y_1518_; lean_object* v___y_1525_; 
if (v_x_1515_ == 0)
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = lean_unsigned_to_nat(1024u);
v___x_1532_ = lean_nat_dec_le(v___x_1531_, v_prec_1516_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1518_ = v___x_1533_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1518_ = v___x_1534_;
goto v___jp_1517_;
}
}
else
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(1024u);
v___x_1536_ = lean_nat_dec_le(v___x_1535_, v_prec_1516_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1525_ = v___x_1537_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1525_ = v___x_1538_;
goto v___jp_1524_;
}
}
v___jp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1));
lean_inc(v___y_1518_);
v___x_1520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___y_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = 0;
v___x_1522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*1, v___x_1521_);
v___x_1523_ = l_Repr_addAppParen(v___x_1522_, v_prec_1516_);
return v___x_1523_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1526_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3));
lean_inc(v___y_1525_);
v___x_1527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___y_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = 0;
v___x_1529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*1, v___x_1528_);
v___x_1530_ = l_Repr_addAppParen(v___x_1529_, v_prec_1516_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object* v_x_1539_, lean_object* v_prec_1540_){
_start:
{
uint8_t v_x_113__boxed_1541_; lean_object* v_res_1542_; 
v_x_113__boxed_1541_ = lean_unbox(v_x_1539_);
v_res_1542_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_x_113__boxed_1541_, v_prec_1540_);
lean_dec(v_prec_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl(uint8_t v_x_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(v_x_1545_);
v___x_1547_ = lean_obj_tag_nat(v___x_1546_);
lean_dec(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl___boxed(lean_object* v_x_1548_){
_start:
{
uint8_t v_x_4__boxed_1549_; lean_object* v_res_1550_; 
v_x_4__boxed_1549_ = lean_unbox(v_x_1548_);
v_res_1550_ = l_Lean_Fmt_Comment_Kind_ctorIdx___impl(v_x_4__boxed_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object* v_k_1551_){
_start:
{
lean_inc(v_k_1551_);
return v_k_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object* v_k_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Fmt_Comment_Kind_ctorElim___redArg(v_k_1552_);
lean_dec(v_k_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object* v_motive_1554_, lean_object* v_ctorIdx_1555_, uint8_t v_t_1556_, lean_object* v_h_1557_, lean_object* v_k_1558_){
_start:
{
lean_inc(v_k_1558_);
return v_k_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object* v_motive_1559_, lean_object* v_ctorIdx_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_k_1563_){
_start:
{
uint8_t v_t_boxed_1564_; lean_object* v_res_1565_; 
v_t_boxed_1564_ = lean_unbox(v_t_1561_);
v_res_1565_ = l_Lean_Fmt_Comment_Kind_ctorElim(v_motive_1559_, v_ctorIdx_1560_, v_t_boxed_1564_, v_h_1562_, v_k_1563_);
lean_dec(v_k_1563_);
lean_dec(v_ctorIdx_1560_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object* v_lineComment_1566_){
_start:
{
lean_inc(v_lineComment_1566_);
return v_lineComment_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object* v_lineComment_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(v_lineComment_1567_);
lean_dec(v_lineComment_1567_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object* v_motive_1569_, uint8_t v_t_1570_, lean_object* v_h_1571_, lean_object* v_lineComment_1572_){
_start:
{
lean_inc(v_lineComment_1572_);
return v_lineComment_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object* v_motive_1573_, lean_object* v_t_1574_, lean_object* v_h_1575_, lean_object* v_lineComment_1576_){
_start:
{
uint8_t v_t_boxed_1577_; lean_object* v_res_1578_; 
v_t_boxed_1577_ = lean_unbox(v_t_1574_);
v_res_1578_ = l_Lean_Fmt_Comment_Kind_lineComment_elim(v_motive_1573_, v_t_boxed_1577_, v_h_1575_, v_lineComment_1576_);
lean_dec(v_lineComment_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object* v_blockComment_1579_){
_start:
{
lean_inc(v_blockComment_1579_);
return v_blockComment_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object* v_blockComment_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(v_blockComment_1580_);
lean_dec(v_blockComment_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object* v_motive_1582_, uint8_t v_t_1583_, lean_object* v_h_1584_, lean_object* v_blockComment_1585_){
_start:
{
lean_inc(v_blockComment_1585_);
return v_blockComment_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object* v_motive_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_blockComment_1589_){
_start:
{
uint8_t v_t_boxed_1590_; lean_object* v_res_1591_; 
v_t_boxed_1590_ = lean_unbox(v_t_1587_);
v_res_1591_ = l_Lean_Fmt_Comment_Kind_blockComment_elim(v_motive_1586_, v_t_boxed_1590_, v_h_1588_, v_blockComment_1589_);
lean_dec(v_blockComment_1589_);
return v_res_1591_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = 0;
return v___x_1592_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind(void){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = 0;
return v___x_1593_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqKind_beq(uint8_t v_x_1594_, uint8_t v_y_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1596_ = lean_box(v_x_1594_);
v___x_1597_ = lean_obj_tag_nat(v___x_1596_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_box(v_y_1595_);
v___x_1599_ = lean_obj_tag_nat(v___x_1598_);
lean_dec(v___x_1598_);
v___x_1600_ = lean_nat_dec_eq(v___x_1597_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqKind_beq___boxed(lean_object* v_x_1601_, lean_object* v_y_1602_){
_start:
{
uint8_t v_x_24__boxed_1603_; uint8_t v_y_25__boxed_1604_; uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_x_24__boxed_1603_ = lean_unbox(v_x_1601_);
v_y_25__boxed_1604_ = lean_unbox(v_y_1602_);
v_res_1605_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_x_24__boxed_1603_, v_y_25__boxed_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t v_x_1615_, lean_object* v_prec_1616_){
_start:
{
lean_object* v___y_1618_; lean_object* v___y_1625_; 
if (v_x_1615_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(1024u);
v___x_1632_ = lean_nat_dec_le(v___x_1631_, v_prec_1616_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1618_ = v___x_1633_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1618_ = v___x_1634_;
goto v___jp_1617_;
}
}
else
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1024u);
v___x_1636_ = lean_nat_dec_le(v___x_1635_, v_prec_1616_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1625_ = v___x_1637_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1625_ = v___x_1638_;
goto v___jp_1624_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1619_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__1));
lean_inc(v___y_1618_);
v___x_1620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___y_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = 0;
v___x_1622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*1, v___x_1621_);
v___x_1623_ = l_Repr_addAppParen(v___x_1622_, v_prec_1616_);
return v___x_1623_;
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1626_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__3));
lean_inc(v___y_1625_);
v___x_1627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___y_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = 0;
v___x_1629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*1, v___x_1628_);
v___x_1630_ = l_Repr_addAppParen(v___x_1629_, v_prec_1616_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object* v_x_1639_, lean_object* v_prec_1640_){
_start:
{
uint8_t v_x_113__boxed_1641_; lean_object* v_res_1642_; 
v_x_113__boxed_1641_ = lean_unbox(v_x_1639_);
v_res_1642_ = l_Lean_Fmt_Comment_instReprKind_repr(v_x_113__boxed_1641_, v_prec_1640_);
lean_dec(v_prec_1640_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default___closed__1(void){
_start:
{
uint8_t v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1647_ = 0;
v___x_1648_ = ((lean_object*)(l_Lean_Fmt_instInhabitedComment_default___closed__0));
v___x_1649_ = 0;
v___x_1650_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_1651_ = 0;
v___x_1652_ = 0;
v___x_1653_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1653_, 0, v___x_1650_);
lean_ctor_set(v___x_1653_, 1, v___x_1650_);
lean_ctor_set(v___x_1653_, 2, v___x_1648_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*3, v___x_1652_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*3 + 1, v___x_1651_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*3 + 2, v___x_1649_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*3 + 3, v___x_1647_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default(void){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Lean_Fmt_instInhabitedComment_default___closed__1, &l_Lean_Fmt_instInhabitedComment_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedComment_default___closed__1);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment(void){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Fmt_instInhabitedComment_default;
return v___x_1655_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(lean_object* v_xs_1656_, lean_object* v_ys_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_zero_1659_; uint8_t v_isZero_1660_; 
v_zero_1659_ = lean_unsigned_to_nat(0u);
v_isZero_1660_ = lean_nat_dec_eq(v_x_1658_, v_zero_1659_);
if (v_isZero_1660_ == 1)
{
lean_dec(v_x_1658_);
return v_isZero_1660_;
}
else
{
lean_object* v_one_1661_; lean_object* v_n_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_one_1661_ = lean_unsigned_to_nat(1u);
v_n_1662_ = lean_nat_sub(v_x_1658_, v_one_1661_);
lean_dec(v_x_1658_);
v___x_1663_ = lean_array_fget_borrowed(v_xs_1656_, v_n_1662_);
v___x_1664_ = lean_array_fget_borrowed(v_ys_1657_, v_n_1662_);
v___x_1665_ = lean_string_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec(v_n_1662_);
return v___x_1665_;
}
else
{
v_x_1658_ = v_n_1662_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg___boxed(lean_object* v_xs_1667_, lean_object* v_ys_1668_, lean_object* v_x_1669_){
_start:
{
uint8_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1667_, v_ys_1668_, v_x_1669_);
lean_dec_ref(v_ys_1668_);
lean_dec_ref(v_xs_1667_);
v_r_1671_ = lean_box(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqComment_beq(lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v_kind_1674_; uint8_t v_placement_1675_; lean_object* v_originalTokenRange_1676_; lean_object* v_originalWhitespaceRange_1677_; uint8_t v_originalWhitespaceKind_1678_; lean_object* v_content_1679_; uint8_t v_emptyLineBefore_1680_; uint8_t v_kind_1681_; uint8_t v_placement_1682_; lean_object* v_originalTokenRange_1683_; lean_object* v_originalWhitespaceRange_1684_; uint8_t v_originalWhitespaceKind_1685_; lean_object* v_content_1686_; uint8_t v_emptyLineBefore_1687_; uint8_t v___x_1688_; 
v_kind_1674_ = lean_ctor_get_uint8(v_x_1672_, sizeof(void*)*3);
v_placement_1675_ = lean_ctor_get_uint8(v_x_1672_, sizeof(void*)*3 + 1);
v_originalTokenRange_1676_ = lean_ctor_get(v_x_1672_, 0);
v_originalWhitespaceRange_1677_ = lean_ctor_get(v_x_1672_, 1);
v_originalWhitespaceKind_1678_ = lean_ctor_get_uint8(v_x_1672_, sizeof(void*)*3 + 2);
v_content_1679_ = lean_ctor_get(v_x_1672_, 2);
v_emptyLineBefore_1680_ = lean_ctor_get_uint8(v_x_1672_, sizeof(void*)*3 + 3);
v_kind_1681_ = lean_ctor_get_uint8(v_x_1673_, sizeof(void*)*3);
v_placement_1682_ = lean_ctor_get_uint8(v_x_1673_, sizeof(void*)*3 + 1);
v_originalTokenRange_1683_ = lean_ctor_get(v_x_1673_, 0);
v_originalWhitespaceRange_1684_ = lean_ctor_get(v_x_1673_, 1);
v_originalWhitespaceKind_1685_ = lean_ctor_get_uint8(v_x_1673_, sizeof(void*)*3 + 2);
v_content_1686_ = lean_ctor_get(v_x_1673_, 2);
v_emptyLineBefore_1687_ = lean_ctor_get_uint8(v_x_1673_, sizeof(void*)*3 + 3);
v___x_1688_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_kind_1674_, v_kind_1681_);
if (v___x_1688_ == 0)
{
return v___x_1688_;
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_placement_1675_, v_placement_1682_);
if (v___x_1689_ == 0)
{
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Lean_Syntax_instBEqRange_beq(v_originalTokenRange_1676_, v_originalTokenRange_1683_);
if (v___x_1690_ == 0)
{
return v___x_1690_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = l_Lean_Syntax_instBEqRange_beq(v_originalWhitespaceRange_1677_, v_originalWhitespaceRange_1684_);
if (v___x_1691_ == 0)
{
return v___x_1691_;
}
else
{
uint8_t v___x_1692_; 
v___x_1692_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_originalWhitespaceKind_1678_, v_originalWhitespaceKind_1685_);
if (v___x_1692_ == 0)
{
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = lean_array_get_size(v_content_1679_);
v___x_1694_ = lean_array_get_size(v_content_1686_);
v___x_1695_ = lean_nat_dec_eq(v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_content_1679_, v_content_1686_, v___x_1693_);
if (v___x_1696_ == 0)
{
return v___x_1696_;
}
else
{
if (v_emptyLineBefore_1687_ == 0)
{
if (v_emptyLineBefore_1680_ == 0)
{
return v___x_1696_;
}
else
{
return v_emptyLineBefore_1687_;
}
}
else
{
return v_emptyLineBefore_1680_;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqComment_beq___boxed(lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
uint8_t v_res_1699_; lean_object* v_r_1700_; 
v_res_1699_ = l_Lean_Fmt_instBEqComment_beq(v_x_1697_, v_x_1698_);
lean_dec_ref(v_x_1698_);
lean_dec_ref(v_x_1697_);
v_r_1700_ = lean_box(v_res_1699_);
return v_r_1700_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(lean_object* v_xs_1701_, lean_object* v_ys_1702_, lean_object* v_hsz_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1701_, v_ys_1702_, v_x_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___boxed(lean_object* v_xs_1707_, lean_object* v_ys_1708_, lean_object* v_hsz_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(v_xs_1707_, v_ys_1708_, v_hsz_1709_, v_x_1710_, v_x_1711_);
lean_dec_ref(v_ys_1708_);
lean_dec_ref(v_xs_1707_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
lean_dec(v_x_1716_);
return v_x_1717_;
}
else
{
lean_object* v_head_1719_; lean_object* v_tail_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1731_; 
v_head_1719_ = lean_ctor_get(v_x_1718_, 0);
v_tail_1720_ = lean_ctor_get(v_x_1718_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1722_ = v_x_1718_;
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_tail_1720_);
lean_inc(v_head_1719_);
lean_dec(v_x_1718_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1731_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
lean_inc(v_x_1716_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 5);
lean_ctor_set(v___x_1722_, 1, v_x_1716_);
lean_ctor_set(v___x_1722_, 0, v_x_1717_);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_x_1717_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_x_1716_);
v___x_1725_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_String_quote(v_head_1719_);
v___x_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v_x_1717_ = v___x_1728_;
v_x_1718_ = v_tail_1720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
lean_dec(v_x_1732_);
return v_x_1733_;
}
else
{
lean_object* v_head_1735_; lean_object* v_tail_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1747_; 
v_head_1735_ = lean_ctor_get(v_x_1734_, 0);
v_tail_1736_ = lean_ctor_get(v_x_1734_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1734_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1738_ = v_x_1734_;
v_isShared_1739_ = v_isSharedCheck_1747_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_tail_1736_);
lean_inc(v_head_1735_);
lean_dec(v_x_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1747_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
lean_inc(v_x_1732_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set_tag(v___x_1738_, 5);
lean_ctor_set(v___x_1738_, 1, v_x_1732_);
lean_ctor_set(v___x_1738_, 0, v_x_1733_);
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_x_1733_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_x_1732_);
v___x_1741_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = l_String_quote(v_head_1735_);
v___x_1743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(v_x_1732_, v___x_1744_, v_tail_1736_);
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = l_String_quote(v___y_1748_);
v___x_1750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
lean_object* v___x_1753_; 
lean_dec(v_x_1752_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
else
{
lean_object* v_tail_1754_; 
v_tail_1754_ = lean_ctor_get(v_x_1751_, 1);
if (lean_obj_tag(v_tail_1754_) == 0)
{
lean_object* v_head_1755_; lean_object* v___x_1756_; 
lean_dec(v_x_1752_);
v_head_1755_ = lean_ctor_get(v_x_1751_, 0);
lean_inc(v_head_1755_);
lean_dec_ref_known(v_x_1751_, 2);
v___x_1756_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1755_);
return v___x_1756_;
}
else
{
lean_object* v_head_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_inc(v_tail_1754_);
v_head_1757_ = lean_ctor_get(v_x_1751_, 0);
lean_inc(v_head_1757_);
lean_dec_ref_known(v_x_1751_, 2);
v___x_1758_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1757_);
v___x_1759_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(v_x_1752_, v___x_1758_, v_tail_1754_);
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object* v_xs_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_array_get_size(v_xs_1760_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_nat_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1764_ = lean_array_to_list(v_xs_1760_);
v___x_1765_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_1766_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(v___x_1764_, v___x_1765_);
v___x_1767_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_1768_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_1769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1766_);
v___x_1770_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_1771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1767_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Std_Format_fill(v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; 
lean_dec_ref(v_xs_1760_);
v___x_1774_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_1774_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_unsigned_to_nat(8u);
v___x_1785_ = lean_nat_to_int(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(13u);
v___x_1790_ = lean_nat_to_int(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(22u);
v___x_1795_ = lean_nat_to_int(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_unsigned_to_nat(11u);
v___x_1806_ = lean_nat_to_int(v___x_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_unsigned_to_nat(19u);
v___x_1811_ = lean_nat_to_int(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object* v_x_1812_){
_start:
{
uint8_t v_kind_1813_; uint8_t v_placement_1814_; lean_object* v_originalTokenRange_1815_; lean_object* v_originalWhitespaceRange_1816_; uint8_t v_originalWhitespaceKind_1817_; lean_object* v_content_1818_; uint8_t v_emptyLineBefore_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_kind_1813_ = lean_ctor_get_uint8(v_x_1812_, sizeof(void*)*3);
v_placement_1814_ = lean_ctor_get_uint8(v_x_1812_, sizeof(void*)*3 + 1);
v_originalTokenRange_1815_ = lean_ctor_get(v_x_1812_, 0);
lean_inc_ref(v_originalTokenRange_1815_);
v_originalWhitespaceRange_1816_ = lean_ctor_get(v_x_1812_, 1);
lean_inc_ref(v_originalWhitespaceRange_1816_);
v_originalWhitespaceKind_1817_ = lean_ctor_get_uint8(v_x_1812_, sizeof(void*)*3 + 2);
v_content_1818_ = lean_ctor_get(v_x_1812_, 2);
lean_inc_ref(v_content_1818_);
v_emptyLineBefore_1819_ = lean_ctor_get_uint8(v_x_1812_, sizeof(void*)*3 + 3);
lean_dec_ref(v_x_1812_);
v___x_1820_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_1821_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__3));
v___x_1822_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__4, &l_Lean_Fmt_instReprComment_repr___redArg___closed__4_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Lean_Fmt_Comment_instReprKind_repr(v_kind_1813_, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = 0;
v___x_1827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1821_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_box(1);
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__6));
v___x_1834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1820_);
v___x_1836_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__7, &l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7);
v___x_1837_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_placement_1814_, v___x_1823_);
v___x_1838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*1, v___x_1826_);
v___x_1840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1835_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1829_);
v___x_1842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1831_);
v___x_1843_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__9));
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1820_);
v___x_1846_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_1847_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalTokenRange_1815_);
v___x_1848_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*1, v___x_1826_);
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1845_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1829_);
v___x_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1831_);
v___x_1853_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__12));
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1820_);
v___x_1856_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_1857_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalWhitespaceRange_1816_);
v___x_1858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*1, v___x_1826_);
v___x_1860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1855_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1829_);
v___x_1862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1831_);
v___x_1863_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__14));
v___x_1864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v___x_1820_);
v___x_1866_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_1867_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_originalWhitespaceKind_1817_, v___x_1823_);
v___x_1868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*1, v___x_1826_);
v___x_1870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1865_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1829_);
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1831_);
v___x_1873_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__16));
v___x_1874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1820_);
v___x_1876_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__17, &l_Lean_Fmt_instReprComment_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17);
v___x_1877_ = l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(v_content_1818_);
v___x_1878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*1, v___x_1826_);
v___x_1880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1875_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1829_);
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1831_);
v___x_1883_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__19));
v___x_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1820_);
v___x_1886_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__20, &l_Lean_Fmt_instReprComment_repr___redArg___closed__20_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__20);
v___x_1887_ = l_Bool_repr___redArg(v_emptyLineBefore_1819_);
v___x_1888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*1, v___x_1826_);
v___x_1890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1885_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_1892_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1890_);
v___x_1894_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_1895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1891_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*1, v___x_1826_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object* v_x_1898_, lean_object* v_prec_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Fmt_instReprComment_repr___redArg(v_x_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object* v_x_1901_, lean_object* v_prec_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Fmt_instReprComment_repr(v_x_1901_, v_prec_1902_);
lean_dec(v_prec_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object* v_entry_1906_, lean_object* v_as_1907_, lean_object* v_j_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_array_get_size(v_as_1907_);
v___x_1910_ = lean_nat_dec_lt(v_j_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec(v_j_1908_);
v___x_1911_ = lean_box(0);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v_priority_1913_; lean_object* v_priority_1914_; uint8_t v___x_1915_; 
v___x_1912_ = lean_array_fget_borrowed(v_as_1907_, v_j_1908_);
v_priority_1913_ = lean_ctor_get(v___x_1912_, 0);
v_priority_1914_ = lean_ctor_get(v_entry_1906_, 0);
v___x_1915_ = lean_nat_dec_lt(v_priority_1913_, v_priority_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_j_1908_, v___x_1916_);
lean_dec(v_j_1908_);
v_j_1908_ = v___x_1917_;
goto _start;
}
else
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_j_1908_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object* v_entry_1920_, lean_object* v_as_1921_, lean_object* v_j_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1920_, v_as_1921_, v_j_1922_);
lean_dec_ref(v_as_1921_);
lean_dec_ref(v_entry_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object* v_collectors_1924_, lean_object* v_entry_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1925_, v_collectors_1924_, v___x_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_array_get_size(v_collectors_1924_);
v___x_1929_ = l_Array_insertIdx_x21___redArg(v_collectors_1924_, v___x_1928_, v_entry_1925_);
return v___x_1929_;
}
else
{
lean_object* v_val_1930_; lean_object* v___x_1931_; 
v_val_1930_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1931_ = l_Array_insertIdx_x21___redArg(v_collectors_1924_, v_val_1930_, v_entry_1925_);
lean_dec(v_val_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_));
v___x_1936_ = lean_st_mk_ref(v___x_1935_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object* v_priority_1940_, lean_object* v_collector_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_1944_ = lean_st_ref_take(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_priority_1940_);
lean_ctor_set(v___x_1945_, 1, v_collector_1941_);
v___x_1946_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v___x_1944_, v___x_1945_);
v___x_1947_ = lean_st_ref_put(v___x_1943_, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object* v_priority_1949_, lean_object* v_collector_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Fmt_addBuiltinCommentCollector(v_priority_1949_, v_collector_1950_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object* v_constName_1958_, lean_object* v_env_1959_, lean_object* v_opts_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
v___x_1962_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1959_, v_opts_1960_, v___x_1961_, v_constName_1958_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object* v_constName_1963_, lean_object* v_env_1964_, lean_object* v_opts_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(v_constName_1963_, v_env_1964_, v_opts_1965_);
lean_dec_ref(v_opts_1965_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object* v_constName_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_env_1970_; lean_object* v_opts_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_env_1970_ = lean_ctor_get(v_a_1968_, 0);
v_opts_1971_ = lean_ctor_get(v_a_1968_, 1);
v___x_1972_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
lean_inc_ref(v_env_1970_);
v___x_1973_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1970_, v_opts_1971_, v___x_1972_, v_constName_1967_);
v___x_1974_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object* v_constName_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_constName_1975_, v_a_1976_);
lean_dec_ref(v_a_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1979_){
_start:
{
lean_object* v_fst_1980_; 
v_fst_1980_ = lean_ctor_get(v_x_1979_, 0);
lean_inc(v_fst_1980_);
return v_fst_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1981_);
lean_dec_ref(v_x_1981_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1985_);
lean_dec_ref(v_x_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1987_, lean_object* v_s_1988_){
_start:
{
lean_object* v_fst_1989_; lean_object* v___x_1990_; 
v_fst_1989_ = lean_ctor_get(v_s_1988_, 0);
lean_inc_n(v_fst_1989_, 3);
v___x_1990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1990_, 0, v_fst_1989_);
lean_ctor_set(v___x_1990_, 1, v_fst_1989_);
lean_ctor_set(v___x_1990_, 2, v_fst_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1991_, lean_object* v_s_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1991_, v_s_1992_);
lean_dec_ref(v_s_1992_);
lean_dec_ref(v_x_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v_snd_1996_; lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2017_; 
v_snd_1996_ = lean_ctor_get(v_x_1995_, 1);
lean_inc(v_snd_1996_);
v_fst_1997_ = lean_ctor_get(v_x_1994_, 0);
v_snd_1998_ = lean_ctor_get(v_x_1994_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_1994_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2000_ = v_x_1994_;
v_isShared_2001_ = v_isSharedCheck_2017_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_snd_1998_);
lean_inc(v_fst_1997_);
lean_dec(v_x_1994_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2017_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_fst_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_fst_2002_ = lean_ctor_get(v_x_1995_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_x_1995_, 1);
lean_dec(v_unused_2016_);
v___x_2004_ = v_x_1995_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_fst_2002_);
lean_dec(v_x_1995_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_priority_2006_; lean_object* v___x_2008_; 
v_priority_2006_ = lean_ctor_get(v_snd_1996_, 0);
lean_inc(v_priority_2006_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v_priority_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_priority_2006_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2009_ = lean_array_push(v_fst_1997_, v___x_2008_);
v___x_2010_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_snd_1998_, v_snd_1996_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2010_);
lean_ctor_set(v___x_2000_, 0, v___x_2009_);
v___x_2012_ = v___x_2000_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2018_, lean_object* v___x_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = lean_st_ref_get(v___x_2018_);
v___x_2022_ = lean_mk_empty_array_with_capacity(v___x_2019_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2021_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2025_, lean_object* v___x_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2025_, v___x_2026_);
lean_dec(v___x_2026_);
lean_dec(v___x_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(lean_object* v_as_2029_, size_t v_i_2030_, size_t v_stop_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_eq(v_i_2030_, v_stop_2031_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2059_; 
v___x_2036_ = lean_array_uget(v_as_2029_, v_i_2030_);
v_fst_2037_ = lean_ctor_get(v___x_2036_, 0);
v_snd_2038_ = lean_ctor_get(v___x_2036_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2040_ = v___x_2036_;
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_snd_2038_);
lean_inc(v_fst_2037_);
lean_dec(v___x_2036_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_fst_2037_, v___y_2033_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v_a_2043_);
lean_ctor_set(v___x_2040_, 0, v_snd_2038_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_snd_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_a_2043_);
v___x_2045_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; 
v___x_2046_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_b_2032_, v___x_2045_);
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2030_, v___x_2047_);
v_i_2030_ = v___x_2048_;
v_b_2032_ = v___x_2046_;
goto _start;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2040_);
lean_dec(v_snd_2038_);
lean_dec_ref(v_b_2032_);
v_a_2051_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2042_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2042_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_b_2032_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_2061_, lean_object* v_i_2062_, lean_object* v_stop_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_i_boxed_2067_; size_t v_stop_boxed_2068_; lean_object* v_res_2069_; 
v_i_boxed_2067_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_stop_boxed_2068_ = lean_unbox_usize(v_stop_2063_);
lean_dec(v_stop_2063_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v_as_2061_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2064_, v___y_2065_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_as_2061_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(lean_object* v_as_2070_, size_t v_i_2071_, size_t v_stop_2072_, lean_object* v_b_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_a_2077_; uint8_t v___x_2081_; 
v___x_2081_ = lean_usize_dec_eq(v_i_2071_, v_stop_2072_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_array_uget_borrowed(v_as_2070_, v_i_2071_);
v___x_2084_ = lean_array_get_size(v___x_2083_);
v___x_2085_ = lean_nat_dec_lt(v___x_2082_, v___x_2084_);
if (v___x_2085_ == 0)
{
v_a_2077_ = v_b_2073_;
goto v___jp_2076_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___x_2084_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v___x_2083_, v___x_2086_, v___x_2087_, v_b_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v_a_2077_ = v_a_2089_;
goto v___jp_2076_;
}
else
{
return v___x_2088_;
}
}
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2073_);
return v___x_2090_;
}
v___jp_2076_:
{
size_t v___x_2078_; size_t v___x_2079_; 
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2071_, v___x_2078_);
v_i_2071_ = v___x_2079_;
v_b_2073_ = v_a_2077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; lean_object* v_res_2099_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2091_, v_i_boxed_2097_, v_stop_boxed_2098_, v_b_2094_, v___y_2095_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_as_2091_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_as_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_a_2106_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2110_ = lean_st_ref_get(v___x_2101_);
v___x_2111_ = lean_array_get_size(v_as_2102_);
v___x_2112_ = lean_nat_dec_lt(v___x_2100_, v___x_2111_);
if (v___x_2112_ == 0)
{
v_a_2106_ = v___x_2110_;
goto v___jp_2105_;
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = ((size_t)0ULL);
v___x_2114_ = lean_usize_of_nat(v___x_2111_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2102_, v___x_2113_, v___x_2114_, v___x_2110_, v___y_2103_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v_a_2106_ = v_a_2116_;
goto v___jp_2105_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_a_2117_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2115_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
v___jp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_mk_empty_array_with_capacity(v___x_2100_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v_a_2106_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v_as_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2125_, v___x_2126_, v_as_2127_, v___y_2128_);
lean_dec_ref(v___y_2128_);
lean_dec_ref(v_as_2127_);
lean_dec(v___x_2126_);
lean_dec(v___x_2125_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___f_2141_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_2141_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_2141_, 0, v___x_2140_);
lean_closure_set(v___f_2141_, 1, v___x_2139_);
return v___f_2141_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; 
v___x_2142_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_2143_ = lean_unsigned_to_nat(0u);
v___f_2144_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_2144_, 0, v___x_2143_);
lean_closure_set(v___f_2144_, 1, v___x_2142_);
return v___f_2144_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___f_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2145_ = 0;
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_box(2);
v___f_2148_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2149_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2150_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2151_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___f_2152_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2153_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2154_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___f_2152_);
lean_ctor_set(v___x_2154_, 2, v___f_2151_);
lean_ctor_set(v___x_2154_, 3, v___f_2150_);
lean_ctor_set(v___x_2154_, 4, v___f_2149_);
lean_ctor_set(v___x_2154_, 5, v___f_2148_);
lean_ctor_set(v___x_2154_, 6, v___x_2147_);
lean_ctor_set(v___x_2154_, 7, v___x_2146_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*8, v___x_2145_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*8 + 1, v___x_2145_);
return v___x_2154_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___f_2155_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2156_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___f_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2160_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object* v_env_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v_toEnvExtension_2165_; lean_object* v_asyncMode_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v_snd_2171_; 
v___x_2164_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2165_ = lean_ctor_get(v___x_2164_, 0);
v_asyncMode_2166_ = lean_ctor_get(v_toEnvExtension_2165_, 2);
v___x_2167_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_2168_ = lean_box(0);
v___x_2169_ = 0;
v___x_2170_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2167_, v___x_2164_, v_env_2163_, v_asyncMode_2166_, v___x_2168_, v___x_2169_);
v_snd_2171_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_snd_2171_);
lean_dec(v___x_2170_);
return v_snd_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v_addEntryFn_2172_, lean_object* v___x_2173_, lean_object* v_s_2174_){
_start:
{
lean_object* v_importedEntries_2175_; lean_object* v_state_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2184_; 
v_importedEntries_2175_ = lean_ctor_get(v_s_2174_, 0);
v_state_2176_ = lean_ctor_get(v_s_2174_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_s_2174_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2178_ = v_s_2174_;
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_state_2176_);
lean_inc(v_importedEntries_2175_);
lean_dec(v_s_2174_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_state_2180_; lean_object* v___x_2182_; 
v_state_2180_ = lean_apply_2(v_addEntryFn_2172_, v_state_2176_, v___x_2173_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v_state_2180_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_importedEntries_2175_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_state_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v___x_2185_, lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_decl_2189_, lean_object* v_stx_2190_, uint8_t v_kind_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Attribute_Builtin_getPrio(v_stx_2190_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___x_2255_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc(v_decl_2189_);
lean_inc(v___x_2188_);
v___x_2255_ = l_Lean_ensureAttrDeclIsMeta(v___x_2188_, v_decl_2189_, v_kind_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2255_) == 0)
{
uint8_t v___x_2256_; uint8_t v___x_2257_; 
lean_dec_ref_known(v___x_2255_, 1);
v___x_2256_ = 0;
v___x_2257_ = l_Lean_instBEqAttributeKind_beq(v_kind_2191_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_dec(v_a_2196_);
lean_dec(v_decl_2189_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v___x_2185_);
v___x_2258_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_2188_, v_kind_2191_, v___y_2192_, v___y_2193_);
return v___x_2258_;
}
else
{
v___y_2236_ = v___y_2192_;
v___y_2237_ = v___y_2193_;
goto v___jp_2235_;
}
}
else
{
lean_dec(v_a_2196_);
lean_dec(v_decl_2189_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v___x_2185_);
return v___x_2255_;
}
v___jp_2197_:
{
lean_object* v___x_2200_; lean_object* v_env_2201_; lean_object* v_ref_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2200_ = lean_st_ref_get(v___y_2199_);
v_env_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_ref(v_env_2201_);
lean_dec(v___x_2200_);
v_ref_2202_ = lean_ctor_get(v___y_2198_, 2);
v___x_2203_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2198_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v_env_2201_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc(v_decl_2189_);
v___x_2205_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_decl_2189_, v___x_2204_);
lean_dec_ref_known(v___x_2204_, 2);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_env_2209_; lean_object* v___x_2210_; lean_object* v_toEnvExtension_2211_; lean_object* v_addEntryFn_2212_; lean_object* v_asyncMode_2213_; uint8_t v_logWrites_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; uint8_t v___x_2217_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_a_2196_);
lean_ctor_set(v___x_2207_, 1, v_a_2206_);
v___x_2208_ = lean_st_ref_get(v___y_2199_);
v_env_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc_ref(v_env_2209_);
lean_dec(v___x_2208_);
v___x_2210_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2211_ = lean_ctor_get(v___x_2210_, 0);
v_addEntryFn_2212_ = lean_ctor_get(v___x_2210_, 3);
v_asyncMode_2213_ = lean_ctor_get(v_toEnvExtension_2211_, 2);
v_logWrites_2214_ = lean_ctor_get_uint8(v_toEnvExtension_2211_, sizeof(void*)*6);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_decl_2189_);
lean_ctor_set(v___x_2215_, 1, v___x_2207_);
lean_inc(v_addEntryFn_2212_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_2216_, 0, v_addEntryFn_2212_);
lean_closure_set(v___f_2216_, 1, v___x_2215_);
v___x_2217_ = 1;
if (v_logWrites_2214_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_inc_ref(v_toEnvExtension_2211_);
v___x_2218_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2211_, v_env_2209_, v___f_2216_, v_asyncMode_2213_, v___x_2185_, v___x_2217_);
v___x_2219_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2218_, v___y_2199_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_inc_ref_n(v_toEnvExtension_2211_, 2);
v___x_2220_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2211_, v_env_2209_);
lean_dec_ref(v_env_2209_);
v___x_2221_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2211_, v___x_2220_, v___f_2216_, v_asyncMode_2213_, v___x_2185_, v___x_2217_);
v___x_2222_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2221_, v___y_2199_);
return v___x_2222_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2196_);
lean_dec(v_decl_2189_);
lean_dec(v___x_2185_);
v_a_2223_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2225_ = v___x_2205_;
v_isShared_2226_ = v_isSharedCheck_2234_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2205_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2234_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2227_ = lean_io_error_to_string(v_a_2223_);
v___x_2228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
v___x_2229_ = l_Lean_MessageData_ofFormat(v___x_2228_);
lean_inc(v_ref_2202_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_ref_2202_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2230_);
v___x_2232_ = v___x_2225_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
v___jp_2235_:
{
lean_object* v___x_2238_; 
lean_inc(v_decl_2189_);
v___x_2238_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_2189_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l_Lean_ConstantInfo_type(v_a_2239_);
lean_dec(v_a_2239_);
v___x_2241_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0));
v___x_2242_ = l_Lean_Name_mkStr3(v___x_2186_, v___x_2187_, v___x_2241_);
v___x_2243_ = l_Lean_Expr_isConstOf(v___x_2240_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_a_2196_);
lean_dec(v___x_2185_);
v___x_2244_ = lean_box(0);
v___x_2245_ = l_Lean_mkConst(v___x_2242_, v___x_2244_);
v___x_2246_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_2188_, v_decl_2189_, v___x_2240_, v___x_2245_, v___y_2236_, v___y_2237_);
return v___x_2246_;
}
else
{
lean_dec(v___x_2242_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2188_);
v___y_2198_ = v___y_2236_;
v___y_2199_ = v___y_2237_;
goto v___jp_2197_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_a_2196_);
lean_dec(v_decl_2189_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v___x_2185_);
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_decl_2189_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v___x_2185_);
v_a_2259_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2195_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2195_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v___x_2269_, lean_object* v___x_2270_, lean_object* v_decl_2271_, lean_object* v_stx_2272_, lean_object* v_kind_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v_kind_boxed_2277_; lean_object* v_res_2278_; 
v_kind_boxed_2277_ = lean_unbox(v_kind_2273_);
v_res_2278_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(v___x_2267_, v___x_2268_, v___x_2269_, v___x_2270_, v_decl_2271_, v_stx_2272_, v_kind_boxed_2277_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2278_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_unsigned_to_nat(3853185248u);
v___x_2280_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2281_ = l_Lean_Name_num___override(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2283_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2284_ = l_Lean_Name_str___override(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2286_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2287_ = l_Lean_Name_str___override(v___x_2286_, v___x_2285_);
return v___x_2287_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_unsigned_to_nat(2u);
v___x_2289_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2290_ = l_Lean_Name_num___override(v___x_2289_, v___x_2288_);
return v___x_2290_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2302_ = 1;
v___x_2303_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2304_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2305_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2306_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2303_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3, v___x_2302_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___f_2307_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___f_2308_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2309_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___f_2308_);
lean_ctor_set(v___x_2310_, 2, v___f_2307_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2313_ = l_Lean_registerBuiltinAttribute(v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object* v_attr_2316_, lean_object* v_mk_2317_, lean_object* v_env_2318_, lean_object* v_kind_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v_attr_2316_, v_env_2318_, v_kind_2319_);
v___x_2321_ = l_List_head_x3f___redArg(v___x_2320_);
lean_dec(v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v___x_2322_; 
lean_dec_ref(v_mk_2317_);
v___x_2322_ = lean_box(0);
return v___x_2322_;
}
else
{
lean_object* v_val_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2342_; 
v_val_2323_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2325_ = v___x_2321_;
v_isShared_2326_ = v_isSharedCheck_2342_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_val_2323_);
lean_dec(v___x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2342_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_toOLeanEntry_2327_; lean_object* v_value_2328_; lean_object* v_declName_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2340_; 
v_toOLeanEntry_2327_ = lean_ctor_get(v_val_2323_, 0);
lean_inc_ref(v_toOLeanEntry_2327_);
v_value_2328_ = lean_ctor_get(v_val_2323_, 1);
lean_inc(v_value_2328_);
lean_dec(v_val_2323_);
v_declName_2329_ = lean_ctor_get(v_toOLeanEntry_2327_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_toOLeanEntry_2327_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v_toOLeanEntry_2327_, 0);
lean_dec(v_unused_2341_);
v___x_2331_ = v_toOLeanEntry_2327_;
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_declName_2329_);
lean_dec(v_toOLeanEntry_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2340_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_apply_1(v_mk_2317_, v_value_2328_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2333_);
lean_ctor_set(v___x_2331_, 0, v_declName_2329_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_declName_2329_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2335_);
v___x_2337_ = v___x_2325_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object* v_attr_2343_, lean_object* v_mk_2344_, lean_object* v_env_2345_, lean_object* v_kind_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2343_, v_mk_2344_, v_env_2345_, v_kind_2346_);
lean_dec(v_kind_2346_);
lean_dec_ref(v_attr_2343_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object* v_00_u03b1_2348_, lean_object* v_attr_2349_, lean_object* v_mk_2350_, lean_object* v_env_2351_, lean_object* v_x_2352_, lean_object* v_kind_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2349_, v_mk_2350_, v_env_2351_, v_kind_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object* v_00_u03b1_2355_, lean_object* v_attr_2356_, lean_object* v_mk_2357_, lean_object* v_env_2358_, lean_object* v_x_2359_, lean_object* v_kind_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_Fmt_keyedFmtProvider(v_00_u03b1_2355_, v_attr_2356_, v_mk_2357_, v_env_2358_, v_x_2359_, v_kind_2360_);
lean_dec(v_kind_2360_);
lean_dec_ref(v_x_2359_);
lean_dec_ref(v_attr_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_2362_, lean_object* v_i_2363_, lean_object* v_k_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = lean_array_get_size(v_keys_2362_);
v___x_2366_ = lean_nat_dec_lt(v_i_2363_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_dec(v_i_2363_);
return v___x_2366_;
}
else
{
lean_object* v_k_x27_2367_; uint8_t v___x_2368_; 
v_k_x27_2367_ = lean_array_fget_borrowed(v_keys_2362_, v_i_2363_);
v___x_2368_ = l_Lean_instBEqExtraModUse_beq(v_k_2364_, v_k_x27_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_i_2363_, v___x_2369_);
lean_dec(v_i_2363_);
v_i_2363_ = v___x_2370_;
goto _start;
}
else
{
lean_dec(v_i_2363_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_2372_, lean_object* v_i_2373_, lean_object* v_k_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2372_, v_i_2373_, v_k_2374_);
lean_dec_ref(v_k_2374_);
lean_dec_ref(v_keys_2372_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_2377_, size_t v_x_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_object* v_es_2380_; lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; lean_object* v_j_2384_; lean_object* v___x_2385_; 
v_es_2380_ = lean_ctor_get(v_x_2377_, 0);
v___x_2381_ = lean_box(2);
v___x_2382_ = ((size_t)31ULL);
v___x_2383_ = lean_usize_land(v_x_2378_, v___x_2382_);
v_j_2384_ = lean_usize_to_nat(v___x_2383_);
v___x_2385_ = lean_array_get_borrowed(v___x_2381_, v_es_2380_, v_j_2384_);
lean_dec(v_j_2384_);
switch(lean_obj_tag(v___x_2385_))
{
case 0:
{
lean_object* v_key_2386_; uint8_t v___x_2387_; 
v_key_2386_ = lean_ctor_get(v___x_2385_, 0);
v___x_2387_ = l_Lean_instBEqExtraModUse_beq(v_x_2379_, v_key_2386_);
return v___x_2387_;
}
case 1:
{
lean_object* v_node_2388_; size_t v___x_2389_; size_t v___x_2390_; 
v_node_2388_ = lean_ctor_get(v___x_2385_, 0);
v___x_2389_ = ((size_t)5ULL);
v___x_2390_ = lean_usize_shift_right(v_x_2378_, v___x_2389_);
v_x_2377_ = v_node_2388_;
v_x_2378_ = v___x_2390_;
goto _start;
}
default: 
{
uint8_t v___x_2392_; 
v___x_2392_ = 0;
return v___x_2392_;
}
}
}
else
{
lean_object* v_ks_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_ks_2393_ = lean_ctor_get(v_x_2377_, 0);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_2393_, v___x_2394_, v_x_2379_);
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
size_t v_x_5189__boxed_2399_; uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_x_5189__boxed_2399_ = lean_unbox_usize(v_x_2397_);
lean_dec(v_x_2397_);
v_res_2400_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2396_, v_x_5189__boxed_2399_, v_x_2398_);
lean_dec_ref(v_x_2398_);
lean_dec_ref(v_x_2396_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
uint64_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = l_Lean_instHashableExtraModUse_hash(v_x_2403_);
v___x_2405_ = lean_uint64_to_usize(v___x_2404_);
v___x_2406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2402_, v___x_2405_, v_x_2403_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2407_, v_x_2408_);
lean_dec_ref(v_x_2408_);
lean_dec_ref(v_x_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0(lean_object* v___x_2411_, lean_object* v_entry_2412_, lean_object* v_s_2413_){
_start:
{
lean_object* v_addEntryFn_2414_; lean_object* v_importedEntries_2415_; lean_object* v_state_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_addEntryFn_2414_ = lean_ctor_get(v___x_2411_, 3);
lean_inc(v_addEntryFn_2414_);
lean_dec_ref(v___x_2411_);
v_importedEntries_2415_ = lean_ctor_get(v_s_2413_, 0);
v_state_2416_ = lean_ctor_get(v_s_2413_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_s_2413_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_s_2413_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_state_2416_);
lean_inc(v_importedEntries_2415_);
lean_dec(v_s_2413_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_state_2420_; lean_object* v___x_2422_; 
v_state_2420_ = lean_apply_2(v_addEntryFn_2414_, v_state_2416_, v_entry_2412_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v_state_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_importedEntries_2415_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_state_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2425_; double v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_float_of_nat(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object* v_cls_2430_, lean_object* v_msg_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2482_; 
v_ref_2435_ = lean_ctor_get(v___y_2432_, 2);
v___x_2436_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_2431_, v___y_2432_, v___y_2433_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2482_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2482_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v_traceState_2442_; lean_object* v_env_2443_; lean_object* v_nextMacroScope_2444_; lean_object* v_ngen_2445_; lean_object* v_auxDeclNGen_2446_; lean_object* v_cache_2447_; lean_object* v_recordedDeps_2448_; lean_object* v_messages_2449_; lean_object* v_infoState_2450_; lean_object* v_snapshotTasks_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2481_; 
v___x_2441_ = lean_st_ref_take(v___y_2433_);
v_traceState_2442_ = lean_ctor_get(v___x_2441_, 4);
v_env_2443_ = lean_ctor_get(v___x_2441_, 0);
v_nextMacroScope_2444_ = lean_ctor_get(v___x_2441_, 1);
v_ngen_2445_ = lean_ctor_get(v___x_2441_, 2);
v_auxDeclNGen_2446_ = lean_ctor_get(v___x_2441_, 3);
v_cache_2447_ = lean_ctor_get(v___x_2441_, 5);
v_recordedDeps_2448_ = lean_ctor_get(v___x_2441_, 6);
v_messages_2449_ = lean_ctor_get(v___x_2441_, 7);
v_infoState_2450_ = lean_ctor_get(v___x_2441_, 8);
v_snapshotTasks_2451_ = lean_ctor_get(v___x_2441_, 9);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2453_ = v___x_2441_;
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_snapshotTasks_2451_);
lean_inc(v_infoState_2450_);
lean_inc(v_messages_2449_);
lean_inc(v_recordedDeps_2448_);
lean_inc(v_cache_2447_);
lean_inc(v_traceState_2442_);
lean_inc(v_auxDeclNGen_2446_);
lean_inc(v_ngen_2445_);
lean_inc(v_nextMacroScope_2444_);
lean_inc(v_env_2443_);
lean_dec(v___x_2441_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
uint64_t v_tid_2455_; lean_object* v_traces_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2480_; 
v_tid_2455_ = lean_ctor_get_uint64(v_traceState_2442_, sizeof(void*)*1);
v_traces_2456_ = lean_ctor_get(v_traceState_2442_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_traceState_2442_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2458_ = v_traceState_2442_;
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_traces_2456_);
lean_dec(v_traceState_2442_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; double v___x_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0);
v___x_2463_ = 0;
v___x_2464_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2465_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2465_, 0, v_cls_2430_);
lean_ctor_set(v___x_2465_, 1, v___x_2461_);
lean_ctor_set(v___x_2465_, 2, v___x_2464_);
lean_ctor_set_float(v___x_2465_, sizeof(void*)*3, v___x_2462_);
lean_ctor_set_float(v___x_2465_, sizeof(void*)*3 + 8, v___x_2462_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*3 + 16, v___x_2463_);
v___x_2466_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2));
v___x_2467_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v_a_2437_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
lean_inc(v_ref_2435_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_ref_2435_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = l_Lean_PersistentArray_push___redArg(v_traces_2456_, v___x_2468_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2469_);
v___x_2471_ = v___x_2458_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2469_);
lean_ctor_set_uint64(v_reuseFailAlloc_2479_, sizeof(void*)*1, v_tid_2455_);
v___x_2471_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v___x_2471_);
v___x_2473_ = v___x_2453_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_env_2443_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2444_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2445_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2446_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v_cache_2447_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_recordedDeps_2448_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_messages_2449_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_infoState_2450_);
lean_ctor_set(v_reuseFailAlloc_2478_, 9, v_snapshotTasks_2451_);
v___x_2473_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = lean_st_ref_put(v___y_2433_, v___x_2473_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2460_);
v___x_2476_ = v___x_2439_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2460_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2483_, lean_object* v_msg_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2483_, v_msg_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2488_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v_cls_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_cls_2504_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2505_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9));
v___x_2506_ = l_Lean_Name_append(v___x_2505_, v_cls_2504_);
return v___x_2506_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11));
v___x_2509_ = l_Lean_stringToMessageData(v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object* v_mod_2517_, uint8_t v_isMeta_2518_, lean_object* v_hint_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_env_2541_; uint8_t v_isExporting_2542_; lean_object* v_entry_2543_; lean_object* v___x_2544_; lean_object* v_env_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2539_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0);
v___x_2540_ = lean_st_ref_get(v___y_2521_);
v_env_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc_ref(v_env_2541_);
lean_dec(v___x_2540_);
v_isExporting_2542_ = lean_ctor_get_uint8(v_env_2541_, sizeof(void*)*13);
lean_dec_ref(v_env_2541_);
lean_inc(v_mod_2517_);
v_entry_2543_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2543_, 0, v_mod_2517_);
lean_ctor_set_uint8(v_entry_2543_, sizeof(void*)*1, v_isExporting_2542_);
lean_ctor_set_uint8(v_entry_2543_, sizeof(void*)*1 + 1, v_isMeta_2518_);
v___x_2544_ = lean_st_ref_get(v___y_2521_);
v_env_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_env_2545_);
lean_dec(v___x_2544_);
v___x_2546_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2547_ = lean_box(1);
v___x_2548_ = lean_box(0);
v___x_2549_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2539_, v___x_2546_, v_env_2545_, v___x_2547_, v___x_2548_);
v___x_2550_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v___x_2549_, v_entry_2543_);
lean_dec(v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v_toCold_2551_; lean_object* v_options_2552_; lean_object* v_inheritedTraceOptions_2553_; uint8_t v_hasTrace_2554_; lean_object* v___f_2555_; uint8_t v___x_2556_; lean_object* v___y_2558_; 
v_toCold_2551_ = lean_ctor_get(v___y_2520_, 0);
v_options_2552_ = lean_ctor_get(v_toCold_2551_, 2);
v_inheritedTraceOptions_2553_ = lean_ctor_get(v_toCold_2551_, 11);
v_hasTrace_2554_ = lean_ctor_get_uint8(v_options_2552_, sizeof(void*)*1);
v___f_2555_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2555_, 0, v___x_2546_);
lean_closure_set(v___f_2555_, 1, v_entry_2543_);
v___x_2556_ = 1;
if (v_hasTrace_2554_ == 0)
{
lean_dec(v_hint_2519_);
lean_dec(v_mod_2517_);
v___y_2558_ = v___y_2521_;
goto v___jp_2557_;
}
else
{
lean_object* v_cls_2576_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_cls_2576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2596_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10);
v___x_2597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2553_, v_options_2552_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec(v_hint_2519_);
lean_dec(v_mod_2517_);
v___y_2558_ = v___y_2521_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2598_; lean_object* v___y_2600_; 
v___x_2598_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12);
if (v_isExporting_2542_ == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17));
v___y_2600_ = v___x_2607_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2608_; 
v___x_2608_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18));
v___y_2600_ = v___x_2608_;
goto v___jp_2599_;
}
v___jp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_inc_ref(v___y_2600_);
v___x_2601_ = l_Lean_stringToMessageData(v___y_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2598_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
if (v_isMeta_2518_ == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15));
v___y_2583_ = v___x_2604_;
v___y_2584_ = v___x_2605_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2606_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16));
v___y_2583_ = v___x_2604_;
v___y_2584_ = v___x_2606_;
goto v___jp_2582_;
}
}
}
v___jp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2578_);
lean_ctor_set(v___x_2580_, 1, v___y_2579_);
v___x_2581_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2576_, v___x_2580_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_dec_ref_known(v___x_2581_, 1);
v___y_2558_ = v___y_2521_;
goto v___jp_2557_;
}
else
{
lean_dec_ref(v___f_2555_);
return v___x_2581_;
}
}
v___jp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
lean_inc_ref(v___y_2584_);
v___x_2585_ = l_Lean_stringToMessageData(v___y_2584_);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___y_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_MessageData_ofName(v_mod_2517_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l_Lean_Name_isAnonymous(v_hint_2519_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6);
v___x_2593_ = l_Lean_MessageData_ofName(v_hint_2519_);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___y_2578_ = v___x_2590_;
v___y_2579_ = v___x_2594_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2595_; 
lean_dec(v_hint_2519_);
v___x_2595_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7);
v___y_2578_ = v___x_2590_;
v___y_2579_ = v___x_2595_;
goto v___jp_2577_;
}
}
}
v___jp_2557_:
{
lean_object* v___x_2559_; lean_object* v_toEnvExtension_2560_; lean_object* v_env_2561_; lean_object* v_nextMacroScope_2562_; lean_object* v_ngen_2563_; lean_object* v_auxDeclNGen_2564_; lean_object* v_traceState_2565_; lean_object* v_recordedDeps_2566_; lean_object* v_messages_2567_; lean_object* v_infoState_2568_; lean_object* v_snapshotTasks_2569_; lean_object* v_asyncMode_2570_; uint8_t v_logWrites_2571_; lean_object* v___x_2572_; 
v___x_2559_ = lean_st_ref_take(v___y_2558_);
v_toEnvExtension_2560_ = lean_ctor_get(v___x_2546_, 0);
v_env_2561_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref(v_env_2561_);
v_nextMacroScope_2562_ = lean_ctor_get(v___x_2559_, 1);
lean_inc(v_nextMacroScope_2562_);
v_ngen_2563_ = lean_ctor_get(v___x_2559_, 2);
lean_inc_ref(v_ngen_2563_);
v_auxDeclNGen_2564_ = lean_ctor_get(v___x_2559_, 3);
lean_inc_ref(v_auxDeclNGen_2564_);
v_traceState_2565_ = lean_ctor_get(v___x_2559_, 4);
lean_inc_ref(v_traceState_2565_);
v_recordedDeps_2566_ = lean_ctor_get(v___x_2559_, 6);
lean_inc_ref(v_recordedDeps_2566_);
v_messages_2567_ = lean_ctor_get(v___x_2559_, 7);
lean_inc_ref(v_messages_2567_);
v_infoState_2568_ = lean_ctor_get(v___x_2559_, 8);
lean_inc_ref(v_infoState_2568_);
v_snapshotTasks_2569_ = lean_ctor_get(v___x_2559_, 9);
lean_inc_ref(v_snapshotTasks_2569_);
lean_dec(v___x_2559_);
v_asyncMode_2570_ = lean_ctor_get(v_toEnvExtension_2560_, 2);
v_logWrites_2571_ = lean_ctor_get_uint8(v_toEnvExtension_2560_, sizeof(void*)*6);
v___x_2572_ = lean_box(0);
if (v_logWrites_2571_ == 0)
{
lean_object* v___x_2573_; 
lean_inc_ref(v_toEnvExtension_2560_);
v___x_2573_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2560_, v_env_2561_, v___f_2555_, v_asyncMode_2570_, v___x_2548_, v___x_2556_);
v___y_2524_ = v_traceState_2565_;
v___y_2525_ = v___y_2558_;
v___y_2526_ = v_nextMacroScope_2562_;
v___y_2527_ = v_auxDeclNGen_2564_;
v___y_2528_ = v___x_2572_;
v___y_2529_ = v_infoState_2568_;
v___y_2530_ = v_recordedDeps_2566_;
v___y_2531_ = v_ngen_2563_;
v___y_2532_ = v_snapshotTasks_2569_;
v___y_2533_ = v_messages_2567_;
v___y_2534_ = v___x_2573_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_inc_ref_n(v_toEnvExtension_2560_, 2);
v___x_2574_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2560_, v_env_2561_);
lean_dec_ref(v_env_2561_);
v___x_2575_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2560_, v___x_2574_, v___f_2555_, v_asyncMode_2570_, v___x_2548_, v___x_2556_);
v___y_2524_ = v_traceState_2565_;
v___y_2525_ = v___y_2558_;
v___y_2526_ = v_nextMacroScope_2562_;
v___y_2527_ = v_auxDeclNGen_2564_;
v___y_2528_ = v___x_2572_;
v___y_2529_ = v_infoState_2568_;
v___y_2530_ = v_recordedDeps_2566_;
v___y_2531_ = v_ngen_2563_;
v___y_2532_ = v_snapshotTasks_2569_;
v___y_2533_ = v_messages_2567_;
v___y_2534_ = v___x_2575_;
goto v___jp_2523_;
}
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref_known(v_entry_2543_, 1);
lean_dec(v_hint_2519_);
lean_dec(v_mod_2517_);
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
v___jp_2523_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
v___x_2536_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2534_);
lean_ctor_set(v___x_2536_, 1, v___y_2526_);
lean_ctor_set(v___x_2536_, 2, v___y_2531_);
lean_ctor_set(v___x_2536_, 3, v___y_2527_);
lean_ctor_set(v___x_2536_, 4, v___y_2524_);
lean_ctor_set(v___x_2536_, 5, v___x_2535_);
lean_ctor_set(v___x_2536_, 6, v___y_2530_);
lean_ctor_set(v___x_2536_, 7, v___y_2533_);
lean_ctor_set(v___x_2536_, 8, v___y_2529_);
lean_ctor_set(v___x_2536_, 9, v___y_2532_);
v___x_2537_ = lean_st_ref_put(v___y_2525_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2528_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object* v_mod_2611_, lean_object* v_isMeta_2612_, lean_object* v_hint_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
uint8_t v_isMeta_boxed_2617_; lean_object* v_res_2618_; 
v_isMeta_boxed_2617_ = lean_unbox(v_isMeta_2612_);
v_res_2618_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_mod_2611_, v_isMeta_boxed_2617_, v_hint_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object* v___x_2619_, lean_object* v_declName_2620_, lean_object* v_as_2621_, size_t v_sz_2622_, size_t v_i_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_lt(v_i_2623_, v_sz_2622_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_dec(v_declName_2620_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_b_2624_);
return v___x_2629_;
}
else
{
lean_object* v___x_2630_; lean_object* v_modules_2631_; lean_object* v___x_2632_; lean_object* v_a_2633_; lean_object* v___x_2634_; lean_object* v_toImport_2635_; lean_object* v_module_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v___x_2630_ = l_Lean_Environment_header(v___x_2619_);
v_modules_2631_ = lean_ctor_get(v___x_2630_, 3);
lean_inc_ref(v_modules_2631_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2633_ = lean_array_uget_borrowed(v_as_2621_, v_i_2623_);
v___x_2634_ = lean_array_get(v___x_2632_, v_modules_2631_, v_a_2633_);
lean_dec_ref(v_modules_2631_);
v_toImport_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_toImport_2635_);
lean_dec(v___x_2634_);
v_module_2636_ = lean_ctor_get(v_toImport_2635_, 0);
lean_inc(v_module_2636_);
lean_dec_ref(v_toImport_2635_);
v___x_2637_ = lean_box(0);
v___x_2638_ = 0;
lean_inc(v_declName_2620_);
v___x_2639_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2636_, v___x_2638_, v_declName_2620_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2639_) == 0)
{
size_t v___x_2640_; size_t v___x_2641_; 
lean_dec_ref_known(v___x_2639_, 1);
v___x_2640_ = ((size_t)1ULL);
v___x_2641_ = lean_usize_add(v_i_2623_, v___x_2640_);
v_i_2623_ = v___x_2641_;
v_b_2624_ = v___x_2637_;
goto _start;
}
else
{
lean_dec(v_declName_2620_);
return v___x_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object* v___x_2643_, lean_object* v_declName_2644_, lean_object* v_as_2645_, lean_object* v_sz_2646_, lean_object* v_i_2647_, lean_object* v_b_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
size_t v_sz_boxed_2652_; size_t v_i_boxed_2653_; lean_object* v_res_2654_; 
v_sz_boxed_2652_ = lean_unbox_usize(v_sz_2646_);
lean_dec(v_sz_2646_);
v_i_boxed_2653_ = lean_unbox_usize(v_i_2647_);
lean_dec(v_i_2647_);
v_res_2654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v___x_2643_, v_declName_2644_, v_as_2645_, v_sz_boxed_2652_, v_i_boxed_2653_, v_b_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v_as_2645_);
lean_dec_ref(v___x_2643_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
if (lean_obj_tag(v_x_2656_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_box(0);
return v___x_2657_;
}
else
{
lean_object* v_key_2658_; lean_object* v_value_2659_; lean_object* v_tail_2660_; uint8_t v___x_2661_; 
v_key_2658_ = lean_ctor_get(v_x_2656_, 0);
v_value_2659_ = lean_ctor_get(v_x_2656_, 1);
v_tail_2660_ = lean_ctor_get(v_x_2656_, 2);
v___x_2661_ = lean_name_eq(v_key_2658_, v_a_2655_);
if (v___x_2661_ == 0)
{
v_x_2656_ = v_tail_2660_;
goto _start;
}
else
{
lean_object* v___x_2663_; 
lean_inc(v_value_2659_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_value_2659_);
return v___x_2663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2664_, v_x_2665_);
lean_dec(v_x_2665_);
lean_dec(v_a_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object* v_m_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_buckets_2669_; lean_object* v___x_2670_; uint64_t v___y_2672_; 
v_buckets_2669_ = lean_ctor_get(v_m_2667_, 1);
v___x_2670_ = lean_array_get_size(v_buckets_2669_);
if (lean_obj_tag(v_a_2668_) == 0)
{
uint64_t v___x_2686_; 
v___x_2686_ = 1723ULL;
v___y_2672_ = v___x_2686_;
goto v___jp_2671_;
}
else
{
uint64_t v_hash_2687_; 
v_hash_2687_ = lean_ctor_get_uint64(v_a_2668_, sizeof(void*)*2);
v___y_2672_ = v_hash_2687_;
goto v___jp_2671_;
}
v___jp_2671_:
{
uint64_t v___x_2673_; uint64_t v___x_2674_; uint64_t v_fold_2675_; uint64_t v___x_2676_; uint64_t v___x_2677_; uint64_t v___x_2678_; size_t v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2673_ = 32ULL;
v___x_2674_ = lean_uint64_shift_right(v___y_2672_, v___x_2673_);
v_fold_2675_ = lean_uint64_xor(v___y_2672_, v___x_2674_);
v___x_2676_ = 16ULL;
v___x_2677_ = lean_uint64_shift_right(v_fold_2675_, v___x_2676_);
v___x_2678_ = lean_uint64_xor(v_fold_2675_, v___x_2677_);
v___x_2679_ = lean_uint64_to_usize(v___x_2678_);
v___x_2680_ = lean_usize_of_nat(v___x_2670_);
v___x_2681_ = ((size_t)1ULL);
v___x_2682_ = lean_usize_sub(v___x_2680_, v___x_2681_);
v___x_2683_ = lean_usize_land(v___x_2679_, v___x_2682_);
v___x_2684_ = lean_array_uget_borrowed(v_buckets_2669_, v___x_2683_);
v___x_2685_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2668_, v___x_2684_);
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object* v_m_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_m_2688_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object* v_declName_2694_, uint8_t v_isMeta_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_env_2704_; lean_object* v___y_2706_; lean_object* v___x_2719_; 
v___x_2699_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0);
v___x_2700_ = lean_st_ref_get(v___y_2697_);
v_env_2704_ = lean_ctor_get(v___x_2700_, 0);
lean_inc_ref(v_env_2704_);
lean_dec(v___x_2700_);
v___x_2719_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2704_, v_declName_2694_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_dec_ref(v_env_2704_);
lean_dec(v_declName_2694_);
goto v___jp_2701_;
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2721_; lean_object* v_modules_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_val_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_val_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = l_Lean_Environment_header(v_env_2704_);
v_modules_2722_ = lean_ctor_get(v___x_2721_, 3);
lean_inc_ref(v_modules_2722_);
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_array_get_size(v_modules_2722_);
v___x_2724_ = lean_nat_dec_lt(v_val_2720_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_dec_ref(v_modules_2722_);
lean_dec(v_val_2720_);
lean_dec_ref(v_env_2704_);
lean_dec(v_declName_2694_);
goto v___jp_2701_;
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___y_2728_; 
v___x_2725_ = lean_array_fget(v_modules_2722_, v_val_2720_);
lean_dec(v_val_2720_);
lean_dec_ref(v_modules_2722_);
v___x_2726_ = lean_st_ref_get(v___y_2697_);
if (v_isMeta_2695_ == 0)
{
lean_dec(v___x_2726_);
v___y_2728_ = v_isMeta_2695_;
goto v___jp_2727_;
}
else
{
lean_object* v_env_2739_; uint8_t v___x_2740_; 
v_env_2739_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2726_);
lean_inc(v_declName_2694_);
v___x_2740_ = l_Lean_isMarkedMeta(v_env_2739_, v_declName_2694_);
if (v___x_2740_ == 0)
{
v___y_2728_ = v_isMeta_2695_;
goto v___jp_2727_;
}
else
{
uint8_t v___x_2741_; 
v___x_2741_ = 0;
v___y_2728_ = v___x_2741_;
goto v___jp_2727_;
}
}
v___jp_2727_:
{
lean_object* v_toImport_2729_; lean_object* v_module_2730_; lean_object* v___x_2731_; 
v_toImport_2729_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_ref(v_toImport_2729_);
lean_dec(v___x_2725_);
v_module_2730_ = lean_ctor_get(v_toImport_2729_, 0);
lean_inc(v_module_2730_);
lean_dec_ref(v_toImport_2729_);
lean_inc(v_declName_2694_);
v___x_2731_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2730_, v___y_2728_, v_declName_2694_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec_ref_known(v___x_2731_, 1);
v___x_2732_ = l_Lean_indirectModUseExt;
v___x_2733_ = lean_box(1);
v___x_2734_ = lean_box(0);
lean_inc_ref(v_env_2704_);
v___x_2735_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2699_, v___x_2732_, v_env_2704_, v___x_2733_, v___x_2734_);
v___x_2736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v___x_2735_, v_declName_2694_);
lean_dec(v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2737_; 
v___x_2737_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1));
v___y_2706_ = v___x_2737_;
goto v___jp_2705_;
}
else
{
lean_object* v_val_2738_; 
v_val_2738_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v___x_2736_, 1);
v___y_2706_ = v_val_2738_;
goto v___jp_2705_;
}
}
else
{
lean_dec_ref(v_env_2704_);
lean_dec(v_declName_2694_);
return v___x_2731_;
}
}
}
}
v___jp_2701_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
v___jp_2705_:
{
lean_object* v___x_2707_; size_t v_sz_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___x_2707_ = lean_box(0);
v_sz_2708_ = lean_array_size(v___y_2706_);
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v_env_2704_, v_declName_2694_, v___y_2706_, v_sz_2708_, v___x_2709_, v___x_2707_, v___y_2696_, v___y_2697_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v_env_2704_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v___x_2710_, 0);
lean_dec(v_unused_2718_);
v___x_2712_ = v___x_2710_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v___x_2710_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2707_);
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2707_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object* v_declName_2742_, lean_object* v_isMeta_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v_isMeta_boxed_2747_; lean_object* v_res_2748_; 
v_isMeta_boxed_2747_ = lean_unbox(v_isMeta_2743_);
v_res_2748_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v_declName_2742_, v_isMeta_boxed_2747_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2748_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object* v_a_2749_, lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
uint8_t v___x_2751_; 
v___x_2751_ = 0;
return v___x_2751_;
}
else
{
lean_object* v_head_2752_; lean_object* v_tail_2753_; uint8_t v___x_2754_; 
v_head_2752_ = lean_ctor_get(v_x_2750_, 0);
v_tail_2753_ = lean_ctor_get(v_x_2750_, 1);
v___x_2754_ = lean_name_eq(v_a_2749_, v_head_2752_);
if (v___x_2754_ == 0)
{
v_x_2750_ = v_tail_2753_;
goto _start;
}
else
{
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object* v_a_2756_, lean_object* v_x_2757_){
_start:
{
uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_res_2758_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v_a_2756_, v_x_2757_);
lean_dec(v_x_2757_);
lean_dec(v_a_2756_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object* v_t_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v_infoState_2764_; uint8_t v_enabled_2765_; 
v___x_2763_ = lean_st_ref_get(v___y_2761_);
v_infoState_2764_ = lean_ctor_get(v___x_2763_, 8);
lean_inc_ref(v_infoState_2764_);
lean_dec(v___x_2763_);
v_enabled_2765_ = lean_ctor_get_uint8(v_infoState_2764_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2764_);
if (v_enabled_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec_ref(v_t_2760_);
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v_infoState_2769_; lean_object* v_env_2770_; lean_object* v_nextMacroScope_2771_; lean_object* v_ngen_2772_; lean_object* v_auxDeclNGen_2773_; lean_object* v_traceState_2774_; lean_object* v_cache_2775_; lean_object* v_recordedDeps_2776_; lean_object* v_messages_2777_; lean_object* v_snapshotTasks_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2800_; 
v___x_2768_ = lean_st_ref_take(v___y_2761_);
v_infoState_2769_ = lean_ctor_get(v___x_2768_, 8);
v_env_2770_ = lean_ctor_get(v___x_2768_, 0);
v_nextMacroScope_2771_ = lean_ctor_get(v___x_2768_, 1);
v_ngen_2772_ = lean_ctor_get(v___x_2768_, 2);
v_auxDeclNGen_2773_ = lean_ctor_get(v___x_2768_, 3);
v_traceState_2774_ = lean_ctor_get(v___x_2768_, 4);
v_cache_2775_ = lean_ctor_get(v___x_2768_, 5);
v_recordedDeps_2776_ = lean_ctor_get(v___x_2768_, 6);
v_messages_2777_ = lean_ctor_get(v___x_2768_, 7);
v_snapshotTasks_2778_ = lean_ctor_get(v___x_2768_, 9);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2780_ = v___x_2768_;
v_isShared_2781_ = v_isSharedCheck_2800_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snapshotTasks_2778_);
lean_inc(v_infoState_2769_);
lean_inc(v_messages_2777_);
lean_inc(v_recordedDeps_2776_);
lean_inc(v_cache_2775_);
lean_inc(v_traceState_2774_);
lean_inc(v_auxDeclNGen_2773_);
lean_inc(v_ngen_2772_);
lean_inc(v_nextMacroScope_2771_);
lean_inc(v_env_2770_);
lean_dec(v___x_2768_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2800_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
uint8_t v_enabled_2782_; lean_object* v_assignment_2783_; lean_object* v_lazyAssignment_2784_; lean_object* v_trees_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2799_; 
v_enabled_2782_ = lean_ctor_get_uint8(v_infoState_2769_, sizeof(void*)*3);
v_assignment_2783_ = lean_ctor_get(v_infoState_2769_, 0);
v_lazyAssignment_2784_ = lean_ctor_get(v_infoState_2769_, 1);
v_trees_2785_ = lean_ctor_get(v_infoState_2769_, 2);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_infoState_2769_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2787_ = v_infoState_2769_;
v_isShared_2788_ = v_isSharedCheck_2799_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_trees_2785_);
lean_inc(v_lazyAssignment_2784_);
lean_inc(v_assignment_2783_);
lean_dec(v_infoState_2769_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2799_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = l_Lean_PersistentArray_push___redArg(v_trees_2785_, v_t_2760_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 2, v___x_2790_);
v___x_2792_ = v___x_2787_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_assignment_2783_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_lazyAssignment_2784_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v___x_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2798_, sizeof(void*)*3, v_enabled_2782_);
v___x_2792_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 8, v___x_2792_);
v___x_2794_ = v___x_2780_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2770_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_nextMacroScope_2771_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ngen_2772_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_auxDeclNGen_2773_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_traceState_2774_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v_cache_2775_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_recordedDeps_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v_messages_2777_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2797_, 9, v_snapshotTasks_2778_);
v___x_2794_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_st_ref_put(v___y_2761_, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2789_);
return v___x_2796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2801_, v___y_2802_);
lean_dec(v___y_2802_);
return v_res_2804_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_unsigned_to_nat(32u);
v___x_2806_ = lean_mk_empty_array_with_capacity(v___x_2805_);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2808_ = ((size_t)5ULL);
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = lean_unsigned_to_nat(32u);
v___x_2811_ = lean_mk_empty_array_with_capacity(v___x_2810_);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0);
v___x_2813_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2811_);
lean_ctor_set(v___x_2813_, 2, v___x_2809_);
lean_ctor_set(v___x_2813_, 3, v___x_2809_);
lean_ctor_set_usize(v___x_2813_, 4, v___x_2808_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object* v_t_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v_infoState_2819_; uint8_t v_enabled_2820_; 
v___x_2818_ = lean_st_ref_get(v___y_2816_);
v_infoState_2819_ = lean_ctor_get(v___x_2818_, 8);
lean_inc_ref(v_infoState_2819_);
lean_dec(v___x_2818_);
v_enabled_2820_ = lean_ctor_get_uint8(v_infoState_2819_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2819_);
if (v_enabled_2820_ == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v_t_2814_);
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_t_2814_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v___x_2824_, v___y_2816_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object* v_t_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v_t_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
if (lean_obj_tag(v_a_2831_) == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = l_List_reverse___redArg(v_a_2832_);
return v___x_2833_;
}
else
{
lean_object* v_head_2834_; lean_object* v_tail_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2844_; 
v_head_2834_ = lean_ctor_get(v_a_2831_, 0);
v_tail_2835_ = lean_ctor_get(v_a_2831_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2837_ = v_a_2831_;
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_tail_2835_);
lean_inc(v_head_2834_);
lean_dec(v_a_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = l_Lean_mkLevelParam(v_head_2834_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_a_2832_);
lean_ctor_set(v___x_2837_, 0, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_a_2832_);
v___x_2841_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v_a_2831_ = v_tail_2835_;
v_a_2832_ = v___x_2841_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object* v_constName_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v_env_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_st_ref_get(v___y_2847_);
v_env_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc_ref(v_env_2850_);
lean_dec(v___x_2849_);
v___x_2851_ = 0;
lean_inc(v_constName_2845_);
v___x_2852_ = l_Lean_Environment_findConstVal_x3f(v_env_2850_, v_constName_2845_, v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_2845_, v___y_2846_, v___y_2847_);
return v___x_2853_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_constName_2845_);
v_val_2854_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2852_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_val_2854_);
lean_dec(v___x_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 0);
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_val_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object* v_constName_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
lean_inc(v_constName_2867_);
v___x_2871_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2867_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2883_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_levelParams_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v_levelParams_2876_ = lean_ctor_get(v_a_2872_, 1);
lean_inc(v_levelParams_2876_);
lean_dec(v_a_2872_);
v___x_2877_ = lean_box(0);
v___x_2878_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(v_levelParams_2876_, v___x_2877_);
v___x_2879_ = l_Lean_mkConst(v_constName_2867_, v___x_2878_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2879_);
v___x_2881_ = v___x_2874_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_constName_2867_);
v_a_2884_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2871_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2871_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object* v_constName_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_constName_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object* v_stx_2897_, lean_object* v_n_2898_, lean_object* v_expectedType_x3f_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_n_2898_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v_stx_2897_);
v___x_2907_ = l_Lean_LocalContext_empty;
v___x_2908_ = 0;
v___x_2909_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2909_, 0, v___x_2906_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
lean_ctor_set(v___x_2909_, 2, v_expectedType_x3f_2899_);
lean_ctor_set(v___x_2909_, 3, v_a_2904_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*4, v___x_2908_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*4 + 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
v___x_2911_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v___x_2910_, v___y_2900_, v___y_2901_);
return v___x_2911_;
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_expectedType_x3f_2899_);
lean_dec(v_stx_2897_);
v_a_2912_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2903_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2903_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object* v_stx_2920_, lean_object* v_n_2921_, lean_object* v_expectedType_x3f_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_stx_2920_, v_n_2921_, v_expectedType_x3f_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2926_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0));
v___x_2929_ = l_Lean_stringToMessageData(v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object* v_attrName_2933_, lean_object* v_extraKinds_2934_, uint8_t v_builtin_2935_, lean_object* v_stx_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2940_; lean_object* v_env_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_st_ref_get(v_a_2938_);
v_env_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc_ref(v_env_2941_);
lean_dec(v___x_2940_);
v___x_2942_ = l_Lean_Attribute_Builtin_getIdent(v_stx_2936_, v_a_2937_, v_a_2938_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3020_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_3020_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3020_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___y_2949_; lean_object* v___y_2950_; 
v___x_2947_ = l_Lean_Syntax_getId(v_a_2943_);
if (v_builtin_2935_ == 0)
{
goto v___jp_2997_;
}
else
{
uint8_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = 0;
lean_inc(v___x_2947_);
lean_inc_ref(v_env_2941_);
v___x_3019_ = l_Lean_Environment_find_x3f(v_env_2941_, v___x_2947_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
goto v___jp_2997_;
}
else
{
lean_dec_ref_known(v___x_3019_, 1);
lean_dec_ref(v_env_2941_);
lean_dec(v_attrName_2933_);
v___y_2949_ = v_a_2937_;
v___y_2950_ = v_a_2938_;
goto v___jp_2948_;
}
}
v___jp_2948_:
{
lean_object* v___x_2951_; lean_object* v_env_2952_; uint8_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2951_ = lean_st_ref_get(v___y_2950_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_ref(v_env_2952_);
lean_dec(v___x_2951_);
v___x_2953_ = 1;
lean_inc(v___x_2947_);
v___x_2954_ = l_Lean_Environment_contains(v_env_2952_, v___x_2947_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2956_; 
lean_dec(v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2956_ = v___x_2945_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2947_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
else
{
uint8_t v___x_2958_; lean_object* v___x_2959_; 
lean_del_object(v___x_2945_);
v___x_2958_ = 0;
lean_inc(v___x_2947_);
v___x_2959_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v___x_2947_, v___x_2958_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2987_; 
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2959_, 0);
lean_dec(v_unused_2988_);
v___x_2961_ = v___x_2959_;
v_isShared_2962_ = v_isSharedCheck_2987_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v___x_2959_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2987_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v_infoState_2964_; uint8_t v_enabled_2965_; 
v___x_2963_ = lean_st_ref_get(v___y_2950_);
v_infoState_2964_ = lean_ctor_get(v___x_2963_, 8);
lean_inc_ref(v_infoState_2964_);
lean_dec(v___x_2963_);
v_enabled_2965_ = lean_ctor_get_uint8(v_infoState_2964_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2964_);
if (v_enabled_2965_ == 0)
{
lean_object* v___x_2967_; 
lean_dec(v_a_2943_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2947_);
v___x_2967_ = v___x_2961_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2947_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_del_object(v___x_2961_);
v___x_2969_ = lean_box(0);
lean_inc(v___x_2947_);
v___x_2970_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_a_2943_, v___x_2947_, v___x_2969_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2970_, 0);
lean_dec(v_unused_2978_);
v___x_2972_ = v___x_2970_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_dec(v___x_2970_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2947_);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2947_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v___x_2947_);
v_a_2979_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2970_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2970_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v___x_2947_);
lean_dec(v_a_2943_);
v_a_2989_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2959_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2959_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
v___jp_2997_:
{
uint8_t v___x_2998_; 
lean_inc(v___x_2947_);
v___x_2998_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2941_, v___x_2947_);
if (v___x_2998_ == 0)
{
uint8_t v___x_2999_; 
v___x_2999_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v___x_2947_, v_extraKinds_2934_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_del_object(v___x_2945_);
lean_dec(v_a_2943_);
v___x_3000_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1);
v___x_3001_ = l_Lean_MessageData_ofName(v_attrName_2933_);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = l_Lean_MessageData_ofName(v___x_2947_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3004_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3008_, v_a_2937_, v_a_2938_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
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
else
{
lean_dec(v_attrName_2933_);
v___y_2949_ = v_a_2937_;
v___y_2950_ = v_a_2938_;
goto v___jp_2948_;
}
}
else
{
lean_dec(v_attrName_2933_);
v___y_2949_ = v_a_2937_;
v___y_2950_ = v_a_2938_;
goto v___jp_2948_;
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_env_2941_);
lean_dec(v_attrName_2933_);
v_a_3021_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2942_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2942_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object* v_attrName_3029_, lean_object* v_extraKinds_3030_, lean_object* v_builtin_3031_, lean_object* v_stx_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
uint8_t v_builtin_boxed_3036_; lean_object* v_res_3037_; 
v_builtin_boxed_3036_ = lean_unbox(v_builtin_3031_);
v_res_3037_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(v_attrName_3029_, v_extraKinds_3030_, v_builtin_boxed_3036_, v_stx_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_extraKinds_3030_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object* v_00_u03b2_3038_, lean_object* v_m_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_3039_, v_a_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3042_, lean_object* v_m_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(v_00_u03b2_3042_, v_m_3043_, v_a_3044_);
lean_dec(v_a_3044_);
lean_dec_ref(v_m_3043_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object* v_t_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_3046_, v___y_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object* v_t_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(v_t_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3055_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_3057_, v_x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
uint8_t v_res_3063_; lean_object* v_r_3064_; 
v_res_3063_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(v_00_u03b2_3060_, v_x_3061_, v_x_3062_);
lean_dec_ref(v_x_3062_);
lean_dec_ref(v_x_3061_);
v_r_3064_ = lean_box(v_res_3063_);
return v_r_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3065_, lean_object* v_a_3066_, lean_object* v_x_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_3066_, v_x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3069_, lean_object* v_a_3070_, lean_object* v_x_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(v_00_u03b2_3069_, v_a_3070_, v_x_3071_);
lean_dec(v_x_3071_);
lean_dec(v_a_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3073_, lean_object* v_x_3074_, size_t v_x_3075_, lean_object* v_x_3076_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3074_, v_x_3075_, v_x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3078_, lean_object* v_x_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
size_t v_x_6265__boxed_3082_; uint8_t v_res_3083_; lean_object* v_r_3084_; 
v_x_6265__boxed_3082_ = lean_unbox_usize(v_x_3080_);
lean_dec(v_x_3080_);
v_res_3083_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3078_, v_x_3079_, v_x_6265__boxed_3082_, v_x_3081_);
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_x_3079_);
v_r_3084_ = lean_box(v_res_3083_);
return v_r_3084_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_3085_, lean_object* v_keys_3086_, lean_object* v_vals_3087_, lean_object* v_heq_3088_, lean_object* v_i_3089_, lean_object* v_k_3090_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_3086_, v_i_3089_, v_k_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3092_, lean_object* v_keys_3093_, lean_object* v_vals_3094_, lean_object* v_heq_3095_, lean_object* v_i_3096_, lean_object* v_k_3097_){
_start:
{
uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_res_3098_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_3092_, v_keys_3093_, v_vals_3094_, v_heq_3095_, v_i_3096_, v_k_3097_);
lean_dec_ref(v_k_3097_);
lean_dec_ref(v_vals_3094_);
lean_dec_ref(v_keys_3093_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(uint8_t v_builtin_3100_, lean_object* v_declName_3101_, lean_object* v_key_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_box(0);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_builtin_3108_, lean_object* v_declName_3109_, lean_object* v_key_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
uint8_t v_builtin_boxed_3114_; lean_object* v_res_3115_; 
v_builtin_boxed_3114_ = lean_unbox(v_builtin_3108_);
v_res_3115_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(v_builtin_boxed_3114_, v_declName_3109_, v_key_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v_key_3110_);
lean_dec(v_declName_3109_);
return v_res_3115_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = l_Lean_Fmt_headerKind;
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3127_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3131_ = l_Lean_Fmt_cmdsKind;
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3130_);
return v___x_3132_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3134_ = l_Lean_Fmt_moduleKind;
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3133_);
return v___x_3135_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3138_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed), 7, 2);
lean_closure_set(v___x_3138_, 0, v___x_3137_);
lean_closure_set(v___x_3138_, 1, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___f_3139_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3140_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3141_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3142_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3143_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3144_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3145_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v___x_3143_);
lean_ctor_set(v___x_3145_, 2, v___x_3142_);
lean_ctor_set(v___x_3145_, 3, v___x_3141_);
lean_ctor_set(v___x_3145_, 4, v___x_3140_);
lean_ctor_set(v___x_3145_, 5, v___f_3139_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3153_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3154_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3152_, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object* v_constName_3162_, lean_object* v_env_3163_, lean_object* v_opts_3164_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
v___x_3166_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3163_, v_opts_3164_, v___x_3165_, v_constName_3162_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object* v_constName_3167_, lean_object* v_env_3168_, lean_object* v_opts_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(v_constName_3167_, v_env_3168_, v_opts_3169_);
lean_dec_ref(v_opts_3169_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object* v_constName_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_env_3174_; lean_object* v_opts_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_env_3174_ = lean_ctor_get(v_a_3172_, 0);
v_opts_3175_ = lean_ctor_get(v_a_3172_, 1);
v___x_3176_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
lean_inc_ref(v_env_3174_);
v___x_3177_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3174_, v_opts_3175_, v___x_3176_, v_constName_3171_);
v___x_3178_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object* v_constName_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_constName_3179_, v_a_3180_);
lean_dec_ref(v_a_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_));
v___x_3187_ = lean_st_mk_ref(v___x_3186_);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object* v_f_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3193_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3194_ = lean_st_ref_take(v___x_3193_);
v___x_3195_ = lean_array_push(v___x_3194_, v_f_3191_);
v___x_3196_ = lean_st_ref_put(v___x_3193_, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object* v_f_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_Fmt_addBuiltinStickyTermFn(v_f_3198_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3201_){
_start:
{
lean_object* v_fst_3202_; 
v_fst_3202_ = lean_ctor_get(v_x_3201_, 0);
lean_inc(v_fst_3202_);
return v_fst_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3203_);
lean_dec_ref(v_x_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_box(0);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3207_);
lean_dec_ref(v_x_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3209_, lean_object* v_s_3210_){
_start:
{
lean_object* v_fst_3211_; lean_object* v___x_3212_; 
v_fst_3211_ = lean_ctor_get(v_s_3210_, 0);
lean_inc_n(v_fst_3211_, 3);
v___x_3212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3212_, 0, v_fst_3211_);
lean_ctor_set(v___x_3212_, 1, v_fst_3211_);
lean_ctor_set(v___x_3212_, 2, v_fst_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3213_, lean_object* v_s_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3213_, v_s_3214_);
lean_dec_ref(v_s_3214_);
lean_dec_ref(v_x_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v_fst_3220_; lean_object* v_snd_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3230_; 
v_fst_3218_ = lean_ctor_get(v_x_3216_, 0);
lean_inc(v_fst_3218_);
v_snd_3219_ = lean_ctor_get(v_x_3216_, 1);
lean_inc(v_snd_3219_);
lean_dec_ref(v_x_3216_);
v_fst_3220_ = lean_ctor_get(v_x_3217_, 0);
v_snd_3221_ = lean_ctor_get(v_x_3217_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_x_3217_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3223_ = v_x_3217_;
v_isShared_3224_ = v_isSharedCheck_3230_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_snd_3221_);
lean_inc(v_fst_3220_);
lean_dec(v_x_3217_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3230_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3225_ = lean_array_push(v_fst_3218_, v_fst_3220_);
v___x_3226_ = lean_array_push(v_snd_3219_, v_snd_3221_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3226_);
lean_ctor_set(v___x_3223_, 0, v___x_3225_);
v___x_3228_ = v___x_3223_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3231_, lean_object* v___x_3232_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_st_ref_get(v___x_3231_);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3232_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v___x_3234_);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3238_, v___x_3239_);
lean_dec(v___x_3239_);
lean_dec(v___x_3238_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(lean_object* v_as_3242_, size_t v_i_3243_, size_t v_stop_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_eq(v_i_3243_, v_stop_3244_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_array_uget_borrowed(v_as_3242_, v_i_3243_);
lean_inc(v___x_3249_);
v___x_3250_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v___x_3249_, v___y_3246_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = lean_array_push(v_b_3245_, v_a_3251_);
v___x_3253_ = ((size_t)1ULL);
v___x_3254_ = lean_usize_add(v_i_3243_, v___x_3253_);
v_i_3243_ = v___x_3254_;
v_b_3245_ = v___x_3252_;
goto _start;
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v_b_3245_);
v_a_3256_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3250_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3250_);
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
else
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_b_3245_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_3265_, lean_object* v_i_3266_, lean_object* v_stop_3267_, lean_object* v_b_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
size_t v_i_boxed_3271_; size_t v_stop_boxed_3272_; lean_object* v_res_3273_; 
v_i_boxed_3271_ = lean_unbox_usize(v_i_3266_);
lean_dec(v_i_3266_);
v_stop_boxed_3272_ = lean_unbox_usize(v_stop_3267_);
lean_dec(v_stop_3267_);
v_res_3273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v_as_3265_, v_i_boxed_3271_, v_stop_boxed_3272_, v_b_3268_, v___y_3269_);
lean_dec_ref(v___y_3269_);
lean_dec_ref(v_as_3265_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(lean_object* v_as_3274_, size_t v_i_3275_, size_t v_stop_3276_, lean_object* v_b_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_a_3281_; uint8_t v___x_3285_; 
v___x_3285_ = lean_usize_dec_eq(v_i_3275_, v_stop_3276_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = lean_array_uget_borrowed(v_as_3274_, v_i_3275_);
v___x_3288_ = lean_array_get_size(v___x_3287_);
v___x_3289_ = lean_nat_dec_lt(v___x_3286_, v___x_3288_);
if (v___x_3289_ == 0)
{
v_a_3281_ = v_b_3277_;
goto v___jp_3280_;
}
else
{
size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3288_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v___x_3287_, v___x_3290_, v___x_3291_, v_b_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v___x_3292_, 1);
v_a_3281_ = v_a_3293_;
goto v___jp_3280_;
}
else
{
return v___x_3292_;
}
}
}
else
{
lean_object* v___x_3294_; 
v___x_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3294_, 0, v_b_3277_);
return v___x_3294_;
}
v___jp_3280_:
{
size_t v___x_3282_; size_t v___x_3283_; 
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_add(v_i_3275_, v___x_3282_);
v_i_3275_ = v___x_3283_;
v_b_3277_ = v_a_3281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_3295_, lean_object* v_i_3296_, lean_object* v_stop_3297_, lean_object* v_b_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
size_t v_i_boxed_3301_; size_t v_stop_boxed_3302_; lean_object* v_res_3303_; 
v_i_boxed_3301_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_stop_boxed_3302_ = lean_unbox_usize(v_stop_3297_);
lean_dec(v_stop_3297_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3295_, v_i_boxed_3301_, v_stop_boxed_3302_, v_b_3298_, v___y_3299_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_as_3295_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3304_, lean_object* v___x_3305_, lean_object* v_as_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_a_3310_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3314_ = lean_st_ref_get(v___x_3305_);
v___x_3315_ = lean_array_get_size(v_as_3306_);
v___x_3316_ = lean_nat_dec_lt(v___x_3304_, v___x_3315_);
if (v___x_3316_ == 0)
{
v_a_3310_ = v___x_3314_;
goto v___jp_3309_;
}
else
{
size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = lean_usize_of_nat(v___x_3315_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3306_, v___x_3317_, v___x_3318_, v___x_3314_, v___y_3307_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_a_3310_ = v_a_3320_;
goto v___jp_3309_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3321_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3319_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3304_);
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v_a_3310_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v_as_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3329_, v___x_3330_, v_as_3331_, v___y_3332_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v_as_3331_);
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
return v_res_3334_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___f_3345_; 
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_3345_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_3345_, 0, v___x_3344_);
lean_closure_set(v___f_3345_, 1, v___x_3343_);
return v___f_3345_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; 
v___x_3346_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3347_ = lean_unsigned_to_nat(0u);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_3348_, 0, v___x_3347_);
lean_closure_set(v___f_3348_, 1, v___x_3346_);
return v___f_3348_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___f_3353_; lean_object* v___f_3354_; lean_object* v___f_3355_; lean_object* v___f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3349_ = 0;
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_box(2);
v___f_3352_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3353_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3354_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3355_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___f_3356_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3358_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___f_3356_);
lean_ctor_set(v___x_3358_, 2, v___f_3355_);
lean_ctor_set(v___x_3358_, 3, v___f_3354_);
lean_ctor_set(v___x_3358_, 4, v___f_3353_);
lean_ctor_set(v___x_3358_, 5, v___f_3352_);
lean_ctor_set(v___x_3358_, 6, v___x_3351_);
lean_ctor_set(v___x_3358_, 7, v___x_3350_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*8, v___x_3349_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*8 + 1, v___x_3349_);
return v___x_3358_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___f_3359_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3360_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___f_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3364_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_a_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_name_3367_, lean_object* v_decl_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3372_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3373_ = l_Lean_MessageData_ofName(v_name_3367_);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3376_, v___y_3369_, v___y_3370_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_name_3378_, lean_object* v_decl_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_name_3378_, v_decl_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v_decl_3379_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_addEntryFn_3384_, lean_object* v___x_3385_, lean_object* v_s_3386_){
_start:
{
lean_object* v_importedEntries_3387_; lean_object* v_state_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3396_; 
v_importedEntries_3387_ = lean_ctor_get(v_s_3386_, 0);
v_state_3388_ = lean_ctor_get(v_s_3386_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_s_3386_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3390_ = v_s_3386_;
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_state_3388_);
lean_inc(v_importedEntries_3387_);
lean_dec(v_s_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_state_3392_; lean_object* v___x_3394_; 
v_state_3392_ = lean_apply_2(v_addEntryFn_3384_, v_state_3388_, v___x_3385_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v_state_3392_);
v___x_3394_ = v___x_3390_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_importedEntries_3387_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_state_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3398_, lean_object* v___x_3399_, lean_object* v___x_3400_, lean_object* v___x_3401_, lean_object* v_name_3402_, lean_object* v_decl_3403_, lean_object* v_stx_3404_, uint8_t v_kind_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3404_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_dec_ref_known(v___x_3477_, 1);
if (v_builtin_3398_ == 0)
{
lean_object* v___x_3478_; 
lean_inc(v_decl_3403_);
lean_inc(v_name_3402_);
v___x_3478_ = l_Lean_ensureAttrDeclIsMeta(v_name_3402_, v_decl_3403_, v_kind_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_dec_ref_known(v___x_3478_, 1);
goto v___jp_3473_;
}
else
{
lean_dec(v_decl_3403_);
lean_dec(v_name_3402_);
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec(v___x_3399_);
return v___x_3478_;
}
}
else
{
goto v___jp_3473_;
}
}
else
{
lean_dec(v_decl_3403_);
lean_dec(v_name_3402_);
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec(v___x_3399_);
return v___x_3477_;
}
v___jp_3409_:
{
if (v_builtin_3398_ == 0)
{
lean_object* v___x_3412_; lean_object* v_env_3413_; lean_object* v___x_3414_; lean_object* v_env_3415_; lean_object* v_ref_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
v___x_3412_ = lean_st_ref_get(v___y_3411_);
v_env_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_env_3413_);
lean_dec(v___x_3412_);
v___x_3414_ = lean_st_ref_get(v___y_3411_);
v_env_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc_ref(v_env_3415_);
lean_dec(v___x_3414_);
v_ref_3416_ = lean_ctor_get(v___y_3410_, 2);
v___x_3417_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3410_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v_env_3415_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_inc(v_decl_3403_);
v___x_3419_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_decl_3403_, v___x_3418_);
lean_dec_ref_known(v___x_3418_, 2);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v_toEnvExtension_3422_; lean_object* v_addEntryFn_3423_; lean_object* v_asyncMode_3424_; uint8_t v_logWrites_3425_; lean_object* v___x_3426_; lean_object* v___f_3427_; uint8_t v___x_3428_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3422_ = lean_ctor_get(v___x_3421_, 0);
v_addEntryFn_3423_ = lean_ctor_get(v___x_3421_, 3);
v_asyncMode_3424_ = lean_ctor_get(v_toEnvExtension_3422_, 2);
v_logWrites_3425_ = lean_ctor_get_uint8(v_toEnvExtension_3422_, sizeof(void*)*6);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v_decl_3403_);
lean_ctor_set(v___x_3426_, 1, v_a_3420_);
lean_inc(v_addEntryFn_3423_);
v___f_3427_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_3427_, 0, v_addEntryFn_3423_);
lean_closure_set(v___f_3427_, 1, v___x_3426_);
v___x_3428_ = 1;
if (v_logWrites_3425_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_inc_ref(v_toEnvExtension_3422_);
v___x_3429_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3422_, v_env_3413_, v___f_3427_, v_asyncMode_3424_, v___x_3399_, v___x_3428_);
v___x_3430_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3429_, v___y_3411_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_inc_ref_n(v_toEnvExtension_3422_, 2);
v___x_3431_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3422_, v_env_3413_);
lean_dec_ref(v_env_3413_);
v___x_3432_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3422_, v___x_3431_, v___f_3427_, v_asyncMode_3424_, v___x_3399_, v___x_3428_);
v___x_3433_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3432_, v___y_3411_);
return v___x_3433_;
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_env_3413_);
lean_dec(v_decl_3403_);
lean_dec(v___x_3399_);
v_a_3434_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3436_ = v___x_3419_;
v_isShared_3437_ = v_isSharedCheck_3445_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3419_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3445_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3438_ = lean_io_error_to_string(v_a_3434_);
v___x_3439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
v___x_3440_ = l_Lean_MessageData_ofFormat(v___x_3439_);
lean_inc(v_ref_3416_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_ref_3416_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3441_);
v___x_3443_ = v___x_3436_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec(v___x_3399_);
v___x_3446_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3447_ = l_Lean_Name_mkStr3(v___x_3400_, v___x_3401_, v___x_3446_);
v___x_3448_ = lean_box(0);
v___x_3449_ = l_Lean_mkConst(v___x_3447_, v___x_3448_);
lean_inc(v_decl_3403_);
v___x_3450_ = l_Lean_mkConst(v_decl_3403_, v___x_3448_);
v___x_3451_ = l_Lean_Expr_app___override(v___x_3449_, v___x_3450_);
v___x_3452_ = l_Lean_declareBuiltin(v_decl_3403_, v___x_3451_, v___y_3410_, v___y_3411_);
return v___x_3452_;
}
}
v___jp_3453_:
{
lean_object* v___x_3456_; 
lean_inc(v_decl_3403_);
v___x_3456_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_3403_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_ConstantInfo_type(v_a_3457_);
lean_dec(v_a_3457_);
v___x_3459_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0));
lean_inc_ref(v___x_3401_);
lean_inc_ref(v___x_3400_);
v___x_3460_ = l_Lean_Name_mkStr3(v___x_3400_, v___x_3401_, v___x_3459_);
v___x_3461_ = l_Lean_Expr_isConstOf(v___x_3458_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec(v___x_3399_);
v___x_3462_ = lean_box(0);
v___x_3463_ = l_Lean_mkConst(v___x_3460_, v___x_3462_);
v___x_3464_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_name_3402_, v_decl_3403_, v___x_3458_, v___x_3463_, v___y_3454_, v___y_3455_);
return v___x_3464_;
}
else
{
lean_dec(v___x_3460_);
lean_dec_ref(v___x_3458_);
lean_dec(v_name_3402_);
v___y_3410_ = v___y_3454_;
v___y_3411_ = v___y_3455_;
goto v___jp_3409_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_decl_3403_);
lean_dec(v_name_3402_);
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec(v___x_3399_);
v_a_3465_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3456_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3456_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
v___jp_3473_:
{
uint8_t v___x_3474_; uint8_t v___x_3475_; 
v___x_3474_ = 0;
v___x_3475_ = l_Lean_instBEqAttributeKind_beq(v_kind_3405_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec(v_decl_3403_);
lean_dec_ref(v___x_3401_);
lean_dec_ref(v___x_3400_);
lean_dec(v___x_3399_);
v___x_3476_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_3402_, v_kind_3405_, v___y_3406_, v___y_3407_);
return v___x_3476_;
}
else
{
v___y_3454_ = v___y_3406_;
v___y_3455_ = v___y_3407_;
goto v___jp_3453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3479_, lean_object* v___x_3480_, lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v_name_3483_, lean_object* v_decl_3484_, lean_object* v_stx_3485_, lean_object* v_kind_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
uint8_t v_builtin_boxed_3490_; uint8_t v_kind_boxed_3491_; lean_object* v_res_3492_; 
v_builtin_boxed_3490_ = lean_unbox(v_builtin_3479_);
v_kind_boxed_3491_ = lean_unbox(v_kind_3486_);
v_res_3492_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3490_, v___x_3480_, v___x_3481_, v___x_3482_, v_name_3483_, v_decl_3484_, v_stx_3485_, v_kind_boxed_3491_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3507_, lean_object* v_name_3508_){
_start:
{
lean_object* v___f_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; lean_object* v___y_3518_; 
lean_inc_n(v_name_3508_, 2);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3510_, 0, v_name_3508_);
v___x_3511_ = lean_box(0);
v___x_3512_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0));
v___x_3513_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1));
v___x_3514_ = lean_box(v_builtin_3507_);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_3515_, 0, v___x_3514_);
lean_closure_set(v___f_3515_, 1, v___x_3511_);
lean_closure_set(v___f_3515_, 2, v___x_3512_);
lean_closure_set(v___f_3515_, 3, v___x_3513_);
lean_closure_set(v___f_3515_, 4, v_name_3508_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
if (v_builtin_3507_ == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___y_3518_ = v___x_3525_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3526_; 
v___x_3526_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___y_3518_ = v___x_3526_;
goto v___jp_3517_;
}
v___jp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3519_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
lean_inc_ref(v___y_3518_);
v___x_3520_ = lean_string_append(v___y_3518_, v___x_3519_);
v___x_3521_ = 1;
v___x_3522_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3522_, 0, v___x_3516_);
lean_ctor_set(v___x_3522_, 1, v_name_3508_);
lean_ctor_set(v___x_3522_, 2, v___x_3520_);
lean_ctor_set_uint8(v___x_3522_, sizeof(void*)*3, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___f_3515_);
lean_ctor_set(v___x_3523_, 2, v___f_3510_);
v___x_3524_ = l_Lean_registerBuiltinAttribute(v___x_3523_);
return v___x_3524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3527_, lean_object* v_name_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v_builtin_boxed_3530_; lean_object* v_res_3531_; 
v_builtin_boxed_3530_ = lean_unbox(v_builtin_3527_);
v_res_3531_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3530_, v_name_3528_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = 1;
v___x_3540_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3541_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3539_, v___x_3540_);
if (lean_obj_tag(v___x_3541_) == 0)
{
uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3541_, 1);
v___x_3542_ = 0;
v___x_3543_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3544_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3542_, v___x_3543_);
return v___x_3544_;
}
else
{
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
return v_res_3546_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object* v_t_3547_, lean_object* v_as_3548_, size_t v_i_3549_, size_t v_stop_3550_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = lean_usize_dec_eq(v_i_3549_, v_stop_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_158__overap_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_158__overap_3552_ = lean_array_uget_borrowed(v_as_3548_, v_i_3549_);
lean_inc(v___x_158__overap_3552_);
lean_inc(v_t_3547_);
v___x_3553_ = lean_apply_1(v___x_158__overap_3552_, v_t_3547_);
v___x_3554_ = lean_unbox(v___x_3553_);
if (v___x_3554_ == 0)
{
size_t v___x_3555_; size_t v___x_3556_; 
v___x_3555_ = ((size_t)1ULL);
v___x_3556_ = lean_usize_add(v_i_3549_, v___x_3555_);
v_i_3549_ = v___x_3556_;
goto _start;
}
else
{
uint8_t v___x_3558_; 
lean_dec(v_t_3547_);
v___x_3558_ = lean_unbox(v___x_3553_);
return v___x_3558_;
}
}
else
{
uint8_t v___x_3559_; 
lean_dec(v_t_3547_);
v___x_3559_ = 0;
return v___x_3559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object* v_t_3560_, lean_object* v_as_3561_, lean_object* v_i_3562_, lean_object* v_stop_3563_){
_start:
{
size_t v_i_boxed_3564_; size_t v_stop_boxed_3565_; uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_i_boxed_3564_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_stop_boxed_3565_ = lean_unbox_usize(v_stop_3563_);
lean_dec(v_stop_3563_);
v_res_3566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3560_, v_as_3561_, v_i_boxed_3564_, v_stop_boxed_3565_);
lean_dec_ref(v_as_3561_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object* v_env_3568_, lean_object* v_t_3569_){
_start:
{
lean_object* v___x_3570_; lean_object* v_toEnvExtension_3571_; lean_object* v_asyncMode_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v_snd_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3570_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3571_ = lean_ctor_get(v___x_3570_, 0);
v_asyncMode_3572_ = lean_ctor_get(v_toEnvExtension_3571_, 2);
v___x_3573_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_3574_ = lean_box(0);
v___x_3575_ = 0;
v___x_3576_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3573_, v___x_3570_, v_env_3568_, v_asyncMode_3572_, v___x_3574_, v___x_3575_);
v_snd_3577_ = lean_ctor_get(v___x_3576_, 1);
lean_inc(v_snd_3577_);
lean_dec(v___x_3576_);
v___x_3578_ = lean_unsigned_to_nat(0u);
v___x_3579_ = lean_array_get_size(v_snd_3577_);
v___x_3580_ = lean_nat_dec_lt(v___x_3578_, v___x_3579_);
if (v___x_3580_ == 0)
{
lean_dec(v_snd_3577_);
lean_dec(v_t_3569_);
return v___x_3580_;
}
else
{
if (v___x_3580_ == 0)
{
lean_dec(v_snd_3577_);
lean_dec(v_t_3569_);
return v___x_3580_;
}
else
{
size_t v___x_3581_; size_t v___x_3582_; uint8_t v___x_3583_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3579_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3569_, v_snd_3577_, v___x_3581_, v___x_3582_);
lean_dec(v_snd_3577_);
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object* v_env_3584_, lean_object* v_t_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_3584_, v_t_3585_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(uint8_t v_x_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_box(v_x_3588_);
v___x_3590_ = lean_obj_tag_nat(v___x_3589_);
lean_dec(v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl___boxed(lean_object* v_x_3591_){
_start:
{
uint8_t v_x_4__boxed_3592_; lean_object* v_res_3593_; 
v_x_4__boxed_3592_ = lean_unbox(v_x_3591_);
v_res_3593_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(v_x_4__boxed_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object* v_k_3594_){
_start:
{
lean_inc(v_k_3594_);
return v_k_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object* v_k_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(v_k_3595_);
lean_dec(v_k_3595_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object* v_motive_3597_, lean_object* v_ctorIdx_3598_, uint8_t v_t_3599_, lean_object* v_h_3600_, lean_object* v_k_3601_){
_start:
{
lean_inc(v_k_3601_);
return v_k_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object* v_motive_3602_, lean_object* v_ctorIdx_3603_, lean_object* v_t_3604_, lean_object* v_h_3605_, lean_object* v_k_3606_){
_start:
{
uint8_t v_t_boxed_3607_; lean_object* v_res_3608_; 
v_t_boxed_3607_ = lean_unbox(v_t_3604_);
v_res_3608_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim(v_motive_3602_, v_ctorIdx_3603_, v_t_boxed_3607_, v_h_3605_, v_k_3606_);
lean_dec(v_k_3606_);
lean_dec(v_ctorIdx_3603_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object* v_left_3609_){
_start:
{
lean_inc(v_left_3609_);
return v_left_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object* v_left_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(v_left_3610_);
lean_dec(v_left_3610_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object* v_motive_3612_, uint8_t v_t_3613_, lean_object* v_h_3614_, lean_object* v_left_3615_){
_start:
{
lean_inc(v_left_3615_);
return v_left_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object* v_motive_3616_, lean_object* v_t_3617_, lean_object* v_h_3618_, lean_object* v_left_3619_){
_start:
{
uint8_t v_t_boxed_3620_; lean_object* v_res_3621_; 
v_t_boxed_3620_ = lean_unbox(v_t_3617_);
v_res_3621_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim(v_motive_3616_, v_t_boxed_3620_, v_h_3618_, v_left_3619_);
lean_dec(v_left_3619_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object* v_right_3622_){
_start:
{
lean_inc(v_right_3622_);
return v_right_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object* v_right_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(v_right_3623_);
lean_dec(v_right_3623_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object* v_motive_3625_, uint8_t v_t_3626_, lean_object* v_h_3627_, lean_object* v_right_3628_){
_start:
{
lean_inc(v_right_3628_);
return v_right_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object* v_motive_3629_, lean_object* v_t_3630_, lean_object* v_h_3631_, lean_object* v_right_3632_){
_start:
{
uint8_t v_t_boxed_3633_; lean_object* v_res_3634_; 
v_t_boxed_3633_ = lean_unbox(v_t_3630_);
v_res_3634_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim(v_motive_3629_, v_t_boxed_3633_, v_h_3631_, v_right_3632_);
lean_dec(v_right_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object* v_middle_3635_){
_start:
{
lean_inc(v_middle_3635_);
return v_middle_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object* v_middle_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(v_middle_3636_);
lean_dec(v_middle_3636_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object* v_motive_3638_, uint8_t v_t_3639_, lean_object* v_h_3640_, lean_object* v_middle_3641_){
_start:
{
lean_inc(v_middle_3641_);
return v_middle_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object* v_motive_3642_, lean_object* v_t_3643_, lean_object* v_h_3644_, lean_object* v_middle_3645_){
_start:
{
uint8_t v_t_boxed_3646_; lean_object* v_res_3647_; 
v_t_boxed_3646_ = lean_unbox(v_t_3643_);
v_res_3647_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim(v_motive_3642_, v_t_boxed_3646_, v_h_3644_, v_middle_3645_);
lean_dec(v_middle_3645_);
return v_res_3647_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default(void){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = 0;
return v___x_3648_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity(void){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = 0;
return v___x_3649_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t v_x_3650_, uint8_t v_y_3651_){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3652_ = lean_box(v_x_3650_);
v___x_3653_ = lean_obj_tag_nat(v___x_3652_);
lean_dec(v___x_3652_);
v___x_3654_ = lean_box(v_y_3651_);
v___x_3655_ = lean_obj_tag_nat(v___x_3654_);
lean_dec(v___x_3654_);
v___x_3656_ = lean_nat_dec_eq(v___x_3653_, v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object* v_x_3657_, lean_object* v_y_3658_){
_start:
{
uint8_t v_x_24__boxed_3659_; uint8_t v_y_25__boxed_3660_; uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_x_24__boxed_3659_ = lean_unbox(v_x_3657_);
v_y_25__boxed_3660_ = lean_unbox(v_y_3658_);
v_res_3661_ = l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(v_x_24__boxed_3659_, v_y_25__boxed_3660_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object* v_x_3669_, lean_object* v_x_3670_){
_start:
{
lean_object* v_prec_3671_; lean_object* v_lhsPrec_3672_; lean_object* v_rhsPrec_3673_; lean_object* v_prec_3674_; lean_object* v_lhsPrec_3675_; lean_object* v_rhsPrec_3676_; uint8_t v___x_3677_; 
v_prec_3671_ = lean_ctor_get(v_x_3669_, 0);
v_lhsPrec_3672_ = lean_ctor_get(v_x_3669_, 1);
v_rhsPrec_3673_ = lean_ctor_get(v_x_3669_, 2);
v_prec_3674_ = lean_ctor_get(v_x_3670_, 0);
v_lhsPrec_3675_ = lean_ctor_get(v_x_3670_, 1);
v_rhsPrec_3676_ = lean_ctor_get(v_x_3670_, 2);
v___x_3677_ = lean_nat_dec_eq(v_prec_3671_, v_prec_3674_);
if (v___x_3677_ == 0)
{
return v___x_3677_;
}
else
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_nat_dec_eq(v_lhsPrec_3672_, v_lhsPrec_3675_);
if (v___x_3678_ == 0)
{
return v___x_3678_;
}
else
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_nat_dec_eq(v_rhsPrec_3673_, v_rhsPrec_3676_);
return v___x_3679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
uint8_t v_res_3682_; lean_object* v_r_3683_; 
v_res_3682_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_x_3680_, v_x_3681_);
lean_dec_ref(v_x_3681_);
lean_dec_ref(v_x_3680_);
v_r_3683_ = lean_box(v_res_3682_);
return v_r_3683_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_unsigned_to_nat(16u);
v___x_3688_ = lean_mk_array(v___x_3687_, v___x_3686_);
return v___x_3688_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v___x_3689_);
return v___x_3691_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; 
v___x_3692_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1);
v___x_3693_ = lean_box(0);
v___x_3694_ = 0;
v___x_3695_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3692_);
lean_ctor_set_uint8(v___x_3695_, sizeof(void*)*2, v___x_3694_);
lean_ctor_set_uint8(v___x_3695_, sizeof(void*)*2 + 1, v___x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default(void){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2);
return v___x_3696_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation(void){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Fmt_instInhabitedInfixOperation_default;
return v___x_3697_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object* v_x_3698_, lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 0)
{
if (lean_obj_tag(v_x_3699_) == 0)
{
uint8_t v___x_3700_; 
v___x_3700_ = 1;
return v___x_3700_;
}
else
{
uint8_t v___x_3701_; 
v___x_3701_ = 0;
return v___x_3701_;
}
}
else
{
if (lean_obj_tag(v_x_3699_) == 0)
{
uint8_t v___x_3702_; 
v___x_3702_ = 0;
return v___x_3702_;
}
else
{
lean_object* v_val_3703_; lean_object* v_val_3704_; uint8_t v___x_3705_; 
v_val_3703_ = lean_ctor_get(v_x_3698_, 0);
v_val_3704_ = lean_ctor_get(v_x_3699_, 0);
v___x_3705_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_3703_, v_val_3704_);
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object* v_x_3706_, lean_object* v_x_3707_){
_start:
{
uint8_t v_res_3708_; lean_object* v_r_3709_; 
v_res_3708_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_x_3706_, v_x_3707_);
lean_dec(v_x_3707_);
lean_dec(v_x_3706_);
v_r_3709_ = lean_box(v_res_3708_);
return v_r_3709_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_3710_, lean_object* v_x_3711_){
_start:
{
if (lean_obj_tag(v_x_3710_) == 0)
{
if (lean_obj_tag(v_x_3711_) == 0)
{
uint8_t v___x_3712_; 
v___x_3712_ = 1;
return v___x_3712_;
}
else
{
uint8_t v___x_3713_; 
v___x_3713_ = 0;
return v___x_3713_;
}
}
else
{
if (lean_obj_tag(v_x_3711_) == 0)
{
uint8_t v___x_3714_; 
v___x_3714_ = 0;
return v___x_3714_;
}
else
{
uint8_t v___x_3715_; 
v___x_3715_ = 1;
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
uint8_t v_res_3718_; lean_object* v_r_3719_; 
v_res_3718_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v_x_3716_, v_x_3717_);
lean_dec(v_x_3717_);
lean_dec(v_x_3716_);
v_r_3719_ = lean_box(v_res_3718_);
return v_r_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_m_u2082_3723_, lean_object* v___x_3724_, lean_object* v___x_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___y_3731_; uint8_t v___x_3744_; 
v___x_3728_ = lean_box(0);
v___x_3729_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v___x_3744_ = lean_nat_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3744_ == 0)
{
uint8_t v___x_3745_; 
v___x_3745_ = 1;
v___y_3731_ = v___x_3745_;
goto v___jp_3730_;
}
else
{
uint8_t v___x_3746_; 
v___x_3746_ = 0;
v___y_3731_ = v___x_3746_;
goto v___jp_3730_;
}
v___jp_3730_:
{
if (lean_obj_tag(v_a_3726_) == 0)
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_a_3727_);
return v___x_3732_;
}
else
{
lean_object* v_key_3733_; lean_object* v_value_3734_; lean_object* v_tail_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
lean_dec_ref(v_a_3727_);
v_key_3733_ = lean_ctor_get(v_a_3726_, 0);
v_value_3734_ = lean_ctor_get(v_a_3726_, 1);
v_tail_3735_ = lean_ctor_get(v_a_3726_, 2);
v___x_3736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_u2082_3723_, v_key_3733_);
lean_inc(v_value_3734_);
v___x_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3737_, 0, v_value_3734_);
v___x_3738_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v___x_3736_, v___x_3737_);
lean_dec_ref_known(v___x_3737_, 1);
lean_dec(v___x_3736_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3739_ = lean_box(v___y_3731_);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set(v___x_3741_, 1, v___x_3728_);
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
return v___x_3742_;
}
else
{
v_a_3726_ = v_tail_3735_;
v_a_3727_ = v___x_3729_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_m_u2082_3747_, lean_object* v___x_3748_, lean_object* v___x_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3747_, v___x_3748_, v___x_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3750_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_m_u2082_3747_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_m_u2082_3753_, lean_object* v___x_3754_, lean_object* v___x_3755_, lean_object* v_as_3756_, size_t v_sz_3757_, size_t v_i_3758_, lean_object* v_b_3759_){
_start:
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_usize_dec_lt(v_i_3758_, v_sz_3757_);
if (v___x_3760_ == 0)
{
return v_b_3759_;
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_array_uget_borrowed(v_as_3756_, v_i_3758_);
v___x_3762_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3753_, v___x_3754_, v___x_3755_, v_a_3761_, v_b_3759_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
return v_a_3763_;
}
else
{
lean_object* v_a_3764_; size_t v___x_3765_; size_t v___x_3766_; 
v_a_3764_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3762_, 1);
v___x_3765_ = ((size_t)1ULL);
v___x_3766_ = lean_usize_add(v_i_3758_, v___x_3765_);
v_i_3758_ = v___x_3766_;
v_b_3759_ = v_a_3764_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_m_u2082_3768_, lean_object* v___x_3769_, lean_object* v___x_3770_, lean_object* v_as_3771_, lean_object* v_sz_3772_, lean_object* v_i_3773_, lean_object* v_b_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3772_);
lean_dec(v_sz_3772_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3773_);
lean_dec(v_i_3773_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3768_, v___x_3769_, v___x_3770_, v_as_3771_, v_sz_boxed_3775_, v_i_boxed_3776_, v_b_3774_);
lean_dec_ref(v_as_3771_);
lean_dec(v___x_3770_);
lean_dec(v___x_3769_);
lean_dec_ref(v_m_u2082_3768_);
return v_res_3777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object* v_m_u2081_3778_, lean_object* v_m_u2082_3779_){
_start:
{
lean_object* v_size_3780_; lean_object* v_buckets_3781_; lean_object* v_size_3782_; uint8_t v___x_3783_; 
v_size_3780_ = lean_ctor_get(v_m_u2081_3778_, 0);
v_buckets_3781_ = lean_ctor_get(v_m_u2081_3778_, 1);
v_size_3782_ = lean_ctor_get(v_m_u2082_3779_, 0);
v___x_3783_ = lean_nat_dec_eq(v_size_3780_, v_size_3782_);
if (v___x_3783_ == 0)
{
return v___x_3783_;
}
else
{
lean_object* v___x_3784_; size_t v_sz_3785_; size_t v___x_3786_; lean_object* v___x_3787_; lean_object* v_fst_3788_; 
v___x_3784_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v_sz_3785_ = lean_array_size(v_buckets_3781_);
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3779_, v_size_3780_, v_size_3782_, v_buckets_3781_, v_sz_3785_, v___x_3786_, v___x_3784_);
v_fst_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_fst_3788_);
lean_dec_ref(v___x_3787_);
if (lean_obj_tag(v_fst_3788_) == 0)
{
return v___x_3783_;
}
else
{
lean_object* v_val_3789_; uint8_t v___x_3790_; 
v_val_3789_ = lean_ctor_get(v_fst_3788_, 0);
lean_inc(v_val_3789_);
lean_dec_ref_known(v_fst_3788_, 1);
v___x_3790_ = lean_unbox(v_val_3789_);
lean_dec(v_val_3789_);
return v___x_3790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_m_u2081_3791_, lean_object* v_m_u2082_3792_){
_start:
{
uint8_t v_res_3793_; lean_object* v_r_3794_; 
v_res_3793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3791_, v_m_u2082_3792_);
lean_dec_ref(v_m_u2082_3792_);
lean_dec_ref(v_m_u2081_3791_);
v_r_3794_ = lean_box(v_res_3793_);
return v_r_3794_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object* v_m_u2081_3795_, lean_object* v_m_u2082_3796_){
_start:
{
uint8_t v___x_3797_; 
v___x_3797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3795_, v_m_u2082_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object* v_m_u2081_3798_, lean_object* v_m_u2082_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(v_m_u2081_3798_, v_m_u2082_3799_);
lean_dec_ref(v_m_u2082_3799_);
lean_dec_ref(v_m_u2081_3798_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object* v_m_u2081_3802_, lean_object* v_m_u2082_3803_){
_start:
{
uint8_t v___x_3804_; 
v___x_3804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3802_, v_m_u2082_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object* v_m_u2081_3805_, lean_object* v_m_u2082_3806_){
_start:
{
uint8_t v_res_3807_; lean_object* v_r_3808_; 
v_res_3807_ = l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(v_m_u2081_3805_, v_m_u2082_3806_);
lean_dec_ref(v_m_u2082_3806_);
lean_dec_ref(v_m_u2081_3805_);
v_r_3808_ = lean_box(v_res_3807_);
return v_r_3808_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object* v_m_u2081_3809_, lean_object* v_m_u2082_3810_){
_start:
{
uint8_t v___x_3811_; 
v___x_3811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3809_, v_m_u2082_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object* v_m_u2081_3812_, lean_object* v_m_u2082_3813_){
_start:
{
uint8_t v_res_3814_; lean_object* v_r_3815_; 
v_res_3814_ = l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(v_m_u2081_3812_, v_m_u2082_3813_);
lean_dec_ref(v_m_u2082_3813_);
lean_dec_ref(v_m_u2081_3812_);
v_r_3815_ = lean_box(v_res_3814_);
return v_r_3815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object* v_x_3816_, lean_object* v_x_3817_){
_start:
{
uint8_t v_sparse_3818_; uint8_t v_separateFinalOperand_3819_; lean_object* v_precs_x3f_3820_; lean_object* v_extendedChainKinds_3821_; uint8_t v_sparse_3822_; uint8_t v_separateFinalOperand_3823_; lean_object* v_precs_x3f_3824_; lean_object* v_extendedChainKinds_3825_; 
v_sparse_3818_ = lean_ctor_get_uint8(v_x_3816_, sizeof(void*)*2);
v_separateFinalOperand_3819_ = lean_ctor_get_uint8(v_x_3816_, sizeof(void*)*2 + 1);
v_precs_x3f_3820_ = lean_ctor_get(v_x_3816_, 0);
v_extendedChainKinds_3821_ = lean_ctor_get(v_x_3816_, 1);
v_sparse_3822_ = lean_ctor_get_uint8(v_x_3817_, sizeof(void*)*2);
v_separateFinalOperand_3823_ = lean_ctor_get_uint8(v_x_3817_, sizeof(void*)*2 + 1);
v_precs_x3f_3824_ = lean_ctor_get(v_x_3817_, 0);
v_extendedChainKinds_3825_ = lean_ctor_get(v_x_3817_, 1);
if (v_sparse_3822_ == 0)
{
if (v_sparse_3818_ == 0)
{
goto v___jp_3829_;
}
else
{
return v_sparse_3822_;
}
}
else
{
if (v_sparse_3818_ == 0)
{
return v_sparse_3818_;
}
else
{
goto v___jp_3829_;
}
}
v___jp_3826_:
{
uint8_t v___x_3827_; 
v___x_3827_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_precs_x3f_3820_, v_precs_x3f_3824_);
if (v___x_3827_ == 0)
{
return v___x_3827_;
}
else
{
uint8_t v___x_3828_; 
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_extendedChainKinds_3821_, v_extendedChainKinds_3825_);
return v___x_3828_;
}
}
v___jp_3829_:
{
if (v_separateFinalOperand_3823_ == 0)
{
if (v_separateFinalOperand_3819_ == 0)
{
goto v___jp_3826_;
}
else
{
return v_separateFinalOperand_3823_;
}
}
else
{
if (v_separateFinalOperand_3819_ == 0)
{
return v_separateFinalOperand_3819_;
}
else
{
goto v___jp_3826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object* v_x_3830_, lean_object* v_x_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l_Lean_Fmt_instBEqInfixOperation_beq(v_x_3830_, v_x_3831_);
lean_dec_ref(v_x_3831_);
lean_dec_ref(v_x_3830_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3865_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3866_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3864_, v___x_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2____boxed(lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3898_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3899_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3897_, v___x_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2____boxed(lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(lean_object* v_x_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_obj_tag_nat(v_x_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl___boxed(lean_object* v_x_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(v_x_3904_);
lean_dec_ref(v_x_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object* v_t_3906_, lean_object* v_k_3907_){
_start:
{
if (lean_obj_tag(v_t_3906_) == 0)
{
lean_object* v_group_3908_; lean_object* v___x_3909_; 
v_group_3908_ = lean_ctor_get(v_t_3906_, 0);
lean_inc_ref(v_group_3908_);
lean_dec_ref_known(v_t_3906_, 1);
v___x_3909_ = lean_apply_1(v_k_3907_, v_group_3908_);
return v___x_3909_;
}
else
{
lean_object* v_lhs_3910_; lean_object* v_rhs_3911_; lean_object* v___x_3912_; 
v_lhs_3910_ = lean_ctor_get(v_t_3906_, 0);
lean_inc(v_lhs_3910_);
v_rhs_3911_ = lean_ctor_get(v_t_3906_, 1);
lean_inc(v_rhs_3911_);
lean_dec_ref_known(v_t_3906_, 2);
v___x_3912_ = lean_apply_2(v_k_3907_, v_lhs_3910_, v_rhs_3911_);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object* v_motive_3913_, lean_object* v_ctorIdx_3914_, lean_object* v_t_3915_, lean_object* v_h_3916_, lean_object* v_k_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3915_, v_k_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object* v_motive_3919_, lean_object* v_ctorIdx_3920_, lean_object* v_t_3921_, lean_object* v_h_3922_, lean_object* v_k_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_Fmt_QuantifierBinders_ctorElim(v_motive_3919_, v_ctorIdx_3920_, v_t_3921_, v_h_3922_, v_k_3923_);
lean_dec(v_ctorIdx_3920_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object* v_t_3925_, lean_object* v_binders_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3925_, v_binders_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object* v_motive_3928_, lean_object* v_t_3929_, lean_object* v_h_3930_, lean_object* v_binders_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3929_, v_binders_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object* v_t_3933_, lean_object* v_pred_3934_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3933_, v_pred_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object* v_motive_3936_, lean_object* v_t_3937_, lean_object* v_h_3938_, lean_object* v_pred_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3937_, v_pred_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3970_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3971_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3969_, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2____boxed(lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
return v_res_3973_;
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
