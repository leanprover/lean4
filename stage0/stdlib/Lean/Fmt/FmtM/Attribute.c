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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind_default(void){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind(void){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = lean_unsigned_to_nat(16u);
v___x_259_ = lean_mk_array(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = l_Lean_ShareCommon_objectFactory;
v___x_266_ = l_ShareCommon_mkStateImpl(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_267_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__0, &l_Lean_Fmt_instInhabitedState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__0);
v___x_270_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
v___x_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
lean_ctor_set(v___x_271_, 3, v___x_267_);
lean_ctor_set(v___x_271_, 4, v___x_267_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__1, &l_Lean_Fmt_instInhabitedState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__1);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Fmt_instInhabitedState_default;
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object* v_s_274_){
_start:
{
lean_object* v_toBacktrackableState_275_; 
v_toBacktrackableState_275_ = lean_ctor_get(v_s_274_, 0);
lean_inc_ref(v_toBacktrackableState_275_);
return v_toBacktrackableState_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(v_s_276_);
lean_dec_ref(v_s_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object* v_s_278_, lean_object* v_d_279_){
_start:
{
lean_object* v_shareCommonState_280_; lean_object* v_freshTagId_281_; lean_object* v_missingFormatters_282_; lean_object* v_partialFormatters_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_shareCommonState_280_ = lean_ctor_get(v_s_278_, 1);
v_freshTagId_281_ = lean_ctor_get(v_s_278_, 2);
v_missingFormatters_282_ = lean_ctor_get(v_s_278_, 3);
v_partialFormatters_283_ = lean_ctor_get(v_s_278_, 4);
v_isSharedCheck_290_ = !lean_is_exclusive(v_s_278_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v_s_278_, 0);
lean_dec(v_unused_291_);
v___x_285_ = v_s_278_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_partialFormatters_283_);
lean_inc(v_missingFormatters_282_);
lean_inc(v_freshTagId_281_);
lean_inc(v_shareCommonState_280_);
lean_dec(v_s_278_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_d_279_);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_d_279_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_shareCommonState_280_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_freshTagId_281_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_missingFormatters_282_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_partialFormatters_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object* v_entry_303_, lean_object* v_as_304_, lean_object* v_j_305_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_array_get_size(v_as_304_);
v___x_307_ = lean_nat_dec_lt(v_j_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v_j_305_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v_priority_310_; lean_object* v_priority_311_; uint8_t v___x_312_; 
v___x_309_ = lean_array_fget_borrowed(v_as_304_, v_j_305_);
v_priority_310_ = lean_ctor_get(v___x_309_, 0);
v_priority_311_ = lean_ctor_get(v_entry_303_, 0);
v___x_312_ = lean_nat_dec_lt(v_priority_310_, v_priority_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_j_305_, v___x_313_);
lean_dec(v_j_305_);
v_j_305_ = v___x_314_;
goto _start;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_j_305_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object* v_entry_317_, lean_object* v_as_318_, lean_object* v_j_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_317_, v_as_318_, v_j_319_);
lean_dec_ref(v_as_318_);
lean_dec_ref(v_entry_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object* v_providers_321_, lean_object* v_entry_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_322_, v_providers_321_, v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_array_get_size(v_providers_321_);
v___x_326_ = l_Array_insertIdx_x21___redArg(v_providers_321_, v___x_325_, v_entry_322_);
return v___x_326_;
}
else
{
lean_object* v_val_327_; lean_object* v___x_328_; 
v_val_327_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_327_);
lean_dec_ref_known(v___x_324_, 1);
v___x_328_ = l_Array_insertIdx_x21___redArg(v_providers_321_, v_val_327_, v_entry_322_);
lean_dec(v_val_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_));
v___x_333_ = lean_st_mk_ref(v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object* v_priority_337_, lean_object* v_provider_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_340_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_341_ = lean_st_ref_take(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_priority_337_);
lean_ctor_set(v___x_342_, 1, v_provider_338_);
v___x_343_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v___x_341_, v___x_342_);
v___x_344_ = lean_st_ref_put(v___x_340_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object* v_priority_346_, lean_object* v_provider_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Fmt_addBuiltinFmtProvider(v_priority_346_, v_provider_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object* v_constName_357_, lean_object* v_env_358_, lean_object* v_opts_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
v___x_361_ = l_Lean_Environment_evalConstCheck___redArg(v_env_358_, v_opts_359_, v___x_360_, v_constName_357_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object* v_constName_362_, lean_object* v_env_363_, lean_object* v_opts_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(v_constName_362_, v_env_363_, v_opts_364_);
lean_dec_ref(v_opts_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object* v_e_366_){
_start:
{
if (lean_obj_tag(v_e_366_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_a_368_ = lean_ctor_get(v_e_366_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_e_366_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v_e_366_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v_e_366_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_mk_io_user_error(v_a_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 1);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_a_377_ = lean_ctor_get(v_e_366_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_e_366_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v_e_366_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v_e_366_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 0);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object* v_e_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object* v_00_u03b1_388_, lean_object* v_e_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object* v_00_u03b1_392_, lean_object* v_e_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(v_00_u03b1_392_, v_e_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object* v_constName_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_env_399_; lean_object* v_opts_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_env_399_ = lean_ctor_get(v_a_397_, 0);
v_opts_400_ = lean_ctor_get(v_a_397_, 1);
v___x_401_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
lean_inc_ref(v_env_399_);
v___x_402_ = l_Lean_Environment_evalConstCheck___redArg(v_env_399_, v_opts_400_, v___x_401_, v_constName_396_);
v___x_403_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object* v_constName_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_constName_404_, v_a_405_);
lean_dec_ref(v_a_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_408_){
_start:
{
lean_object* v_fst_409_; 
v_fst_409_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_fst_409_);
return v_fst_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_410_);
lean_dec_ref(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_box(0);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_414_);
lean_dec_ref(v_x_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_416_, lean_object* v_s_417_){
_start:
{
lean_object* v_fst_418_; lean_object* v___x_419_; 
v_fst_418_ = lean_ctor_get(v_s_417_, 0);
lean_inc_n(v_fst_418_, 3);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_fst_418_);
lean_ctor_set(v___x_419_, 1, v_fst_418_);
lean_ctor_set(v___x_419_, 2, v_fst_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_x_420_, lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v_x_420_, v_s_421_);
lean_dec_ref(v_s_421_);
lean_dec_ref(v_x_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_snd_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_446_; 
v_snd_425_ = lean_ctor_get(v_x_424_, 1);
lean_inc(v_snd_425_);
v_fst_426_ = lean_ctor_get(v_x_423_, 0);
v_snd_427_ = lean_ctor_get(v_x_423_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_446_ == 0)
{
v___x_429_ = v_x_423_;
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_x_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_446_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_444_; 
v_fst_431_ = lean_ctor_get(v_x_424_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_x_424_, 1);
lean_dec(v_unused_445_);
v___x_433_ = v_x_424_;
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_fst_431_);
lean_dec(v_x_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_priority_435_; lean_object* v___x_437_; 
v_priority_435_ = lean_ctor_get(v_snd_425_, 0);
lean_inc(v_priority_435_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_priority_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_priority_435_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_array_push(v_fst_426_, v___x_437_);
v___x_439_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_snd_427_, v_snd_425_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_439_);
lean_ctor_set(v___x_429_, 0, v___x_438_);
v___x_441_ = v___x_429_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_447_, lean_object* v___x_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_st_ref_get(v___x_447_);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_448_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_454_, v___x_455_);
lean_dec(v___x_455_);
lean_dec(v___x_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_, lean_object* v___y_462_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_488_; 
v___x_465_ = lean_array_uget(v_as_458_, v_i_459_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_488_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_fst_466_, v___y_462_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v_a_472_);
lean_ctor_set(v___x_469_, 0, v_snd_467_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_snd_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_a_472_);
v___x_474_ = v_reuseFailAlloc_479_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; size_t v___x_476_; size_t v___x_477_; 
v___x_475_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_b_461_, v___x_474_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_459_, v___x_476_);
v_i_459_ = v___x_477_;
v_b_461_ = v___x_475_;
goto _start;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_del_object(v___x_469_);
lean_dec(v_snd_467_);
lean_dec_ref(v_b_461_);
v_a_480_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_b_461_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v_i_boxed_496_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v_as_490_, v_i_boxed_496_, v_stop_boxed_497_, v_b_493_, v___y_494_);
lean_dec_ref(v___y_494_);
lean_dec_ref(v_as_490_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_a_506_; uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_array_uget_borrowed(v_as_499_, v_i_500_);
v___x_513_ = lean_array_get_size(v___x_512_);
v___x_514_ = lean_nat_dec_lt(v___x_511_, v___x_513_);
if (v___x_514_ == 0)
{
v_a_506_ = v_b_502_;
goto v___jp_505_;
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_usize_of_nat(v___x_513_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__0(v___x_512_, v___x_515_, v___x_516_, v_b_502_, v___y_503_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v_a_506_ = v_a_518_;
goto v___jp_505_;
}
else
{
return v___x_517_;
}
}
}
else
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_b_502_);
return v___x_519_;
}
v___jp_505_:
{
size_t v___x_507_; size_t v___x_508_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_500_, v___x_507_);
v_i_500_ = v___x_508_;
v_b_502_ = v_a_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_520_, v_i_boxed_526_, v_stop_boxed_527_, v_b_523_, v___y_524_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v_as_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v_as_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_a_535_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_st_ref_get(v___x_530_);
v___x_540_ = lean_array_get_size(v_as_531_);
v___x_541_ = lean_nat_dec_lt(v___x_529_, v___x_540_);
if (v___x_541_ == 0)
{
v_a_535_ = v___x_539_;
goto v___jp_534_;
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_540_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__spec__1(v_as_531_, v___x_542_, v___x_543_, v___x_539_, v___y_532_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v_a_535_ = v_a_545_;
goto v___jp_534_;
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_a_535_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v_as_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(v___x_554_, v___x_555_, v_as_556_, v___y_557_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v_as_556_);
lean_dec(v___x_555_);
lean_dec(v___x_554_);
return v_res_559_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___f_597_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___f_597_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_597_, 0, v___x_596_);
lean_closure_set(v___f_597_, 1, v___x_595_);
return v___f_597_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___f_600_; 
v___x_598_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_599_ = lean_unsigned_to_nat(0u);
v___f_600_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_600_, 0, v___x_599_);
lean_closure_set(v___f_600_, 1, v___x_598_);
return v___f_600_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_601_ = 0;
v___x_602_ = lean_box(0);
v___x_603_ = lean_box(2);
v___f_604_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_605_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_606_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___f_607_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___f_608_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_609_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_610_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___f_608_);
lean_ctor_set(v___x_610_, 2, v___f_607_);
lean_ctor_set(v___x_610_, 3, v___f_606_);
lean_ctor_set(v___x_610_, 4, v___f_605_);
lean_ctor_set(v___x_610_, 5, v___f_604_);
lean_ctor_set(v___x_610_, 6, v___x_603_);
lean_ctor_set(v___x_610_, 7, v___x_602_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*8, v___x_601_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*8 + 1, v___x_601_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___f_611_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_));
v___x_612_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___f_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_);
v___x_616_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2____boxed(lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_107089426____hygCtx___hyg_2_();
return v_res_618_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__0(void){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Array_instInhabited___redArg();
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__0, &l_Lean_Fmt_getFmtProviders___closed__0_once, _init_l_Lean_Fmt_getFmtProviders___closed__0);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object* v_env_622_){
_start:
{
lean_object* v___x_623_; lean_object* v_toEnvExtension_624_; lean_object* v_asyncMode_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v_snd_630_; 
v___x_623_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_624_ = lean_ctor_get(v___x_623_, 0);
v_asyncMode_625_ = lean_ctor_get(v_toEnvExtension_624_, 2);
v___x_626_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_627_ = lean_box(0);
v___x_628_ = 0;
v___x_629_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_626_, v___x_623_, v_env_622_, v_asyncMode_625_, v___x_627_, v___x_628_);
v_snd_630_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_snd_630_);
lean_dec(v___x_629_);
return v_snd_630_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_631_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_nextMacroScope_640_; lean_object* v_ngen_641_; lean_object* v_auxDeclNGen_642_; lean_object* v_traceState_643_; lean_object* v_recordedDeps_644_; lean_object* v_messages_645_; lean_object* v_infoState_646_; lean_object* v_snapshotTasks_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_658_; 
v___x_639_ = lean_st_ref_take(v___y_637_);
v_nextMacroScope_640_ = lean_ctor_get(v___x_639_, 1);
v_ngen_641_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_642_ = lean_ctor_get(v___x_639_, 3);
v_traceState_643_ = lean_ctor_get(v___x_639_, 4);
v_recordedDeps_644_ = lean_ctor_get(v___x_639_, 6);
v_messages_645_ = lean_ctor_get(v___x_639_, 7);
v_infoState_646_ = lean_ctor_get(v___x_639_, 8);
v_snapshotTasks_647_ = lean_ctor_get(v___x_639_, 9);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_659_ = lean_ctor_get(v___x_639_, 5);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_660_);
v___x_649_ = v___x_639_;
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_snapshotTasks_647_);
lean_inc(v_infoState_646_);
lean_inc(v_messages_645_);
lean_inc(v_recordedDeps_644_);
lean_inc(v_traceState_643_);
lean_inc(v_auxDeclNGen_642_);
lean_inc(v_ngen_641_);
lean_inc(v_nextMacroScope_640_);
lean_dec(v___x_639_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = lean_box(0);
v___x_652_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 5, v___x_652_);
lean_ctor_set(v___x_649_, 0, v_env_636_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_env_636_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_nextMacroScope_640_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_ngen_641_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_auxDeclNGen_642_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v_traceState_643_);
lean_ctor_set(v_reuseFailAlloc_657_, 5, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_657_, 6, v_recordedDeps_644_);
lean_ctor_set(v_reuseFailAlloc_657_, 7, v_messages_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 8, v_infoState_646_);
lean_ctor_set(v_reuseFailAlloc_657_, 9, v_snapshotTasks_647_);
v___x_654_ = v_reuseFailAlloc_657_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_st_ref_put(v___y_637_, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_651_);
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_661_, v___y_662_);
lean_dec(v___y_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(lean_object* v_env_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v_env_665_, v___y_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1(v_env_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v_addEntryFn_675_, lean_object* v___x_676_, lean_object* v_s_677_){
_start:
{
lean_object* v_importedEntries_678_; lean_object* v_state_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
v_importedEntries_678_ = lean_ctor_get(v_s_677_, 0);
v_state_679_ = lean_ctor_get(v_s_677_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_s_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_681_ = v_s_677_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_state_679_);
lean_inc(v_importedEntries_678_);
lean_dec(v_s_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_state_683_; lean_object* v___x_685_; 
v_state_683_ = lean_apply_2(v_addEntryFn_675_, v_state_679_, v___x_676_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_state_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_importedEntries_678_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_state_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_691_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
lean_ctor_set(v___x_693_, 3, v___x_692_);
lean_ctor_set(v___x_693_, 4, v___x_691_);
lean_ctor_set(v___x_693_, 5, v___x_691_);
lean_ctor_set(v___x_693_, 6, v___x_691_);
lean_ctor_set(v___x_693_, 7, v___x_691_);
lean_ctor_set(v___x_693_, 8, v___x_691_);
lean_ctor_set(v___x_693_, 9, v___x_691_);
lean_ctor_set(v___x_693_, 10, v___x_691_);
lean_ctor_set(v___x_693_, 11, v___x_690_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_unsigned_to_nat(32u);
v___x_695_ = lean_mk_empty_array_with_capacity(v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_unsigned_to_nat(32u);
v___x_700_ = lean_mk_empty_array_with_capacity(v___x_699_);
v___x_701_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_702_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_698_);
lean_ctor_set(v___x_702_, 3, v___x_698_);
lean_ctor_set_usize(v___x_702_, 4, v___x_697_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_box(1);
v___x_704_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_705_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
lean_ctor_set(v___x_706_, 2, v___x_703_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v_toCold_712_; lean_object* v_env_713_; lean_object* v_options_714_; uint8_t v___x_715_; lean_object* v_env_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_711_ = lean_st_ref_get(v___y_709_);
v_toCold_712_ = lean_ctor_get(v___y_708_, 0);
v_env_713_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_env_713_);
lean_dec(v___x_711_);
v_options_714_ = lean_ctor_get(v_toCold_712_, 2);
v___x_715_ = 0;
v_env_716_ = l_Lean_Environment_setRecordingDeps(v_env_713_, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_718_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_714_);
v___x_719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_719_, 0, v_env_716_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
lean_ctor_set(v___x_719_, 3, v_options_714_);
v___x_720_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_msgData_707_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msgData_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_ref_731_; lean_object* v___x_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_ref_731_ = lean_ctor_get(v___y_728_, 2);
v___x_732_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_727_, v___y_728_, v___y_729_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_inc(v_ref_731_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_ref_731_);
lean_ctor_set(v___x_737_, 1, v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_747_, lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_toCold_752_; lean_object* v_currRecDepth_753_; lean_object* v_ref_754_; uint16_t v_optionFlags_755_; uint8_t v_suppressElabErrors_756_; uint8_t v_checkDeprecated_757_; uint8_t v_isRecordingDeps_758_; lean_object* v_ref_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_toCold_752_ = lean_ctor_get(v___y_749_, 0);
v_currRecDepth_753_ = lean_ctor_get(v___y_749_, 1);
v_ref_754_ = lean_ctor_get(v___y_749_, 2);
v_optionFlags_755_ = lean_ctor_get_uint16(v___y_749_, sizeof(void*)*3);
v_suppressElabErrors_756_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*3 + 2);
v_checkDeprecated_757_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*3 + 3);
v_isRecordingDeps_758_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*3 + 4);
v_ref_759_ = l_Lean_replaceRef(v_ref_747_, v_ref_754_);
lean_inc(v_currRecDepth_753_);
lean_inc_ref(v_toCold_752_);
v___x_760_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_760_, 0, v_toCold_752_);
lean_ctor_set(v___x_760_, 1, v_currRecDepth_753_);
lean_ctor_set(v___x_760_, 2, v_ref_759_);
lean_ctor_set_uint16(v___x_760_, sizeof(void*)*3, v_optionFlags_755_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3 + 2, v_suppressElabErrors_756_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3 + 3, v_checkDeprecated_757_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*3 + 4, v_isRecordingDeps_758_);
v___x_761_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_748_, v___x_760_, v___y_750_);
lean_dec_ref_known(v___x_760_, 3);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_762_, v_msg_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v_ref_762_);
return v_res_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_789_, lean_object* v_declHint_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_env_795_; uint8_t v___x_796_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_st_ref_get(v___y_791_);
v_env_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_env_795_);
lean_dec(v___x_794_);
v___x_796_ = l_Lean_Name_isAnonymous(v_declHint_790_);
if (v___x_796_ == 0)
{
uint8_t v_isExporting_797_; 
v_isExporting_797_ = lean_ctor_get_uint8(v_env_795_, sizeof(void*)*13);
if (v_isExporting_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v_env_795_);
lean_dec(v_declHint_790_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_msg_789_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; uint8_t v___x_800_; 
lean_inc_ref(v_env_795_);
v___x_799_ = l_Lean_Environment_setExporting(v_env_795_, v___x_796_);
lean_inc(v_declHint_790_);
lean_inc_ref(v___x_799_);
v___x_800_ = l_Lean_Environment_contains(v___x_799_, v_declHint_790_, v_isExporting_797_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_799_);
lean_dec_ref(v_env_795_);
lean_dec(v_declHint_790_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_msg_789_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_c_807_; lean_object* v___x_808_; 
v___x_802_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_803_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_804_ = l_Lean_Options_empty;
lean_inc_ref(v___x_799_);
v___x_805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_805_, 0, v___x_799_);
lean_ctor_set(v___x_805_, 1, v___x_802_);
lean_ctor_set(v___x_805_, 2, v___x_803_);
lean_ctor_set(v___x_805_, 3, v___x_804_);
lean_inc(v_declHint_790_);
v___x_806_ = l_Lean_MessageData_ofConstName(v_declHint_790_, v___x_796_);
v_c_807_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_807_, 0, v___x_805_);
lean_ctor_set(v_c_807_, 1, v___x_806_);
v___x_808_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_799_, v_declHint_790_);
lean_dec_ref(v___x_799_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v_env_795_);
lean_dec(v_declHint_790_);
v___x_809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_c_807_);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_MessageData_note(v___x_812_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v_msg_789_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
else
{
lean_object* v_val_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_850_; 
v_val_816_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_850_ == 0)
{
v___x_818_ = v___x_808_;
v_isShared_819_ = v_isSharedCheck_850_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_val_816_);
lean_dec(v___x_808_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_850_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v_moduleNames_821_; lean_object* v_mod_822_; uint8_t v___x_823_; 
v___x_820_ = l_Lean_Environment_header(v_env_795_);
lean_dec_ref(v_env_795_);
v_moduleNames_821_ = lean_ctor_get(v___x_820_, 4);
lean_inc_ref(v_moduleNames_821_);
lean_dec_ref(v___x_820_);
v_mod_822_ = lean_array_get(v___x_793_, v_moduleNames_821_, v_val_816_);
lean_dec(v_val_816_);
lean_dec_ref(v_moduleNames_821_);
v___x_823_ = l_Lean_isPrivateName(v_declHint_790_);
lean_dec(v_declHint_790_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_c_807_);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_MessageData_ofName(v_mod_822_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_MessageData_note(v___x_831_);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v_msg_789_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 0);
lean_ctor_set(v___x_818_, 0, v___x_833_);
v___x_835_ = v___x_818_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_c_807_);
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_MessageData_ofName(v_mod_822_);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_MessageData_note(v___x_844_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v_msg_789_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 0);
lean_ctor_set(v___x_818_, 0, v___x_846_);
v___x_848_ = v___x_818_;
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
}
}
}
}
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v_env_795_);
lean_dec(v_declHint_790_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_msg_789_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_852_, lean_object* v_declHint_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_852_, v_declHint_853_, v___y_854_);
lean_dec(v___y_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_857_, lean_object* v_declHint_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_872_; 
v___x_862_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_857_, v_declHint_858_, v___y_860_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_872_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = l_Lean_unknownIdentifierMessageTag;
v___x_868_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_a_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_873_, lean_object* v_declHint_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_873_, v_declHint_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_879_, lean_object* v_msg_880_, lean_object* v_declHint_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
v___x_885_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_880_, v_declHint_881_, v___y_882_, v___y_883_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v___x_887_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_879_, v_a_886_, v___y_882_, v___y_883_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_888_, lean_object* v_msg_889_, lean_object* v_declHint_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_888_, v_msg_889_, v_declHint_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v_ref_888_);
return v_res_894_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_901_, lean_object* v_constName_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_906_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_907_ = 0;
lean_inc(v_constName_902_);
v___x_908_ = l_Lean_MessageData_ofConstName(v_constName_902_, v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_901_, v___x_911_, v_constName_902_, v___y_903_, v___y_904_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_913_, lean_object* v_constName_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_913_, v_constName_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v_ref_913_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_ref_923_; lean_object* v___x_924_; 
v_ref_923_ = lean_ctor_get(v___y_920_, 2);
v___x_924_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_923_, v_constName_919_, v___y_920_, v___y_921_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(lean_object* v_constName_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; lean_object* v_env_935_; uint8_t v___x_936_; lean_object* v___x_937_; 
v___x_934_ = lean_st_ref_get(v___y_932_);
v_env_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc_ref(v_env_935_);
lean_dec(v___x_934_);
v___x_936_ = 0;
lean_inc(v_constName_930_);
v___x_937_ = l_Lean_Environment_find_x3f(v_env_935_, v_constName_930_, v___x_936_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_930_, v___y_931_, v___y_932_);
return v___x_938_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_constName_930_);
v_val_939_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_937_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v___x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_val_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_constName_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_961_, uint8_t v_kind_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___y_972_; 
v___x_966_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_967_ = l_Lean_MessageData_ofName(v_name_961_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
switch(v_kind_962_)
{
case 0:
{
lean_object* v___x_979_; 
v___x_979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___y_972_ = v___x_979_;
goto v___jp_971_;
}
case 1:
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__5));
v___y_972_ = v___x_980_;
goto v___jp_971_;
}
default: 
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_972_ = v___x_981_;
goto v___jp_971_;
}
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref(v___y_972_);
v___x_973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_973_, 0, v___y_972_);
v___x_974_ = l_Lean_MessageData_ofFormat(v___x_973_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_970_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_977_, v___y_963_, v___y_964_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_982_, lean_object* v_kind_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_kind_boxed_987_; lean_object* v_res_988_; 
v_kind_boxed_987_ = lean_unbox(v_kind_983_);
v_res_988_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_982_, v_kind_boxed_987_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_1004_, lean_object* v_declName_1005_, lean_object* v_givenType_1006_, lean_object* v_expectedType_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1011_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_1012_ = l_Lean_MessageData_ofName(v_attrName_1004_);
lean_inc_ref(v___x_1012_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = 0;
v___x_1017_ = l_Lean_MessageData_ofConstName(v_declName_1005_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_indentExpr(v_givenType_1006_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1012_);
v___x_1026_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_indentExpr(v_expectedType_1007_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1029_, v___y_1008_, v___y_1009_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_1031_, lean_object* v_declName_1032_, lean_object* v_givenType_1033_, lean_object* v_expectedType_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1031_, v_declName_1032_, v_givenType_1033_, v_expectedType_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v_decl_1043_, lean_object* v_stx_1044_, uint8_t v_kind_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1044_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___x_1109_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
lean_inc(v_decl_1043_);
lean_inc(v___x_1042_);
v___x_1109_ = l_Lean_ensureAttrDeclIsMeta(v___x_1042_, v_decl_1043_, v_kind_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1109_) == 0)
{
uint8_t v___x_1110_; uint8_t v___x_1111_; 
lean_dec_ref_known(v___x_1109_, 1);
v___x_1110_ = 0;
v___x_1111_ = l_Lean_instBEqAttributeKind_beq(v_kind_1045_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_a_1050_);
lean_dec(v_decl_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v___x_1039_);
v___x_1112_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_1042_, v_kind_1045_, v___y_1046_, v___y_1047_);
return v___x_1112_;
}
else
{
v___y_1090_ = v___y_1046_;
v___y_1091_ = v___y_1047_;
goto v___jp_1089_;
}
}
else
{
lean_dec(v_a_1050_);
lean_dec(v_decl_1043_);
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v___x_1039_);
return v___x_1109_;
}
v___jp_1051_:
{
lean_object* v___x_1054_; lean_object* v_env_1055_; lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1054_ = lean_st_ref_get(v___y_1053_);
v_env_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_env_1055_);
lean_dec(v___x_1054_);
v_ref_1056_ = lean_ctor_get(v___y_1052_, 2);
v___x_1057_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1052_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_env_1055_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
lean_inc(v_decl_1043_);
v___x_1059_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_decl_1043_, v___x_1058_);
lean_dec_ref_known(v___x_1058_, 2);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_env_1063_; lean_object* v___x_1064_; lean_object* v_toEnvExtension_1065_; lean_object* v_addEntryFn_1066_; lean_object* v_asyncMode_1067_; uint8_t v_logWrites_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; uint8_t v___x_1071_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_a_1050_);
lean_ctor_set(v___x_1061_, 1, v_a_1060_);
v___x_1062_ = lean_st_ref_get(v___y_1053_);
v_env_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_env_1063_);
lean_dec(v___x_1062_);
v___x_1064_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_1065_ = lean_ctor_get(v___x_1064_, 0);
v_addEntryFn_1066_ = lean_ctor_get(v___x_1064_, 3);
v_asyncMode_1067_ = lean_ctor_get(v_toEnvExtension_1065_, 2);
v_logWrites_1068_ = lean_ctor_get_uint8(v_toEnvExtension_1065_, sizeof(void*)*6);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_decl_1043_);
lean_ctor_set(v___x_1069_, 1, v___x_1061_);
lean_inc(v_addEntryFn_1066_);
v___f_1070_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1070_, 0, v_addEntryFn_1066_);
lean_closure_set(v___f_1070_, 1, v___x_1069_);
v___x_1071_ = 1;
if (v_logWrites_1068_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_inc_ref(v_toEnvExtension_1065_);
v___x_1072_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1065_, v_env_1063_, v___f_1070_, v_asyncMode_1067_, v___x_1039_, v___x_1071_);
v___x_1073_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1072_, v___y_1053_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc_ref_n(v_toEnvExtension_1065_, 2);
v___x_1074_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1065_, v_env_1063_);
lean_dec_ref(v_env_1063_);
v___x_1075_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1065_, v___x_1074_, v___f_1070_, v_asyncMode_1067_, v___x_1039_, v___x_1071_);
v___x_1076_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_1075_, v___y_1053_);
return v___x_1076_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1050_);
lean_dec(v_decl_1043_);
lean_dec(v___x_1039_);
v_a_1077_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1079_ = v___x_1059_;
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1059_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1081_ = lean_io_error_to_string(v_a_1077_);
v___x_1082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_ofFormat(v___x_1082_);
lean_inc(v_ref_1056_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_ref_1056_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1084_);
v___x_1086_ = v___x_1079_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1092_; 
lean_inc(v_decl_1043_);
v___x_1092_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_1043_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Lean_ConstantInfo_type(v_a_1093_);
lean_dec(v_a_1093_);
v___x_1095_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2));
v___x_1096_ = l_Lean_Name_mkStr3(v___x_1040_, v___x_1041_, v___x_1095_);
v___x_1097_ = l_Lean_Expr_isConstOf(v___x_1094_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v_a_1050_);
lean_dec(v___x_1039_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_mkConst(v___x_1096_, v___x_1098_);
v___x_1100_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_1042_, v_decl_1043_, v___x_1094_, v___x_1099_, v___y_1090_, v___y_1091_);
return v___x_1100_;
}
else
{
lean_dec(v___x_1096_);
lean_dec_ref(v___x_1094_);
lean_dec(v___x_1042_);
v___y_1052_ = v___y_1090_;
v___y_1053_ = v___y_1091_;
goto v___jp_1051_;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_a_1050_);
lean_dec(v_decl_1043_);
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v___x_1039_);
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_decl_1043_);
lean_dec(v___x_1042_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v___x_1039_);
v_a_1113_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1049_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1049_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v___x_1123_, lean_object* v___x_1124_, lean_object* v_decl_1125_, lean_object* v_stx_1126_, lean_object* v_kind_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_kind_boxed_1131_; lean_object* v_res_1132_; 
v_kind_boxed_1131_ = lean_unbox(v_kind_1127_);
v_res_1132_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_, v_decl_1125_, v_stx_1126_, v_kind_boxed_1131_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(lean_object* v___x_1139_, lean_object* v_decl_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1145_ = l_Lean_MessageData_ofName(v___x_1139_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_1148_, v___y_1141_, v___y_1142_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v___x_1150_, lean_object* v_decl_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(v___x_1150_, v_decl_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v_decl_1151_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_1212_ = l_Lean_registerBuiltinAttribute(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2____boxed(lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_();
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v_msg_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0(v_00_u03b1_1221_, v_msg_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1227_, lean_object* v_attrName_1228_, lean_object* v_declName_1229_, lean_object* v_givenType_1230_, lean_object* v_expectedType_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_attrName_1228_, v_declName_1229_, v_givenType_1230_, v_expectedType_1231_, v___y_1232_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1236_, lean_object* v_attrName_1237_, lean_object* v_declName_1238_, lean_object* v_givenType_1239_, lean_object* v_expectedType_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3(v_00_u03b1_1236_, v_attrName_1237_, v_declName_1238_, v_givenType_1239_, v_expectedType_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1245_, lean_object* v_name_1246_, uint8_t v_kind_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_1246_, v_kind_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_name_1253_, lean_object* v_kind_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_kind_boxed_1258_; lean_object* v_res_1259_; 
v_kind_boxed_1258_ = lean_unbox(v_kind_1254_);
v_res_1259_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4(v_00_u03b1_1252_, v_name_1253_, v_kind_boxed_1258_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1260_, lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1266_, v_constName_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1273_, v_constName_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_ref_1280_, lean_object* v_constName_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1279_, v_ref_1280_, v_constName_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v_ref_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1286_, lean_object* v_ref_1287_, lean_object* v_msg_1288_, lean_object* v_declHint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1287_, v_msg_1288_, v_declHint_1289_, v___y_1290_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_ref_1295_, lean_object* v_msg_1296_, lean_object* v_declHint_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1294_, v_ref_1295_, v_msg_1296_, v_declHint_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v_ref_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1302_, lean_object* v_declHint_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1302_, v_declHint_1303_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1314_, lean_object* v_ref_1315_, lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1315_, v_msg_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v_msg_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1321_, v_ref_1322_, v_msg_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v_ref_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(uint8_t v_x_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(v_x_1328_);
v___x_1330_ = lean_obj_tag_nat(v___x_1329_);
lean_dec(v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl___boxed(lean_object* v_x_1331_){
_start:
{
uint8_t v_x_4__boxed_1332_; lean_object* v_res_1333_; 
v_x_4__boxed_1332_ = lean_unbox(v_x_1331_);
v_res_1333_ = l_Lean_Fmt_Comment_Whitespace_ctorIdx___impl(v_x_4__boxed_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(lean_object* v_k_1334_){
_start:
{
lean_inc(v_k_1334_);
return v_k_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg___boxed(lean_object* v_k_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Fmt_Comment_Whitespace_ctorElim___redArg(v_k_1335_);
lean_dec(v_k_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim(lean_object* v_motive_1337_, lean_object* v_ctorIdx_1338_, uint8_t v_t_1339_, lean_object* v_h_1340_, lean_object* v_k_1341_){
_start:
{
lean_inc(v_k_1341_);
return v_k_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_ctorElim___boxed(lean_object* v_motive_1342_, lean_object* v_ctorIdx_1343_, lean_object* v_t_1344_, lean_object* v_h_1345_, lean_object* v_k_1346_){
_start:
{
uint8_t v_t_boxed_1347_; lean_object* v_res_1348_; 
v_t_boxed_1347_ = lean_unbox(v_t_1344_);
v_res_1348_ = l_Lean_Fmt_Comment_Whitespace_ctorElim(v_motive_1342_, v_ctorIdx_1343_, v_t_boxed_1347_, v_h_1345_, v_k_1346_);
lean_dec(v_k_1346_);
lean_dec(v_ctorIdx_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(lean_object* v_leading_1349_){
_start:
{
lean_inc(v_leading_1349_);
return v_leading_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg___boxed(lean_object* v_leading_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Fmt_Comment_Whitespace_leading_elim___redArg(v_leading_1350_);
lean_dec(v_leading_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim(lean_object* v_motive_1352_, uint8_t v_t_1353_, lean_object* v_h_1354_, lean_object* v_leading_1355_){
_start:
{
lean_inc(v_leading_1355_);
return v_leading_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_leading_elim___boxed(lean_object* v_motive_1356_, lean_object* v_t_1357_, lean_object* v_h_1358_, lean_object* v_leading_1359_){
_start:
{
uint8_t v_t_boxed_1360_; lean_object* v_res_1361_; 
v_t_boxed_1360_ = lean_unbox(v_t_1357_);
v_res_1361_ = l_Lean_Fmt_Comment_Whitespace_leading_elim(v_motive_1356_, v_t_boxed_1360_, v_h_1358_, v_leading_1359_);
lean_dec(v_leading_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(lean_object* v_trailing_1362_){
_start:
{
lean_inc(v_trailing_1362_);
return v_trailing_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg___boxed(lean_object* v_trailing_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim___redArg(v_trailing_1363_);
lean_dec(v_trailing_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim(lean_object* v_motive_1365_, uint8_t v_t_1366_, lean_object* v_h_1367_, lean_object* v_trailing_1368_){
_start:
{
lean_inc(v_trailing_1368_);
return v_trailing_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Whitespace_trailing_elim___boxed(lean_object* v_motive_1369_, lean_object* v_t_1370_, lean_object* v_h_1371_, lean_object* v_trailing_1372_){
_start:
{
uint8_t v_t_boxed_1373_; lean_object* v_res_1374_; 
v_t_boxed_1373_ = lean_unbox(v_t_1370_);
v_res_1374_ = l_Lean_Fmt_Comment_Whitespace_trailing_elim(v_motive_1369_, v_t_boxed_1373_, v_h_1371_, v_trailing_1372_);
lean_dec(v_trailing_1372_);
return v_res_1374_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace_default(void){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = 0;
return v___x_1375_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedWhitespace(void){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = 0;
return v___x_1376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqWhitespace_beq(uint8_t v_x_1377_, uint8_t v_y_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1379_ = lean_box(v_x_1377_);
v___x_1380_ = lean_obj_tag_nat(v___x_1379_);
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(v_y_1378_);
v___x_1382_ = lean_obj_tag_nat(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1383_ = lean_nat_dec_eq(v___x_1380_, v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqWhitespace_beq___boxed(lean_object* v_x_1384_, lean_object* v_y_1385_){
_start:
{
uint8_t v_x_24__boxed_1386_; uint8_t v_y_25__boxed_1387_; uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_x_24__boxed_1386_ = lean_unbox(v_x_1384_);
v_y_25__boxed_1387_ = lean_unbox(v_y_1385_);
v_res_1388_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_x_24__boxed_1386_, v_y_25__boxed_1387_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(2u);
v___x_1399_ = lean_nat_to_int(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_to_int(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr(uint8_t v_x_1402_, lean_object* v_prec_1403_){
_start:
{
lean_object* v___y_1405_; lean_object* v___y_1412_; 
if (v_x_1402_ == 0)
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = lean_unsigned_to_nat(1024u);
v___x_1419_ = lean_nat_dec_le(v___x_1418_, v_prec_1403_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1405_ = v___x_1420_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1405_ = v___x_1421_;
goto v___jp_1404_;
}
}
else
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_unsigned_to_nat(1024u);
v___x_1423_ = lean_nat_dec_le(v___x_1422_, v_prec_1403_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1412_ = v___x_1425_;
goto v___jp_1411_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__1));
lean_inc(v___y_1405_);
v___x_1407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = 0;
v___x_1409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*1, v___x_1408_);
v___x_1410_ = l_Repr_addAppParen(v___x_1409_, v_prec_1403_);
return v___x_1410_;
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1413_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__3));
lean_inc(v___y_1412_);
v___x_1414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___y_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = 0;
v___x_1416_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*1, v___x_1415_);
v___x_1417_ = l_Repr_addAppParen(v___x_1416_, v_prec_1403_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprWhitespace_repr___boxed(lean_object* v_x_1426_, lean_object* v_prec_1427_){
_start:
{
uint8_t v_x_117__boxed_1428_; lean_object* v_res_1429_; 
v_x_117__boxed_1428_ = lean_unbox(v_x_1426_);
v_res_1429_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_x_117__boxed_1428_, v_prec_1427_);
lean_dec(v_prec_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl(uint8_t v_x_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_box(v_x_1432_);
v___x_1434_ = lean_obj_tag_nat(v___x_1433_);
lean_dec(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorIdx___impl___boxed(lean_object* v_x_1435_){
_start:
{
uint8_t v_x_4__boxed_1436_; lean_object* v_res_1437_; 
v_x_4__boxed_1436_ = lean_unbox(v_x_1435_);
v_res_1437_ = l_Lean_Fmt_Comment_Placement_ctorIdx___impl(v_x_4__boxed_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg(lean_object* v_k_1438_){
_start:
{
lean_inc(v_k_1438_);
return v_k_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___redArg___boxed(lean_object* v_k_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Fmt_Comment_Placement_ctorElim___redArg(v_k_1439_);
lean_dec(v_k_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim(lean_object* v_motive_1441_, lean_object* v_ctorIdx_1442_, uint8_t v_t_1443_, lean_object* v_h_1444_, lean_object* v_k_1445_){
_start:
{
lean_inc(v_k_1445_);
return v_k_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_ctorElim___boxed(lean_object* v_motive_1446_, lean_object* v_ctorIdx_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_k_1450_){
_start:
{
uint8_t v_t_boxed_1451_; lean_object* v_res_1452_; 
v_t_boxed_1451_ = lean_unbox(v_t_1448_);
v_res_1452_ = l_Lean_Fmt_Comment_Placement_ctorElim(v_motive_1446_, v_ctorIdx_1447_, v_t_boxed_1451_, v_h_1449_, v_k_1450_);
lean_dec(v_k_1450_);
lean_dec(v_ctorIdx_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(lean_object* v_afterToken_1453_){
_start:
{
lean_inc(v_afterToken_1453_);
return v_afterToken_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg___boxed(lean_object* v_afterToken_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Fmt_Comment_Placement_afterToken_elim___redArg(v_afterToken_1454_);
lean_dec(v_afterToken_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim(lean_object* v_motive_1456_, uint8_t v_t_1457_, lean_object* v_h_1458_, lean_object* v_afterToken_1459_){
_start:
{
lean_inc(v_afterToken_1459_);
return v_afterToken_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_afterToken_elim___boxed(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_afterToken_1463_){
_start:
{
uint8_t v_t_boxed_1464_; lean_object* v_res_1465_; 
v_t_boxed_1464_ = lean_unbox(v_t_1461_);
v_res_1465_ = l_Lean_Fmt_Comment_Placement_afterToken_elim(v_motive_1460_, v_t_boxed_1464_, v_h_1462_, v_afterToken_1463_);
lean_dec(v_afterToken_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(lean_object* v_onLineBeforeToken_1466_){
_start:
{
lean_inc(v_onLineBeforeToken_1466_);
return v_onLineBeforeToken_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg___boxed(lean_object* v_onLineBeforeToken_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___redArg(v_onLineBeforeToken_1467_);
lean_dec(v_onLineBeforeToken_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(lean_object* v_motive_1469_, uint8_t v_t_1470_, lean_object* v_h_1471_, lean_object* v_onLineBeforeToken_1472_){
_start:
{
lean_inc(v_onLineBeforeToken_1472_);
return v_onLineBeforeToken_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim___boxed(lean_object* v_motive_1473_, lean_object* v_t_1474_, lean_object* v_h_1475_, lean_object* v_onLineBeforeToken_1476_){
_start:
{
uint8_t v_t_boxed_1477_; lean_object* v_res_1478_; 
v_t_boxed_1477_ = lean_unbox(v_t_1474_);
v_res_1478_ = l_Lean_Fmt_Comment_Placement_onLineBeforeToken_elim(v_motive_1473_, v_t_boxed_1477_, v_h_1475_, v_onLineBeforeToken_1476_);
lean_dec(v_onLineBeforeToken_1476_);
return v_res_1478_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement_default(void){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedPlacement(void){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = 0;
return v___x_1480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqPlacement_beq(uint8_t v_x_1481_, uint8_t v_y_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1483_ = lean_box(v_x_1481_);
v___x_1484_ = lean_obj_tag_nat(v___x_1483_);
lean_dec(v___x_1483_);
v___x_1485_ = lean_box(v_y_1482_);
v___x_1486_ = lean_obj_tag_nat(v___x_1485_);
lean_dec(v___x_1485_);
v___x_1487_ = lean_nat_dec_eq(v___x_1484_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqPlacement_beq___boxed(lean_object* v_x_1488_, lean_object* v_y_1489_){
_start:
{
uint8_t v_x_24__boxed_1490_; uint8_t v_y_25__boxed_1491_; uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_x_24__boxed_1490_ = lean_unbox(v_x_1488_);
v_y_25__boxed_1491_ = lean_unbox(v_y_1489_);
v_res_1492_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_x_24__boxed_1490_, v_y_25__boxed_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr(uint8_t v_x_1502_, lean_object* v_prec_1503_){
_start:
{
lean_object* v___y_1505_; lean_object* v___y_1512_; 
if (v_x_1502_ == 0)
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_unsigned_to_nat(1024u);
v___x_1519_ = lean_nat_dec_le(v___x_1518_, v_prec_1503_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1505_ = v___x_1520_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1505_ = v___x_1521_;
goto v___jp_1504_;
}
}
else
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_unsigned_to_nat(1024u);
v___x_1523_ = lean_nat_dec_le(v___x_1522_, v_prec_1503_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1512_ = v___x_1524_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1512_ = v___x_1525_;
goto v___jp_1511_;
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1506_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__1));
lean_inc(v___y_1505_);
v___x_1507_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = 0;
v___x_1509_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*1, v___x_1508_);
v___x_1510_ = l_Repr_addAppParen(v___x_1509_, v_prec_1503_);
return v___x_1510_;
}
v___jp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1513_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprPlacement_repr___closed__3));
lean_inc(v___y_1512_);
v___x_1514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___y_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = 0;
v___x_1516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*1, v___x_1515_);
v___x_1517_ = l_Repr_addAppParen(v___x_1516_, v_prec_1503_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprPlacement_repr___boxed(lean_object* v_x_1526_, lean_object* v_prec_1527_){
_start:
{
uint8_t v_x_113__boxed_1528_; lean_object* v_res_1529_; 
v_x_113__boxed_1528_ = lean_unbox(v_x_1526_);
v_res_1529_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_x_113__boxed_1528_, v_prec_1527_);
lean_dec(v_prec_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl(uint8_t v_x_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_box(v_x_1532_);
v___x_1534_ = lean_obj_tag_nat(v___x_1533_);
lean_dec(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorIdx___impl___boxed(lean_object* v_x_1535_){
_start:
{
uint8_t v_x_4__boxed_1536_; lean_object* v_res_1537_; 
v_x_4__boxed_1536_ = lean_unbox(v_x_1535_);
v_res_1537_ = l_Lean_Fmt_Comment_Kind_ctorIdx___impl(v_x_4__boxed_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg(lean_object* v_k_1538_){
_start:
{
lean_inc(v_k_1538_);
return v_k_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___redArg___boxed(lean_object* v_k_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Fmt_Comment_Kind_ctorElim___redArg(v_k_1539_);
lean_dec(v_k_1539_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim(lean_object* v_motive_1541_, lean_object* v_ctorIdx_1542_, uint8_t v_t_1543_, lean_object* v_h_1544_, lean_object* v_k_1545_){
_start:
{
lean_inc(v_k_1545_);
return v_k_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_ctorElim___boxed(lean_object* v_motive_1546_, lean_object* v_ctorIdx_1547_, lean_object* v_t_1548_, lean_object* v_h_1549_, lean_object* v_k_1550_){
_start:
{
uint8_t v_t_boxed_1551_; lean_object* v_res_1552_; 
v_t_boxed_1551_ = lean_unbox(v_t_1548_);
v_res_1552_ = l_Lean_Fmt_Comment_Kind_ctorElim(v_motive_1546_, v_ctorIdx_1547_, v_t_boxed_1551_, v_h_1549_, v_k_1550_);
lean_dec(v_k_1550_);
lean_dec(v_ctorIdx_1547_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(lean_object* v_lineComment_1553_){
_start:
{
lean_inc(v_lineComment_1553_);
return v_lineComment_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg___boxed(lean_object* v_lineComment_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Fmt_Comment_Kind_lineComment_elim___redArg(v_lineComment_1554_);
lean_dec(v_lineComment_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim(lean_object* v_motive_1556_, uint8_t v_t_1557_, lean_object* v_h_1558_, lean_object* v_lineComment_1559_){
_start:
{
lean_inc(v_lineComment_1559_);
return v_lineComment_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_lineComment_elim___boxed(lean_object* v_motive_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_lineComment_1563_){
_start:
{
uint8_t v_t_boxed_1564_; lean_object* v_res_1565_; 
v_t_boxed_1564_ = lean_unbox(v_t_1561_);
v_res_1565_ = l_Lean_Fmt_Comment_Kind_lineComment_elim(v_motive_1560_, v_t_boxed_1564_, v_h_1562_, v_lineComment_1563_);
lean_dec(v_lineComment_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(lean_object* v_blockComment_1566_){
_start:
{
lean_inc(v_blockComment_1566_);
return v_blockComment_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg___boxed(lean_object* v_blockComment_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Fmt_Comment_Kind_blockComment_elim___redArg(v_blockComment_1567_);
lean_dec(v_blockComment_1567_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim(lean_object* v_motive_1569_, uint8_t v_t_1570_, lean_object* v_h_1571_, lean_object* v_blockComment_1572_){
_start:
{
lean_inc(v_blockComment_1572_);
return v_blockComment_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_Kind_blockComment_elim___boxed(lean_object* v_motive_1573_, lean_object* v_t_1574_, lean_object* v_h_1575_, lean_object* v_blockComment_1576_){
_start:
{
uint8_t v_t_boxed_1577_; lean_object* v_res_1578_; 
v_t_boxed_1577_ = lean_unbox(v_t_1574_);
v_res_1578_ = l_Lean_Fmt_Comment_Kind_blockComment_elim(v_motive_1573_, v_t_boxed_1577_, v_h_1575_, v_blockComment_1576_);
lean_dec(v_blockComment_1576_);
return v_res_1578_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = 0;
return v___x_1579_;
}
}
static uint8_t _init_l_Lean_Fmt_Comment_instInhabitedKind(void){
_start:
{
uint8_t v___x_1580_; 
v___x_1580_ = 0;
return v___x_1580_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Comment_instBEqKind_beq(uint8_t v_x_1581_, uint8_t v_y_1582_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1583_ = lean_box(v_x_1581_);
v___x_1584_ = lean_obj_tag_nat(v___x_1583_);
lean_dec(v___x_1583_);
v___x_1585_ = lean_box(v_y_1582_);
v___x_1586_ = lean_obj_tag_nat(v___x_1585_);
lean_dec(v___x_1585_);
v___x_1587_ = lean_nat_dec_eq(v___x_1584_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instBEqKind_beq___boxed(lean_object* v_x_1588_, lean_object* v_y_1589_){
_start:
{
uint8_t v_x_24__boxed_1590_; uint8_t v_y_25__boxed_1591_; uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_x_24__boxed_1590_ = lean_unbox(v_x_1588_);
v_y_25__boxed_1591_ = lean_unbox(v_y_1589_);
v_res_1592_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_x_24__boxed_1590_, v_y_25__boxed_1591_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr(uint8_t v_x_1602_, lean_object* v_prec_1603_){
_start:
{
lean_object* v___y_1605_; lean_object* v___y_1612_; 
if (v_x_1602_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_unsigned_to_nat(1024u);
v___x_1619_ = lean_nat_dec_le(v___x_1618_, v_prec_1603_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1605_ = v___x_1620_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1605_ = v___x_1621_;
goto v___jp_1604_;
}
}
else
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_unsigned_to_nat(1024u);
v___x_1623_ = lean_nat_dec_le(v___x_1622_, v_prec_1603_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__4);
v___y_1612_ = v___x_1624_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_obj_once(&l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5, &l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5_once, _init_l_Lean_Fmt_Comment_instReprWhitespace_repr___closed__5);
v___y_1612_ = v___x_1625_;
goto v___jp_1611_;
}
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1606_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__1));
lean_inc(v___y_1605_);
v___x_1607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___y_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = 0;
v___x_1609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set_uint8(v___x_1609_, sizeof(void*)*1, v___x_1608_);
v___x_1610_ = l_Repr_addAppParen(v___x_1609_, v_prec_1603_);
return v___x_1610_;
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1613_ = ((lean_object*)(l_Lean_Fmt_Comment_instReprKind_repr___closed__3));
lean_inc(v___y_1612_);
v___x_1614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___y_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = 0;
v___x_1616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*1, v___x_1615_);
v___x_1617_ = l_Repr_addAppParen(v___x_1616_, v_prec_1603_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Comment_instReprKind_repr___boxed(lean_object* v_x_1626_, lean_object* v_prec_1627_){
_start:
{
uint8_t v_x_113__boxed_1628_; lean_object* v_res_1629_; 
v_x_113__boxed_1628_ = lean_unbox(v_x_1626_);
v_res_1629_ = l_Lean_Fmt_Comment_instReprKind_repr(v_x_113__boxed_1628_, v_prec_1627_);
lean_dec(v_prec_1627_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default___closed__1(void){
_start:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v___x_1634_ = ((lean_object*)(l_Lean_Fmt_instInhabitedComment_default___closed__0));
v___x_1635_ = 0;
v___x_1636_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_1637_ = 0;
v___x_1638_ = 0;
v___x_1639_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1636_);
lean_ctor_set(v___x_1639_, 2, v___x_1634_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3, v___x_1638_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 1, v___x_1637_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*3 + 2, v___x_1635_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment_default(void){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_obj_once(&l_Lean_Fmt_instInhabitedComment_default___closed__1, &l_Lean_Fmt_instInhabitedComment_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedComment_default___closed__1);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedComment(void){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Fmt_instInhabitedComment_default;
return v___x_1641_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(lean_object* v_xs_1642_, lean_object* v_ys_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v_zero_1645_; uint8_t v_isZero_1646_; 
v_zero_1645_ = lean_unsigned_to_nat(0u);
v_isZero_1646_ = lean_nat_dec_eq(v_x_1644_, v_zero_1645_);
if (v_isZero_1646_ == 1)
{
lean_dec(v_x_1644_);
return v_isZero_1646_;
}
else
{
lean_object* v_one_1647_; lean_object* v_n_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_one_1647_ = lean_unsigned_to_nat(1u);
v_n_1648_ = lean_nat_sub(v_x_1644_, v_one_1647_);
lean_dec(v_x_1644_);
v___x_1649_ = lean_array_fget_borrowed(v_xs_1642_, v_n_1648_);
v___x_1650_ = lean_array_fget_borrowed(v_ys_1643_, v_n_1648_);
v___x_1651_ = lean_string_dec_eq(v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec(v_n_1648_);
return v___x_1651_;
}
else
{
v_x_1644_ = v_n_1648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg___boxed(lean_object* v_xs_1653_, lean_object* v_ys_1654_, lean_object* v_x_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1653_, v_ys_1654_, v_x_1655_);
lean_dec_ref(v_ys_1654_);
lean_dec_ref(v_xs_1653_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqComment_beq(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
uint8_t v_kind_1660_; uint8_t v_placement_1661_; lean_object* v_originalTokenRange_1662_; lean_object* v_originalWhitespaceRange_1663_; uint8_t v_originalWhitespaceKind_1664_; lean_object* v_content_1665_; uint8_t v_kind_1666_; uint8_t v_placement_1667_; lean_object* v_originalTokenRange_1668_; lean_object* v_originalWhitespaceRange_1669_; uint8_t v_originalWhitespaceKind_1670_; lean_object* v_content_1671_; uint8_t v___x_1672_; 
v_kind_1660_ = lean_ctor_get_uint8(v_x_1658_, sizeof(void*)*3);
v_placement_1661_ = lean_ctor_get_uint8(v_x_1658_, sizeof(void*)*3 + 1);
v_originalTokenRange_1662_ = lean_ctor_get(v_x_1658_, 0);
v_originalWhitespaceRange_1663_ = lean_ctor_get(v_x_1658_, 1);
v_originalWhitespaceKind_1664_ = lean_ctor_get_uint8(v_x_1658_, sizeof(void*)*3 + 2);
v_content_1665_ = lean_ctor_get(v_x_1658_, 2);
v_kind_1666_ = lean_ctor_get_uint8(v_x_1659_, sizeof(void*)*3);
v_placement_1667_ = lean_ctor_get_uint8(v_x_1659_, sizeof(void*)*3 + 1);
v_originalTokenRange_1668_ = lean_ctor_get(v_x_1659_, 0);
v_originalWhitespaceRange_1669_ = lean_ctor_get(v_x_1659_, 1);
v_originalWhitespaceKind_1670_ = lean_ctor_get_uint8(v_x_1659_, sizeof(void*)*3 + 2);
v_content_1671_ = lean_ctor_get(v_x_1659_, 2);
v___x_1672_ = l_Lean_Fmt_Comment_instBEqKind_beq(v_kind_1660_, v_kind_1666_);
if (v___x_1672_ == 0)
{
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = l_Lean_Fmt_Comment_instBEqPlacement_beq(v_placement_1661_, v_placement_1667_);
if (v___x_1673_ == 0)
{
return v___x_1673_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_Syntax_instBEqRange_beq(v_originalTokenRange_1662_, v_originalTokenRange_1668_);
if (v___x_1674_ == 0)
{
return v___x_1674_;
}
else
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Lean_Syntax_instBEqRange_beq(v_originalWhitespaceRange_1663_, v_originalWhitespaceRange_1669_);
if (v___x_1675_ == 0)
{
return v___x_1675_;
}
else
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_Fmt_Comment_instBEqWhitespace_beq(v_originalWhitespaceKind_1664_, v_originalWhitespaceKind_1670_);
if (v___x_1676_ == 0)
{
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1677_ = lean_array_get_size(v_content_1665_);
v___x_1678_ = lean_array_get_size(v_content_1671_);
v___x_1679_ = lean_nat_dec_eq(v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
return v___x_1679_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_content_1665_, v_content_1671_, v___x_1677_);
return v___x_1680_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqComment_beq___boxed(lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Lean_Fmt_instBEqComment_beq(v_x_1681_, v_x_1682_);
lean_dec_ref(v_x_1682_);
lean_dec_ref(v_x_1681_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(lean_object* v_xs_1685_, lean_object* v_ys_1686_, lean_object* v_hsz_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___redArg(v_xs_1685_, v_ys_1686_, v_x_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0___boxed(lean_object* v_xs_1691_, lean_object* v_ys_1692_, lean_object* v_hsz_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Array_isEqvAux___at___00Lean_Fmt_instBEqComment_beq_spec__0(v_xs_1691_, v_ys_1692_, v_hsz_1693_, v_x_1694_, v_x_1695_);
lean_dec_ref(v_ys_1692_);
lean_dec_ref(v_xs_1691_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_dec(v_x_1700_);
return v_x_1701_;
}
else
{
lean_object* v_head_1703_; lean_object* v_tail_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1715_; 
v_head_1703_ = lean_ctor_get(v_x_1702_, 0);
v_tail_1704_ = lean_ctor_get(v_x_1702_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1706_ = v_x_1702_;
v_isShared_1707_ = v_isSharedCheck_1715_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_tail_1704_);
lean_inc(v_head_1703_);
lean_dec(v_x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1715_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
lean_inc(v_x_1700_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 5);
lean_ctor_set(v___x_1706_, 1, v_x_1700_);
lean_ctor_set(v___x_1706_, 0, v_x_1701_);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_x_1701_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_x_1700_);
v___x_1709_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = l_String_quote(v_head_1703_);
v___x_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1709_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v_x_1701_ = v___x_1712_;
v_x_1702_ = v_tail_1704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
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
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1726_ = l_String_quote(v_head_1719_);
v___x_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1_spec__2(v_x_1716_, v___x_1728_, v_tail_1720_);
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_String_quote(v___y_1732_);
v___x_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_object* v___x_1737_; 
lean_dec(v_x_1736_);
v___x_1737_ = lean_box(0);
return v___x_1737_;
}
else
{
lean_object* v_tail_1738_; 
v_tail_1738_ = lean_ctor_get(v_x_1735_, 1);
if (lean_obj_tag(v_tail_1738_) == 0)
{
lean_object* v_head_1739_; lean_object* v___x_1740_; 
lean_dec(v_x_1736_);
v_head_1739_ = lean_ctor_get(v_x_1735_, 0);
lean_inc(v_head_1739_);
lean_dec_ref_known(v_x_1735_, 2);
v___x_1740_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1739_);
return v___x_1740_;
}
else
{
lean_object* v_head_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc(v_tail_1738_);
v_head_1741_ = lean_ctor_get(v_x_1735_, 0);
lean_inc(v_head_1741_);
lean_dec_ref_known(v_x_1735_, 2);
v___x_1742_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0___lam__0(v_head_1741_);
v___x_1743_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0_spec__1(v_x_1736_, v___x_1742_, v_tail_1738_);
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(lean_object* v_xs_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = lean_array_get_size(v_xs_1744_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_nat_dec_eq(v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1748_ = lean_array_to_list(v_xs_1744_);
v___x_1749_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_1750_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0_spec__0(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_1752_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_1753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1750_);
v___x_1754_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_1755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1751_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Std_Format_fill(v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref(v_xs_1744_);
v___x_1758_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_1758_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_unsigned_to_nat(8u);
v___x_1769_ = lean_nat_to_int(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_unsigned_to_nat(13u);
v___x_1774_ = lean_nat_to_int(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(22u);
v___x_1779_ = lean_nat_to_int(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(11u);
v___x_1790_ = lean_nat_to_int(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___redArg(lean_object* v_x_1791_){
_start:
{
uint8_t v_kind_1792_; uint8_t v_placement_1793_; lean_object* v_originalTokenRange_1794_; lean_object* v_originalWhitespaceRange_1795_; uint8_t v_originalWhitespaceKind_1796_; lean_object* v_content_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_kind_1792_ = lean_ctor_get_uint8(v_x_1791_, sizeof(void*)*3);
v_placement_1793_ = lean_ctor_get_uint8(v_x_1791_, sizeof(void*)*3 + 1);
v_originalTokenRange_1794_ = lean_ctor_get(v_x_1791_, 0);
lean_inc_ref(v_originalTokenRange_1794_);
v_originalWhitespaceRange_1795_ = lean_ctor_get(v_x_1791_, 1);
lean_inc_ref(v_originalWhitespaceRange_1795_);
v_originalWhitespaceKind_1796_ = lean_ctor_get_uint8(v_x_1791_, sizeof(void*)*3 + 2);
v_content_1797_ = lean_ctor_get(v_x_1791_, 2);
lean_inc_ref(v_content_1797_);
lean_dec_ref(v_x_1791_);
v___x_1798_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_1799_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__3));
v___x_1800_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__4, &l_Lean_Fmt_instReprComment_repr___redArg___closed__4_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__4);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = l_Lean_Fmt_Comment_instReprKind_repr(v_kind_1792_, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1800_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = 0;
v___x_1805_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1799_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_box(1);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__6));
v___x_1812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1798_);
v___x_1814_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__7, &l_Lean_Fmt_instReprComment_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__7);
v___x_1815_ = l_Lean_Fmt_Comment_instReprPlacement_repr(v_placement_1793_, v___x_1801_);
v___x_1816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*1, v___x_1804_);
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1807_);
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1809_);
v___x_1821_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__9));
v___x_1822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1798_);
v___x_1824_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__10, &l_Lean_Fmt_instReprComment_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__10);
v___x_1825_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalTokenRange_1794_);
v___x_1826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v___x_1804_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1807_);
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1809_);
v___x_1831_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__12));
v___x_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1798_);
v___x_1834_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_1835_ = l_Lean_Syntax_instReprRange_repr___redArg(v_originalWhitespaceRange_1795_);
v___x_1836_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*1, v___x_1804_);
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1833_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1807_);
v___x_1840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v___x_1809_);
v___x_1841_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__14));
v___x_1842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1798_);
v___x_1844_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_1845_ = l_Lean_Fmt_Comment_instReprWhitespace_repr(v_originalWhitespaceKind_1796_, v___x_1801_);
v___x_1846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*1, v___x_1804_);
v___x_1848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1843_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1807_);
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1809_);
v___x_1851_ = ((lean_object*)(l_Lean_Fmt_instReprComment_repr___redArg___closed__16));
v___x_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1798_);
v___x_1854_ = lean_obj_once(&l_Lean_Fmt_instReprComment_repr___redArg___closed__17, &l_Lean_Fmt_instReprComment_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprComment_repr___redArg___closed__17);
v___x_1855_ = l_Array_repr___at___00Lean_Fmt_instReprComment_repr_spec__0(v_content_1797_);
v___x_1856_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*1, v___x_1804_);
v___x_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1853_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_1860_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1858_);
v___x_1862_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1859_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*1, v___x_1804_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr(lean_object* v_x_1866_, lean_object* v_prec_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Fmt_instReprComment_repr___redArg(v_x_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprComment_repr___boxed(lean_object* v_x_1869_, lean_object* v_prec_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Fmt_instReprComment_repr(v_x_1869_, v_prec_1870_);
lean_dec(v_prec_1870_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object* v_entry_1874_, lean_object* v_as_1875_, lean_object* v_j_1876_){
_start:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_array_get_size(v_as_1875_);
v___x_1878_ = lean_nat_dec_lt(v_j_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec(v_j_1876_);
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v_priority_1881_; lean_object* v_priority_1882_; uint8_t v___x_1883_; 
v___x_1880_ = lean_array_fget_borrowed(v_as_1875_, v_j_1876_);
v_priority_1881_ = lean_ctor_get(v___x_1880_, 0);
v_priority_1882_ = lean_ctor_get(v_entry_1874_, 0);
v___x_1883_ = lean_nat_dec_lt(v_priority_1881_, v_priority_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_add(v_j_1876_, v___x_1884_);
lean_dec(v_j_1876_);
v_j_1876_ = v___x_1885_;
goto _start;
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_j_1876_);
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object* v_entry_1888_, lean_object* v_as_1889_, lean_object* v_j_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1888_, v_as_1889_, v_j_1890_);
lean_dec_ref(v_as_1889_);
lean_dec_ref(v_entry_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object* v_collectors_1892_, lean_object* v_entry_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1893_, v_collectors_1892_, v___x_1894_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_array_get_size(v_collectors_1892_);
v___x_1897_ = l_Array_insertIdx_x21___redArg(v_collectors_1892_, v___x_1896_, v_entry_1893_);
return v___x_1897_;
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1899_; 
v_val_1898_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1899_ = l_Array_insertIdx_x21___redArg(v_collectors_1892_, v_val_1898_, v_entry_1893_);
lean_dec(v_val_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_));
v___x_1904_ = lean_st_mk_ref(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object* v_priority_1908_, lean_object* v_collector_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_1912_ = lean_st_ref_take(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_priority_1908_);
lean_ctor_set(v___x_1913_, 1, v_collector_1909_);
v___x_1914_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v___x_1912_, v___x_1913_);
v___x_1915_ = lean_st_ref_put(v___x_1911_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object* v_priority_1917_, lean_object* v_collector_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Fmt_addBuiltinCommentCollector(v_priority_1917_, v_collector_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object* v_constName_1926_, lean_object* v_env_1927_, lean_object* v_opts_1928_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
v___x_1930_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1927_, v_opts_1928_, v___x_1929_, v_constName_1926_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object* v_constName_1931_, lean_object* v_env_1932_, lean_object* v_opts_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(v_constName_1931_, v_env_1932_, v_opts_1933_);
lean_dec_ref(v_opts_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object* v_constName_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_env_1938_; lean_object* v_opts_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_env_1938_ = lean_ctor_get(v_a_1936_, 0);
v_opts_1939_ = lean_ctor_get(v_a_1936_, 1);
v___x_1940_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
lean_inc_ref(v_env_1938_);
v___x_1941_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1938_, v_opts_1939_, v___x_1940_, v_constName_1935_);
v___x_1942_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object* v_constName_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_constName_1943_, v_a_1944_);
lean_dec_ref(v_a_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1947_){
_start:
{
lean_object* v_fst_1948_; 
v_fst_1948_ = lean_ctor_get(v_x_1947_, 0);
lean_inc(v_fst_1948_);
return v_fst_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1949_);
lean_dec_ref(v_x_1949_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_box(0);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1953_);
lean_dec_ref(v_x_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1955_, lean_object* v_s_1956_){
_start:
{
lean_object* v_fst_1957_; lean_object* v___x_1958_; 
v_fst_1957_ = lean_ctor_get(v_s_1956_, 0);
lean_inc_n(v_fst_1957_, 3);
v___x_1958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1958_, 0, v_fst_1957_);
lean_ctor_set(v___x_1958_, 1, v_fst_1957_);
lean_ctor_set(v___x_1958_, 2, v_fst_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_x_1959_, lean_object* v_s_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v_x_1959_, v_s_1960_);
lean_dec_ref(v_s_1960_);
lean_dec_ref(v_x_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v_snd_1964_; lean_object* v_fst_1965_; lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1985_; 
v_snd_1964_ = lean_ctor_get(v_x_1963_, 1);
lean_inc(v_snd_1964_);
v_fst_1965_ = lean_ctor_get(v_x_1962_, 0);
v_snd_1966_ = lean_ctor_get(v_x_1962_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_x_1962_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1968_ = v_x_1962_;
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_inc(v_fst_1965_);
lean_dec(v_x_1962_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_fst_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_fst_1970_ = lean_ctor_get(v_x_1963_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_x_1963_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_x_1963_, 1);
lean_dec(v_unused_1984_);
v___x_1972_ = v_x_1963_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_fst_1970_);
lean_dec(v_x_1963_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_priority_1974_; lean_object* v___x_1976_; 
v_priority_1974_ = lean_ctor_get(v_snd_1964_, 0);
lean_inc(v_priority_1974_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v_priority_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_fst_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_priority_1974_);
v___x_1976_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_array_push(v_fst_1965_, v___x_1976_);
v___x_1978_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_snd_1966_, v_snd_1964_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_1978_);
lean_ctor_set(v___x_1968_, 0, v___x_1977_);
v___x_1980_ = v___x_1968_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_1986_, lean_object* v___x_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = lean_st_ref_get(v___x_1986_);
v___x_1990_ = lean_mk_empty_array_with_capacity(v___x_1987_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1989_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_1993_, lean_object* v___x_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_1993_, v___x_1994_);
lean_dec(v___x_1994_);
lean_dec(v___x_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(lean_object* v_as_1997_, size_t v_i_1998_, size_t v_stop_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_eq(v_i_1998_, v_stop_1999_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v_fst_2005_; lean_object* v_snd_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2027_; 
v___x_2004_ = lean_array_uget(v_as_1997_, v_i_1998_);
v_fst_2005_ = lean_ctor_get(v___x_2004_, 0);
v_snd_2006_ = lean_ctor_get(v___x_2004_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2008_ = v___x_2004_;
v_isShared_2009_ = v_isSharedCheck_2027_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snd_2006_);
lean_inc(v_fst_2005_);
lean_dec(v___x_2004_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2027_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_fst_2005_, v___y_2001_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v_a_2011_);
lean_ctor_set(v___x_2008_, 0, v_snd_2006_);
v___x_2013_ = v___x_2008_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_snd_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_a_2011_);
v___x_2013_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; 
v___x_2014_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_b_2000_, v___x_2013_);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_1998_, v___x_2015_);
v_i_1998_ = v___x_2016_;
v_b_2000_ = v___x_2014_;
goto _start;
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_2008_);
lean_dec(v_snd_2006_);
lean_dec_ref(v_b_2000_);
v_a_2019_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2010_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2010_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_b_2000_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_2029_, lean_object* v_i_2030_, lean_object* v_stop_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
size_t v_i_boxed_2035_; size_t v_stop_boxed_2036_; lean_object* v_res_2037_; 
v_i_boxed_2035_ = lean_unbox_usize(v_i_2030_);
lean_dec(v_i_2030_);
v_stop_boxed_2036_ = lean_unbox_usize(v_stop_2031_);
lean_dec(v_stop_2031_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v_as_2029_, v_i_boxed_2035_, v_stop_boxed_2036_, v_b_2032_, v___y_2033_);
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_as_2029_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(lean_object* v_as_2038_, size_t v_i_2039_, size_t v_stop_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_a_2045_; uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_eq(v_i_2039_, v_stop_2040_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_array_uget_borrowed(v_as_2038_, v_i_2039_);
v___x_2052_ = lean_array_get_size(v___x_2051_);
v___x_2053_ = lean_nat_dec_lt(v___x_2050_, v___x_2052_);
if (v___x_2053_ == 0)
{
v_a_2045_ = v_b_2041_;
goto v___jp_2044_;
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = lean_usize_of_nat(v___x_2052_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__0(v___x_2051_, v___x_2054_, v___x_2055_, v_b_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v_a_2045_ = v_a_2057_;
goto v___jp_2044_;
}
else
{
return v___x_2056_;
}
}
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2041_);
return v___x_2058_;
}
v___jp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2039_, v___x_2046_);
v_i_2039_ = v___x_2047_;
v_b_2041_ = v_a_2045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_2059_, lean_object* v_i_2060_, lean_object* v_stop_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
size_t v_i_boxed_2065_; size_t v_stop_boxed_2066_; lean_object* v_res_2067_; 
v_i_boxed_2065_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_stop_boxed_2066_ = lean_unbox_usize(v_stop_2061_);
lean_dec(v_stop_2061_);
v_res_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2059_, v_i_boxed_2065_, v_stop_boxed_2066_, v_b_2062_, v___y_2063_);
lean_dec_ref(v___y_2063_);
lean_dec_ref(v_as_2059_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v_as_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_a_2074_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2078_ = lean_st_ref_get(v___x_2069_);
v___x_2079_ = lean_array_get_size(v_as_2070_);
v___x_2080_ = lean_nat_dec_lt(v___x_2068_, v___x_2079_);
if (v___x_2080_ == 0)
{
v_a_2074_ = v___x_2078_;
goto v___jp_2073_;
}
else
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = lean_usize_of_nat(v___x_2079_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__spec__1(v_as_2070_, v___x_2081_, v___x_2082_, v___x_2078_, v___y_2071_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v_a_2074_ = v_a_2084_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2083_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2083_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_mk_empty_array_with_capacity(v___x_2068_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_a_2074_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v_as_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(v___x_2093_, v___x_2094_, v_as_2095_, v___y_2096_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v_as_2095_);
lean_dec(v___x_2094_);
lean_dec(v___x_2093_);
return v_res_2098_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___f_2109_; 
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_2109_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_2109_, 0, v___x_2108_);
lean_closure_set(v___f_2109_, 1, v___x_2107_);
return v___f_2109_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___f_2112_; 
v___x_2110_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_2111_ = lean_unsigned_to_nat(0u);
v___f_2112_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_2112_, 0, v___x_2111_);
lean_closure_set(v___f_2112_, 1, v___x_2110_);
return v___f_2112_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2113_ = 0;
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_box(2);
v___f_2116_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2117_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2118_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___f_2119_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___f_2120_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2121_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2122_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___f_2120_);
lean_ctor_set(v___x_2122_, 2, v___f_2119_);
lean_ctor_set(v___x_2122_, 3, v___f_2118_);
lean_ctor_set(v___x_2122_, 4, v___f_2117_);
lean_ctor_set(v___x_2122_, 5, v___f_2116_);
lean_ctor_set(v___x_2122_, 6, v___x_2115_);
lean_ctor_set(v___x_2122_, 7, v___x_2114_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*8, v___x_2113_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*8 + 1, v___x_2113_);
return v___x_2122_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___f_2123_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_));
v___x_2124_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___f_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_);
v___x_2128_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2____boxed(lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3985394414____hygCtx___hyg_2_();
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object* v_env_2131_){
_start:
{
lean_object* v___x_2132_; lean_object* v_toEnvExtension_2133_; lean_object* v_asyncMode_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v_snd_2139_; 
v___x_2132_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2133_ = lean_ctor_get(v___x_2132_, 0);
v_asyncMode_2134_ = lean_ctor_get(v_toEnvExtension_2133_, 2);
v___x_2135_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_2136_ = lean_box(0);
v___x_2137_ = 0;
v___x_2138_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2135_, v___x_2132_, v_env_2131_, v_asyncMode_2134_, v___x_2136_, v___x_2137_);
v_snd_2139_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2139_);
lean_dec(v___x_2138_);
return v_snd_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v_addEntryFn_2140_, lean_object* v___x_2141_, lean_object* v_s_2142_){
_start:
{
lean_object* v_importedEntries_2143_; lean_object* v_state_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2152_; 
v_importedEntries_2143_ = lean_ctor_get(v_s_2142_, 0);
v_state_2144_ = lean_ctor_get(v_s_2142_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_s_2142_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2146_ = v_s_2142_;
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_state_2144_);
lean_inc(v_importedEntries_2143_);
lean_dec(v_s_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_state_2148_; lean_object* v___x_2150_; 
v_state_2148_ = lean_apply_2(v_addEntryFn_2140_, v_state_2144_, v___x_2141_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_state_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_importedEntries_2143_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_state_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v___x_2155_, lean_object* v___x_2156_, lean_object* v_decl_2157_, lean_object* v_stx_2158_, uint8_t v_kind_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Attribute_Builtin_getPrio(v_stx_2158_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___x_2223_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
lean_inc(v_decl_2157_);
lean_inc(v___x_2156_);
v___x_2223_ = l_Lean_ensureAttrDeclIsMeta(v___x_2156_, v_decl_2157_, v_kind_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2223_) == 0)
{
uint8_t v___x_2224_; uint8_t v___x_2225_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2224_ = 0;
v___x_2225_ = l_Lean_instBEqAttributeKind_beq(v_kind_2159_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec(v_a_2164_);
lean_dec(v_decl_2157_);
lean_dec_ref(v___x_2155_);
lean_dec_ref(v___x_2154_);
lean_dec(v___x_2153_);
v___x_2226_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v___x_2156_, v_kind_2159_, v___y_2160_, v___y_2161_);
return v___x_2226_;
}
else
{
v___y_2204_ = v___y_2160_;
v___y_2205_ = v___y_2161_;
goto v___jp_2203_;
}
}
else
{
lean_dec(v_a_2164_);
lean_dec(v_decl_2157_);
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
lean_dec_ref(v___x_2154_);
lean_dec(v___x_2153_);
return v___x_2223_;
}
v___jp_2165_:
{
lean_object* v___x_2168_; lean_object* v_env_2169_; lean_object* v_ref_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2168_ = lean_st_ref_get(v___y_2167_);
v_env_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2168_);
v_ref_2170_ = lean_ctor_get(v___y_2166_, 2);
v___x_2171_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2166_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_env_2169_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
lean_inc(v_decl_2157_);
v___x_2173_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_decl_2157_, v___x_2172_);
lean_dec_ref_known(v___x_2172_, 2);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v___x_2178_; lean_object* v_toEnvExtension_2179_; lean_object* v_addEntryFn_2180_; lean_object* v_asyncMode_2181_; uint8_t v_logWrites_2182_; lean_object* v___x_2183_; lean_object* v___f_2184_; uint8_t v___x_2185_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v_a_2164_);
lean_ctor_set(v___x_2175_, 1, v_a_2174_);
v___x_2176_ = lean_st_ref_get(v___y_2167_);
v_env_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_ref(v_env_2177_);
lean_dec(v___x_2176_);
v___x_2178_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_2179_ = lean_ctor_get(v___x_2178_, 0);
v_addEntryFn_2180_ = lean_ctor_get(v___x_2178_, 3);
v_asyncMode_2181_ = lean_ctor_get(v_toEnvExtension_2179_, 2);
v_logWrites_2182_ = lean_ctor_get_uint8(v_toEnvExtension_2179_, sizeof(void*)*6);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_decl_2157_);
lean_ctor_set(v___x_2183_, 1, v___x_2175_);
lean_inc(v_addEntryFn_2180_);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_2184_, 0, v_addEntryFn_2180_);
lean_closure_set(v___f_2184_, 1, v___x_2183_);
v___x_2185_ = 1;
if (v_logWrites_2182_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_inc_ref(v_toEnvExtension_2179_);
v___x_2186_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2179_, v_env_2177_, v___f_2184_, v_asyncMode_2181_, v___x_2153_, v___x_2185_);
v___x_2187_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2186_, v___y_2167_);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_inc_ref_n(v_toEnvExtension_2179_, 2);
v___x_2188_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2179_, v_env_2177_);
lean_dec_ref(v_env_2177_);
v___x_2189_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2179_, v___x_2188_, v___f_2184_, v_asyncMode_2181_, v___x_2153_, v___x_2185_);
v___x_2190_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_2189_, v___y_2167_);
return v___x_2190_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_a_2164_);
lean_dec(v_decl_2157_);
lean_dec(v___x_2153_);
v_a_2191_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2193_ = v___x_2173_;
v_isShared_2194_ = v_isSharedCheck_2202_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2173_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2202_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2195_ = lean_io_error_to_string(v_a_2191_);
v___x_2196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
v___x_2197_ = l_Lean_MessageData_ofFormat(v___x_2196_);
lean_inc(v_ref_2170_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_ref_2170_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2198_);
v___x_2200_ = v___x_2193_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
v___jp_2203_:
{
lean_object* v___x_2206_; 
lean_inc(v_decl_2157_);
v___x_2206_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_2157_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v___x_2208_ = l_Lean_ConstantInfo_type(v_a_2207_);
lean_dec(v_a_2207_);
v___x_2209_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0));
v___x_2210_ = l_Lean_Name_mkStr3(v___x_2154_, v___x_2155_, v___x_2209_);
v___x_2211_ = l_Lean_Expr_isConstOf(v___x_2208_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_a_2164_);
lean_dec(v___x_2153_);
v___x_2212_ = lean_box(0);
v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
v___x_2214_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v___x_2156_, v_decl_2157_, v___x_2208_, v___x_2213_, v___y_2204_, v___y_2205_);
return v___x_2214_;
}
else
{
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2208_);
lean_dec(v___x_2156_);
v___y_2166_ = v___y_2204_;
v___y_2167_ = v___y_2205_;
goto v___jp_2165_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2164_);
lean_dec(v_decl_2157_);
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
lean_dec_ref(v___x_2154_);
lean_dec(v___x_2153_);
v_a_2215_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2206_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2206_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_decl_2157_);
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
lean_dec_ref(v___x_2154_);
lean_dec(v___x_2153_);
v_a_2227_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2163_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2163_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v___x_2235_, lean_object* v___x_2236_, lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v_decl_2239_, lean_object* v_stx_2240_, lean_object* v_kind_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v_kind_boxed_2245_; lean_object* v_res_2246_; 
v_kind_boxed_2245_ = lean_unbox(v_kind_2241_);
v_res_2246_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(v___x_2235_, v___x_2236_, v___x_2237_, v___x_2238_, v_decl_2239_, v_stx_2240_, v_kind_boxed_2245_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2246_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_unsigned_to_nat(3853185248u);
v___x_2248_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2249_ = l_Lean_Name_num___override(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2251_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2252_ = l_Lean_Name_str___override(v___x_2251_, v___x_2250_);
return v___x_2252_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_));
v___x_2254_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2255_ = l_Lean_Name_str___override(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2258_ = l_Lean_Name_num___override(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2270_ = 1;
v___x_2271_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2272_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2273_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2274_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2272_);
lean_ctor_set(v___x_2274_, 2, v___x_2271_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*3, v___x_2270_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___f_2275_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___f_2276_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_));
v___x_2277_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___f_2276_);
lean_ctor_set(v___x_2278_, 2, v___f_2275_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_);
v___x_2281_ = l_Lean_registerBuiltinAttribute(v___x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2____boxed(lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3853185248____hygCtx___hyg_2_();
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object* v_attr_2284_, lean_object* v_mk_2285_, lean_object* v_env_2286_, lean_object* v_kind_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v_attr_2284_, v_env_2286_, v_kind_2287_);
v___x_2289_ = l_List_head_x3f___redArg(v___x_2288_);
lean_dec(v___x_2288_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref(v_mk_2285_);
v___x_2290_ = lean_box(0);
return v___x_2290_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2310_; 
v_val_2291_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2293_ = v___x_2289_;
v_isShared_2294_ = v_isSharedCheck_2310_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_val_2291_);
lean_dec(v___x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2310_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_toOLeanEntry_2295_; lean_object* v_value_2296_; lean_object* v_declName_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2308_; 
v_toOLeanEntry_2295_ = lean_ctor_get(v_val_2291_, 0);
lean_inc_ref(v_toOLeanEntry_2295_);
v_value_2296_ = lean_ctor_get(v_val_2291_, 1);
lean_inc(v_value_2296_);
lean_dec(v_val_2291_);
v_declName_2297_ = lean_ctor_get(v_toOLeanEntry_2295_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_toOLeanEntry_2295_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_toOLeanEntry_2295_, 0);
lean_dec(v_unused_2309_);
v___x_2299_ = v_toOLeanEntry_2295_;
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_declName_2297_);
lean_dec(v_toOLeanEntry_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_apply_1(v_mk_2285_, v_value_2296_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 1, v___x_2301_);
lean_ctor_set(v___x_2299_, 0, v_declName_2297_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_declName_2297_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2303_);
v___x_2305_ = v___x_2293_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object* v_attr_2311_, lean_object* v_mk_2312_, lean_object* v_env_2313_, lean_object* v_kind_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2311_, v_mk_2312_, v_env_2313_, v_kind_2314_);
lean_dec(v_kind_2314_);
lean_dec_ref(v_attr_2311_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object* v_00_u03b1_2316_, lean_object* v_attr_2317_, lean_object* v_mk_2318_, lean_object* v_env_2319_, lean_object* v_x_2320_, lean_object* v_kind_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_2317_, v_mk_2318_, v_env_2319_, v_kind_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object* v_00_u03b1_2323_, lean_object* v_attr_2324_, lean_object* v_mk_2325_, lean_object* v_env_2326_, lean_object* v_x_2327_, lean_object* v_kind_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Fmt_keyedFmtProvider(v_00_u03b1_2323_, v_attr_2324_, v_mk_2325_, v_env_2326_, v_x_2327_, v_kind_2328_);
lean_dec(v_kind_2328_);
lean_dec_ref(v_x_2327_);
lean_dec_ref(v_attr_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_2330_, lean_object* v_i_2331_, lean_object* v_k_2332_){
_start:
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = lean_array_get_size(v_keys_2330_);
v___x_2334_ = lean_nat_dec_lt(v_i_2331_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec(v_i_2331_);
return v___x_2334_;
}
else
{
lean_object* v_k_x27_2335_; uint8_t v___x_2336_; 
v_k_x27_2335_ = lean_array_fget_borrowed(v_keys_2330_, v_i_2331_);
v___x_2336_ = l_Lean_instBEqExtraModUse_beq(v_k_2332_, v_k_x27_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = lean_nat_add(v_i_2331_, v___x_2337_);
lean_dec(v_i_2331_);
v_i_2331_ = v___x_2338_;
goto _start;
}
else
{
lean_dec(v_i_2331_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_2340_, lean_object* v_i_2341_, lean_object* v_k_2342_){
_start:
{
uint8_t v_res_2343_; lean_object* v_r_2344_; 
v_res_2343_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2340_, v_i_2341_, v_k_2342_);
lean_dec_ref(v_k_2342_);
lean_dec_ref(v_keys_2340_);
v_r_2344_ = lean_box(v_res_2343_);
return v_r_2344_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_2345_, size_t v_x_2346_, lean_object* v_x_2347_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
lean_object* v_es_2348_; lean_object* v___x_2349_; size_t v___x_2350_; size_t v___x_2351_; lean_object* v_j_2352_; lean_object* v___x_2353_; 
v_es_2348_ = lean_ctor_get(v_x_2345_, 0);
v___x_2349_ = lean_box(2);
v___x_2350_ = ((size_t)31ULL);
v___x_2351_ = lean_usize_land(v_x_2346_, v___x_2350_);
v_j_2352_ = lean_usize_to_nat(v___x_2351_);
v___x_2353_ = lean_array_get_borrowed(v___x_2349_, v_es_2348_, v_j_2352_);
lean_dec(v_j_2352_);
switch(lean_obj_tag(v___x_2353_))
{
case 0:
{
lean_object* v_key_2354_; uint8_t v___x_2355_; 
v_key_2354_ = lean_ctor_get(v___x_2353_, 0);
v___x_2355_ = l_Lean_instBEqExtraModUse_beq(v_x_2347_, v_key_2354_);
return v___x_2355_;
}
case 1:
{
lean_object* v_node_2356_; size_t v___x_2357_; size_t v___x_2358_; 
v_node_2356_ = lean_ctor_get(v___x_2353_, 0);
v___x_2357_ = ((size_t)5ULL);
v___x_2358_ = lean_usize_shift_right(v_x_2346_, v___x_2357_);
v_x_2345_ = v_node_2356_;
v_x_2346_ = v___x_2358_;
goto _start;
}
default: 
{
uint8_t v___x_2360_; 
v___x_2360_ = 0;
return v___x_2360_;
}
}
}
else
{
lean_object* v_ks_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_ks_2361_ = lean_ctor_get(v_x_2345_, 0);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_2361_, v___x_2362_, v_x_2347_);
return v___x_2363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_){
_start:
{
size_t v_x_5189__boxed_2367_; uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_x_5189__boxed_2367_ = lean_unbox_usize(v_x_2365_);
lean_dec(v_x_2365_);
v_res_2368_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2364_, v_x_5189__boxed_2367_, v_x_2366_);
lean_dec_ref(v_x_2366_);
lean_dec_ref(v_x_2364_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
uint64_t v___x_2372_; size_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2372_ = l_Lean_instHashableExtraModUse_hash(v_x_2371_);
v___x_2373_ = lean_uint64_to_usize(v___x_2372_);
v___x_2374_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2370_, v___x_2373_, v_x_2371_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2375_, v_x_2376_);
lean_dec_ref(v_x_2376_);
lean_dec_ref(v_x_2375_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0(lean_object* v___x_2379_, lean_object* v_entry_2380_, lean_object* v_s_2381_){
_start:
{
lean_object* v_addEntryFn_2382_; lean_object* v_importedEntries_2383_; lean_object* v_state_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2392_; 
v_addEntryFn_2382_ = lean_ctor_get(v___x_2379_, 3);
lean_inc(v_addEntryFn_2382_);
lean_dec_ref(v___x_2379_);
v_importedEntries_2383_ = lean_ctor_get(v_s_2381_, 0);
v_state_2384_ = lean_ctor_get(v_s_2381_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_s_2381_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2386_ = v_s_2381_;
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_state_2384_);
lean_inc(v_importedEntries_2383_);
lean_dec(v_s_2381_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_state_2388_; lean_object* v___x_2390_; 
v_state_2388_ = lean_apply_2(v_addEntryFn_2382_, v_state_2384_, v_entry_2380_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v_state_2388_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_importedEntries_2383_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_state_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2393_; double v___x_2394_; 
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2394_ = lean_float_of_nat(v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object* v_cls_2398_, lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_ref_2403_; lean_object* v___x_2404_; lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2450_; 
v_ref_2403_ = lean_ctor_get(v___y_2400_, 2);
v___x_2404_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0_spec__0(v_msg_2399_, v___y_2400_, v___y_2401_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2450_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2450_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v_traceState_2410_; lean_object* v_env_2411_; lean_object* v_nextMacroScope_2412_; lean_object* v_ngen_2413_; lean_object* v_auxDeclNGen_2414_; lean_object* v_cache_2415_; lean_object* v_recordedDeps_2416_; lean_object* v_messages_2417_; lean_object* v_infoState_2418_; lean_object* v_snapshotTasks_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2449_; 
v___x_2409_ = lean_st_ref_take(v___y_2401_);
v_traceState_2410_ = lean_ctor_get(v___x_2409_, 4);
v_env_2411_ = lean_ctor_get(v___x_2409_, 0);
v_nextMacroScope_2412_ = lean_ctor_get(v___x_2409_, 1);
v_ngen_2413_ = lean_ctor_get(v___x_2409_, 2);
v_auxDeclNGen_2414_ = lean_ctor_get(v___x_2409_, 3);
v_cache_2415_ = lean_ctor_get(v___x_2409_, 5);
v_recordedDeps_2416_ = lean_ctor_get(v___x_2409_, 6);
v_messages_2417_ = lean_ctor_get(v___x_2409_, 7);
v_infoState_2418_ = lean_ctor_get(v___x_2409_, 8);
v_snapshotTasks_2419_ = lean_ctor_get(v___x_2409_, 9);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2421_ = v___x_2409_;
v_isShared_2422_ = v_isSharedCheck_2449_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snapshotTasks_2419_);
lean_inc(v_infoState_2418_);
lean_inc(v_messages_2417_);
lean_inc(v_recordedDeps_2416_);
lean_inc(v_cache_2415_);
lean_inc(v_traceState_2410_);
lean_inc(v_auxDeclNGen_2414_);
lean_inc(v_ngen_2413_);
lean_inc(v_nextMacroScope_2412_);
lean_inc(v_env_2411_);
lean_dec(v___x_2409_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2449_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
uint64_t v_tid_2423_; lean_object* v_traces_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2448_; 
v_tid_2423_ = lean_ctor_get_uint64(v_traceState_2410_, sizeof(void*)*1);
v_traces_2424_ = lean_ctor_get(v_traceState_2410_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_traceState_2410_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2426_ = v_traceState_2410_;
v_isShared_2427_ = v_isSharedCheck_2448_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_traces_2424_);
lean_dec(v_traceState_2410_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2448_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; double v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0);
v___x_2431_ = 0;
v___x_2432_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2433_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2433_, 0, v_cls_2398_);
lean_ctor_set(v___x_2433_, 1, v___x_2429_);
lean_ctor_set(v___x_2433_, 2, v___x_2432_);
lean_ctor_set_float(v___x_2433_, sizeof(void*)*3, v___x_2430_);
lean_ctor_set_float(v___x_2433_, sizeof(void*)*3 + 8, v___x_2430_);
lean_ctor_set_uint8(v___x_2433_, sizeof(void*)*3 + 16, v___x_2431_);
v___x_2434_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2));
v___x_2435_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v_a_2405_);
lean_ctor_set(v___x_2435_, 2, v___x_2434_);
lean_inc(v_ref_2403_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_ref_2403_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_PersistentArray_push___redArg(v_traces_2424_, v___x_2436_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2437_);
v___x_2439_ = v___x_2426_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2437_);
lean_ctor_set_uint64(v_reuseFailAlloc_2447_, sizeof(void*)*1, v_tid_2423_);
v___x_2439_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2441_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2439_);
v___x_2441_ = v___x_2421_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_env_2411_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_nextMacroScope_2412_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_ngen_2413_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_auxDeclNGen_2414_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v_cache_2415_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_recordedDeps_2416_);
lean_ctor_set(v_reuseFailAlloc_2446_, 7, v_messages_2417_);
lean_ctor_set(v_reuseFailAlloc_2446_, 8, v_infoState_2418_);
lean_ctor_set(v_reuseFailAlloc_2446_, 9, v_snapshotTasks_2419_);
v___x_2441_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2442_ = lean_st_ref_put(v___y_2401_, v___x_2441_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2428_);
v___x_2444_ = v___x_2407_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2428_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2451_, lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2451_, v_msg_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2456_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3));
v___x_2463_ = l_Lean_stringToMessageData(v___x_2462_);
return v___x_2463_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5));
v___x_2466_ = l_Lean_stringToMessageData(v___x_2465_);
return v___x_2466_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v_cls_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_cls_2472_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2473_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9));
v___x_2474_ = l_Lean_Name_append(v___x_2473_, v_cls_2472_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object* v_mod_2485_, uint8_t v_isMeta_2486_, lean_object* v_hint_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_env_2509_; uint8_t v_isExporting_2510_; lean_object* v_entry_2511_; lean_object* v___x_2512_; lean_object* v_env_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2507_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0);
v___x_2508_ = lean_st_ref_get(v___y_2489_);
v_env_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc_ref(v_env_2509_);
lean_dec(v___x_2508_);
v_isExporting_2510_ = lean_ctor_get_uint8(v_env_2509_, sizeof(void*)*13);
lean_dec_ref(v_env_2509_);
lean_inc(v_mod_2485_);
v_entry_2511_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2511_, 0, v_mod_2485_);
lean_ctor_set_uint8(v_entry_2511_, sizeof(void*)*1, v_isExporting_2510_);
lean_ctor_set_uint8(v_entry_2511_, sizeof(void*)*1 + 1, v_isMeta_2486_);
v___x_2512_ = lean_st_ref_get(v___y_2489_);
v_env_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_env_2513_);
lean_dec(v___x_2512_);
v___x_2514_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2515_ = lean_box(1);
v___x_2516_ = lean_box(0);
v___x_2517_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2507_, v___x_2514_, v_env_2513_, v___x_2515_, v___x_2516_);
v___x_2518_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v___x_2517_, v_entry_2511_);
lean_dec(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v_toCold_2519_; lean_object* v_options_2520_; lean_object* v_inheritedTraceOptions_2521_; uint8_t v_hasTrace_2522_; lean_object* v___f_2523_; uint8_t v___x_2524_; lean_object* v___y_2526_; 
v_toCold_2519_ = lean_ctor_get(v___y_2488_, 0);
v_options_2520_ = lean_ctor_get(v_toCold_2519_, 2);
v_inheritedTraceOptions_2521_ = lean_ctor_get(v_toCold_2519_, 11);
v_hasTrace_2522_ = lean_ctor_get_uint8(v_options_2520_, sizeof(void*)*1);
v___f_2523_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2523_, 0, v___x_2514_);
lean_closure_set(v___f_2523_, 1, v_entry_2511_);
v___x_2524_ = 1;
if (v_hasTrace_2522_ == 0)
{
lean_dec(v_hint_2487_);
lean_dec(v_mod_2485_);
v___y_2526_ = v___y_2489_;
goto v___jp_2525_;
}
else
{
lean_object* v_cls_2544_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_cls_2544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2));
v___x_2564_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10);
v___x_2565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2521_, v_options_2520_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_dec(v_hint_2487_);
lean_dec(v_mod_2485_);
v___y_2526_ = v___y_2489_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2566_; lean_object* v___y_2568_; 
v___x_2566_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12);
if (v_isExporting_2510_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17));
v___y_2568_ = v___x_2575_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2576_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18));
v___y_2568_ = v___x_2576_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_inc_ref(v___y_2568_);
v___x_2569_ = l_Lean_stringToMessageData(v___y_2568_);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2566_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
if (v_isMeta_2486_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15));
v___y_2551_ = v___x_2572_;
v___y_2552_ = v___x_2573_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16));
v___y_2551_ = v___x_2572_;
v___y_2552_ = v___x_2574_;
goto v___jp_2550_;
}
}
}
v___jp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2546_);
lean_ctor_set(v___x_2548_, 1, v___y_2547_);
v___x_2549_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_2544_, v___x_2548_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_dec_ref_known(v___x_2549_, 1);
v___y_2526_ = v___y_2489_;
goto v___jp_2525_;
}
else
{
lean_dec_ref(v___f_2523_);
return v___x_2549_;
}
}
v___jp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
lean_inc_ref(v___y_2552_);
v___x_2553_ = l_Lean_stringToMessageData(v___y_2552_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___y_2551_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_Lean_MessageData_ofName(v_mod_2485_);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_Name_isAnonymous(v_hint_2487_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6);
v___x_2561_ = l_Lean_MessageData_ofName(v_hint_2487_);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___y_2546_ = v___x_2558_;
v___y_2547_ = v___x_2562_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2563_; 
lean_dec(v_hint_2487_);
v___x_2563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7);
v___y_2546_ = v___x_2558_;
v___y_2547_ = v___x_2563_;
goto v___jp_2545_;
}
}
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v_toEnvExtension_2528_; lean_object* v_env_2529_; lean_object* v_nextMacroScope_2530_; lean_object* v_ngen_2531_; lean_object* v_auxDeclNGen_2532_; lean_object* v_traceState_2533_; lean_object* v_recordedDeps_2534_; lean_object* v_messages_2535_; lean_object* v_infoState_2536_; lean_object* v_snapshotTasks_2537_; lean_object* v_asyncMode_2538_; uint8_t v_logWrites_2539_; lean_object* v___x_2540_; 
v___x_2527_ = lean_st_ref_take(v___y_2526_);
v_toEnvExtension_2528_ = lean_ctor_get(v___x_2514_, 0);
v_env_2529_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_env_2529_);
v_nextMacroScope_2530_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_nextMacroScope_2530_);
v_ngen_2531_ = lean_ctor_get(v___x_2527_, 2);
lean_inc_ref(v_ngen_2531_);
v_auxDeclNGen_2532_ = lean_ctor_get(v___x_2527_, 3);
lean_inc_ref(v_auxDeclNGen_2532_);
v_traceState_2533_ = lean_ctor_get(v___x_2527_, 4);
lean_inc_ref(v_traceState_2533_);
v_recordedDeps_2534_ = lean_ctor_get(v___x_2527_, 6);
lean_inc_ref(v_recordedDeps_2534_);
v_messages_2535_ = lean_ctor_get(v___x_2527_, 7);
lean_inc_ref(v_messages_2535_);
v_infoState_2536_ = lean_ctor_get(v___x_2527_, 8);
lean_inc_ref(v_infoState_2536_);
v_snapshotTasks_2537_ = lean_ctor_get(v___x_2527_, 9);
lean_inc_ref(v_snapshotTasks_2537_);
lean_dec(v___x_2527_);
v_asyncMode_2538_ = lean_ctor_get(v_toEnvExtension_2528_, 2);
v_logWrites_2539_ = lean_ctor_get_uint8(v_toEnvExtension_2528_, sizeof(void*)*6);
v___x_2540_ = lean_box(0);
if (v_logWrites_2539_ == 0)
{
lean_object* v___x_2541_; 
lean_inc_ref(v_toEnvExtension_2528_);
v___x_2541_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2528_, v_env_2529_, v___f_2523_, v_asyncMode_2538_, v___x_2516_, v___x_2524_);
v___y_2492_ = v_snapshotTasks_2537_;
v___y_2493_ = v_infoState_2536_;
v___y_2494_ = v_messages_2535_;
v___y_2495_ = v_nextMacroScope_2530_;
v___y_2496_ = v_traceState_2533_;
v___y_2497_ = v_auxDeclNGen_2532_;
v___y_2498_ = v___y_2526_;
v___y_2499_ = v_recordedDeps_2534_;
v___y_2500_ = v___x_2540_;
v___y_2501_ = v_ngen_2531_;
v___y_2502_ = v___x_2541_;
goto v___jp_2491_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_inc_ref_n(v_toEnvExtension_2528_, 2);
v___x_2542_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2528_, v_env_2529_);
lean_dec_ref(v_env_2529_);
v___x_2543_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2528_, v___x_2542_, v___f_2523_, v_asyncMode_2538_, v___x_2516_, v___x_2524_);
v___y_2492_ = v_snapshotTasks_2537_;
v___y_2493_ = v_infoState_2536_;
v___y_2494_ = v_messages_2535_;
v___y_2495_ = v_nextMacroScope_2530_;
v___y_2496_ = v_traceState_2533_;
v___y_2497_ = v_auxDeclNGen_2532_;
v___y_2498_ = v___y_2526_;
v___y_2499_ = v_recordedDeps_2534_;
v___y_2500_ = v___x_2540_;
v___y_2501_ = v_ngen_2531_;
v___y_2502_ = v___x_2543_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref_known(v_entry_2511_, 1);
lean_dec(v_hint_2487_);
lean_dec(v_mod_2485_);
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
v___jp_2491_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg___closed__2);
v___x_2504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2504_, 0, v___y_2502_);
lean_ctor_set(v___x_2504_, 1, v___y_2495_);
lean_ctor_set(v___x_2504_, 2, v___y_2501_);
lean_ctor_set(v___x_2504_, 3, v___y_2497_);
lean_ctor_set(v___x_2504_, 4, v___y_2496_);
lean_ctor_set(v___x_2504_, 5, v___x_2503_);
lean_ctor_set(v___x_2504_, 6, v___y_2499_);
lean_ctor_set(v___x_2504_, 7, v___y_2494_);
lean_ctor_set(v___x_2504_, 8, v___y_2493_);
lean_ctor_set(v___x_2504_, 9, v___y_2492_);
v___x_2505_ = lean_st_ref_put(v___y_2498_, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2500_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object* v_mod_2579_, lean_object* v_isMeta_2580_, lean_object* v_hint_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v_isMeta_boxed_2585_; lean_object* v_res_2586_; 
v_isMeta_boxed_2585_ = lean_unbox(v_isMeta_2580_);
v_res_2586_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_mod_2579_, v_isMeta_boxed_2585_, v_hint_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object* v___x_2587_, lean_object* v_declName_2588_, lean_object* v_as_2589_, size_t v_sz_2590_, size_t v_i_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_lt(v_i_2591_, v_sz_2590_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
lean_dec(v_declName_2588_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_b_2592_);
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; lean_object* v_modules_2599_; lean_object* v___x_2600_; lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v_toImport_2603_; lean_object* v_module_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2598_ = l_Lean_Environment_header(v___x_2587_);
v_modules_2599_ = lean_ctor_get(v___x_2598_, 3);
lean_inc_ref(v_modules_2599_);
lean_dec_ref(v___x_2598_);
v___x_2600_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2601_ = lean_array_uget_borrowed(v_as_2589_, v_i_2591_);
v___x_2602_ = lean_array_get(v___x_2600_, v_modules_2599_, v_a_2601_);
lean_dec_ref(v_modules_2599_);
v_toImport_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_toImport_2603_);
lean_dec(v___x_2602_);
v_module_2604_ = lean_ctor_get(v_toImport_2603_, 0);
lean_inc(v_module_2604_);
lean_dec_ref(v_toImport_2603_);
v___x_2605_ = lean_box(0);
v___x_2606_ = 0;
lean_inc(v_declName_2588_);
v___x_2607_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2604_, v___x_2606_, v_declName_2588_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2607_) == 0)
{
size_t v___x_2608_; size_t v___x_2609_; 
lean_dec_ref_known(v___x_2607_, 1);
v___x_2608_ = ((size_t)1ULL);
v___x_2609_ = lean_usize_add(v_i_2591_, v___x_2608_);
v_i_2591_ = v___x_2609_;
v_b_2592_ = v___x_2605_;
goto _start;
}
else
{
lean_dec(v_declName_2588_);
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object* v___x_2611_, lean_object* v_declName_2612_, lean_object* v_as_2613_, lean_object* v_sz_2614_, lean_object* v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
size_t v_sz_boxed_2620_; size_t v_i_boxed_2621_; lean_object* v_res_2622_; 
v_sz_boxed_2620_ = lean_unbox_usize(v_sz_2614_);
lean_dec(v_sz_2614_);
v_i_boxed_2621_ = lean_unbox_usize(v_i_2615_);
lean_dec(v_i_2615_);
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v___x_2611_, v_declName_2612_, v_as_2613_, v_sz_boxed_2620_, v_i_boxed_2621_, v_b_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_as_2613_);
lean_dec_ref(v___x_2611_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2623_, lean_object* v_x_2624_){
_start:
{
if (lean_obj_tag(v_x_2624_) == 0)
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_box(0);
return v___x_2625_;
}
else
{
lean_object* v_key_2626_; lean_object* v_value_2627_; lean_object* v_tail_2628_; uint8_t v___x_2629_; 
v_key_2626_ = lean_ctor_get(v_x_2624_, 0);
v_value_2627_ = lean_ctor_get(v_x_2624_, 1);
v_tail_2628_ = lean_ctor_get(v_x_2624_, 2);
v___x_2629_ = lean_name_eq(v_key_2626_, v_a_2623_);
if (v___x_2629_ == 0)
{
v_x_2624_ = v_tail_2628_;
goto _start;
}
else
{
lean_object* v___x_2631_; 
lean_inc(v_value_2627_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_value_2627_);
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2632_, lean_object* v_x_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2632_, v_x_2633_);
lean_dec(v_x_2633_);
lean_dec(v_a_2632_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object* v_m_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_buckets_2637_; lean_object* v___x_2638_; uint64_t v___y_2640_; 
v_buckets_2637_ = lean_ctor_get(v_m_2635_, 1);
v___x_2638_ = lean_array_get_size(v_buckets_2637_);
if (lean_obj_tag(v_a_2636_) == 0)
{
uint64_t v___x_2654_; 
v___x_2654_ = 1723ULL;
v___y_2640_ = v___x_2654_;
goto v___jp_2639_;
}
else
{
uint64_t v_hash_2655_; 
v_hash_2655_ = lean_ctor_get_uint64(v_a_2636_, sizeof(void*)*2);
v___y_2640_ = v_hash_2655_;
goto v___jp_2639_;
}
v___jp_2639_:
{
uint64_t v___x_2641_; uint64_t v___x_2642_; uint64_t v_fold_2643_; uint64_t v___x_2644_; uint64_t v___x_2645_; uint64_t v___x_2646_; size_t v___x_2647_; size_t v___x_2648_; size_t v___x_2649_; size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2641_ = 32ULL;
v___x_2642_ = lean_uint64_shift_right(v___y_2640_, v___x_2641_);
v_fold_2643_ = lean_uint64_xor(v___y_2640_, v___x_2642_);
v___x_2644_ = 16ULL;
v___x_2645_ = lean_uint64_shift_right(v_fold_2643_, v___x_2644_);
v___x_2646_ = lean_uint64_xor(v_fold_2643_, v___x_2645_);
v___x_2647_ = lean_uint64_to_usize(v___x_2646_);
v___x_2648_ = lean_usize_of_nat(v___x_2638_);
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_sub(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_usize_land(v___x_2647_, v___x_2650_);
v___x_2652_ = lean_array_uget_borrowed(v_buckets_2637_, v___x_2651_);
v___x_2653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2636_, v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object* v_m_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_m_2656_);
return v_res_2658_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object* v_declName_2662_, uint8_t v_isMeta_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_env_2672_; lean_object* v___y_2674_; lean_object* v___x_2687_; 
v___x_2667_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0);
v___x_2668_ = lean_st_ref_get(v___y_2665_);
v_env_2672_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_env_2672_);
lean_dec(v___x_2668_);
v___x_2687_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2672_, v_declName_2662_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_dec_ref(v_env_2672_);
lean_dec(v_declName_2662_);
goto v___jp_2669_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2689_; lean_object* v_modules_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_val_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = l_Lean_Environment_header(v_env_2672_);
v_modules_2690_ = lean_ctor_get(v___x_2689_, 3);
lean_inc_ref(v_modules_2690_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = lean_array_get_size(v_modules_2690_);
v___x_2692_ = lean_nat_dec_lt(v_val_2688_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_dec_ref(v_modules_2690_);
lean_dec(v_val_2688_);
lean_dec_ref(v_env_2672_);
lean_dec(v_declName_2662_);
goto v___jp_2669_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___y_2696_; 
v___x_2693_ = lean_array_fget(v_modules_2690_, v_val_2688_);
lean_dec(v_val_2688_);
lean_dec_ref(v_modules_2690_);
v___x_2694_ = lean_st_ref_get(v___y_2665_);
if (v_isMeta_2663_ == 0)
{
lean_dec(v___x_2694_);
v___y_2696_ = v_isMeta_2663_;
goto v___jp_2695_;
}
else
{
lean_object* v_env_2707_; uint8_t v___x_2708_; 
v_env_2707_ = lean_ctor_get(v___x_2694_, 0);
lean_inc_ref(v_env_2707_);
lean_dec(v___x_2694_);
lean_inc(v_declName_2662_);
v___x_2708_ = l_Lean_isMarkedMeta(v_env_2707_, v_declName_2662_);
if (v___x_2708_ == 0)
{
v___y_2696_ = v_isMeta_2663_;
goto v___jp_2695_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = 0;
v___y_2696_ = v___x_2709_;
goto v___jp_2695_;
}
}
v___jp_2695_:
{
lean_object* v_toImport_2697_; lean_object* v_module_2698_; lean_object* v___x_2699_; 
v_toImport_2697_ = lean_ctor_get(v___x_2693_, 0);
lean_inc_ref(v_toImport_2697_);
lean_dec(v___x_2693_);
v_module_2698_ = lean_ctor_get(v_toImport_2697_, 0);
lean_inc(v_module_2698_);
lean_dec_ref(v_toImport_2697_);
lean_inc(v_declName_2662_);
v___x_2699_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2698_, v___y_2696_, v_declName_2662_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec_ref_known(v___x_2699_, 1);
v___x_2700_ = l_Lean_indirectModUseExt;
v___x_2701_ = lean_box(1);
v___x_2702_ = lean_box(0);
lean_inc_ref(v_env_2672_);
v___x_2703_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2667_, v___x_2700_, v_env_2672_, v___x_2701_, v___x_2702_);
v___x_2704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v___x_2703_, v_declName_2662_);
lean_dec(v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1));
v___y_2674_ = v___x_2705_;
goto v___jp_2673_;
}
else
{
lean_object* v_val_2706_; 
v_val_2706_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_val_2706_);
lean_dec_ref_known(v___x_2704_, 1);
v___y_2674_ = v_val_2706_;
goto v___jp_2673_;
}
}
else
{
lean_dec_ref(v_env_2672_);
lean_dec(v_declName_2662_);
return v___x_2699_;
}
}
}
}
v___jp_2669_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
return v___x_2671_;
}
v___jp_2673_:
{
lean_object* v___x_2675_; size_t v_sz_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = lean_box(0);
v_sz_2676_ = lean_array_size(v___y_2674_);
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v_env_2672_, v_declName_2662_, v___y_2674_, v_sz_2676_, v___x_2677_, v___x_2675_, v___y_2664_, v___y_2665_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_env_2672_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2686_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2675_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2675_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object* v_declName_2710_, lean_object* v_isMeta_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v_isMeta_boxed_2715_; lean_object* v_res_2716_; 
v_isMeta_boxed_2715_ = lean_unbox(v_isMeta_2711_);
v_res_2716_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v_declName_2710_, v_isMeta_boxed_2715_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2716_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object* v_a_2717_, lean_object* v_x_2718_){
_start:
{
if (lean_obj_tag(v_x_2718_) == 0)
{
uint8_t v___x_2719_; 
v___x_2719_ = 0;
return v___x_2719_;
}
else
{
lean_object* v_head_2720_; lean_object* v_tail_2721_; uint8_t v___x_2722_; 
v_head_2720_ = lean_ctor_get(v_x_2718_, 0);
v_tail_2721_ = lean_ctor_get(v_x_2718_, 1);
v___x_2722_ = lean_name_eq(v_a_2717_, v_head_2720_);
if (v___x_2722_ == 0)
{
v_x_2718_ = v_tail_2721_;
goto _start;
}
else
{
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object* v_a_2724_, lean_object* v_x_2725_){
_start:
{
uint8_t v_res_2726_; lean_object* v_r_2727_; 
v_res_2726_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v_a_2724_, v_x_2725_);
lean_dec(v_x_2725_);
lean_dec(v_a_2724_);
v_r_2727_ = lean_box(v_res_2726_);
return v_r_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object* v_t_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v_infoState_2732_; uint8_t v_enabled_2733_; 
v___x_2731_ = lean_st_ref_get(v___y_2729_);
v_infoState_2732_ = lean_ctor_get(v___x_2731_, 8);
lean_inc_ref(v_infoState_2732_);
lean_dec(v___x_2731_);
v_enabled_2733_ = lean_ctor_get_uint8(v_infoState_2732_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2732_);
if (v_enabled_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec_ref(v_t_2728_);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; lean_object* v_infoState_2737_; lean_object* v_env_2738_; lean_object* v_nextMacroScope_2739_; lean_object* v_ngen_2740_; lean_object* v_auxDeclNGen_2741_; lean_object* v_traceState_2742_; lean_object* v_cache_2743_; lean_object* v_recordedDeps_2744_; lean_object* v_messages_2745_; lean_object* v_snapshotTasks_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2768_; 
v___x_2736_ = lean_st_ref_take(v___y_2729_);
v_infoState_2737_ = lean_ctor_get(v___x_2736_, 8);
v_env_2738_ = lean_ctor_get(v___x_2736_, 0);
v_nextMacroScope_2739_ = lean_ctor_get(v___x_2736_, 1);
v_ngen_2740_ = lean_ctor_get(v___x_2736_, 2);
v_auxDeclNGen_2741_ = lean_ctor_get(v___x_2736_, 3);
v_traceState_2742_ = lean_ctor_get(v___x_2736_, 4);
v_cache_2743_ = lean_ctor_get(v___x_2736_, 5);
v_recordedDeps_2744_ = lean_ctor_get(v___x_2736_, 6);
v_messages_2745_ = lean_ctor_get(v___x_2736_, 7);
v_snapshotTasks_2746_ = lean_ctor_get(v___x_2736_, 9);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2748_ = v___x_2736_;
v_isShared_2749_ = v_isSharedCheck_2768_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snapshotTasks_2746_);
lean_inc(v_infoState_2737_);
lean_inc(v_messages_2745_);
lean_inc(v_recordedDeps_2744_);
lean_inc(v_cache_2743_);
lean_inc(v_traceState_2742_);
lean_inc(v_auxDeclNGen_2741_);
lean_inc(v_ngen_2740_);
lean_inc(v_nextMacroScope_2739_);
lean_inc(v_env_2738_);
lean_dec(v___x_2736_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2768_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint8_t v_enabled_2750_; lean_object* v_assignment_2751_; lean_object* v_lazyAssignment_2752_; lean_object* v_trees_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2767_; 
v_enabled_2750_ = lean_ctor_get_uint8(v_infoState_2737_, sizeof(void*)*3);
v_assignment_2751_ = lean_ctor_get(v_infoState_2737_, 0);
v_lazyAssignment_2752_ = lean_ctor_get(v_infoState_2737_, 1);
v_trees_2753_ = lean_ctor_get(v_infoState_2737_, 2);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_infoState_2737_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2755_ = v_infoState_2737_;
v_isShared_2756_ = v_isSharedCheck_2767_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_trees_2753_);
lean_inc(v_lazyAssignment_2752_);
lean_inc(v_assignment_2751_);
lean_dec(v_infoState_2737_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2767_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = l_Lean_PersistentArray_push___redArg(v_trees_2753_, v_t_2728_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 2, v___x_2758_);
v___x_2760_ = v___x_2755_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_assignment_2751_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_lazyAssignment_2752_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v___x_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2766_, sizeof(void*)*3, v_enabled_2750_);
v___x_2760_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 8, v___x_2760_);
v___x_2762_ = v___x_2748_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_env_2738_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_nextMacroScope_2739_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_ngen_2740_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_auxDeclNGen_2741_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v_traceState_2742_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_cache_2743_);
lean_ctor_set(v_reuseFailAlloc_2765_, 6, v_recordedDeps_2744_);
lean_ctor_set(v_reuseFailAlloc_2765_, 7, v_messages_2745_);
lean_ctor_set(v_reuseFailAlloc_2765_, 8, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2765_, 9, v_snapshotTasks_2746_);
v___x_2762_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_st_ref_put(v___y_2729_, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2757_);
return v___x_2764_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2769_, v___y_2770_);
lean_dec(v___y_2770_);
return v_res_2772_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_unsigned_to_nat(32u);
v___x_2774_ = lean_mk_empty_array_with_capacity(v___x_2773_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2776_ = ((size_t)5ULL);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_unsigned_to_nat(32u);
v___x_2779_ = lean_mk_empty_array_with_capacity(v___x_2778_);
v___x_2780_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0);
v___x_2781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v___x_2779_);
lean_ctor_set(v___x_2781_, 2, v___x_2777_);
lean_ctor_set(v___x_2781_, 3, v___x_2777_);
lean_ctor_set_usize(v___x_2781_, 4, v___x_2776_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object* v_t_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; lean_object* v_infoState_2787_; uint8_t v_enabled_2788_; 
v___x_2786_ = lean_st_ref_get(v___y_2784_);
v_infoState_2787_ = lean_ctor_get(v___x_2786_, 8);
lean_inc_ref(v_infoState_2787_);
lean_dec(v___x_2786_);
v_enabled_2788_ = lean_ctor_get_uint8(v_infoState_2787_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2787_);
if (v_enabled_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec_ref(v_t_2782_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1);
v___x_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_t_2782_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v___x_2792_, v___y_2784_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object* v_t_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v_t_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
if (lean_obj_tag(v_a_2799_) == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = l_List_reverse___redArg(v_a_2800_);
return v___x_2801_;
}
else
{
lean_object* v_head_2802_; lean_object* v_tail_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2812_; 
v_head_2802_ = lean_ctor_get(v_a_2799_, 0);
v_tail_2803_ = lean_ctor_get(v_a_2799_, 1);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_a_2799_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2805_ = v_a_2799_;
v_isShared_2806_ = v_isSharedCheck_2812_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_tail_2803_);
lean_inc(v_head_2802_);
lean_dec(v_a_2799_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2812_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = l_Lean_mkLevelParam(v_head_2802_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v_a_2800_);
lean_ctor_set(v___x_2805_, 0, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_a_2800_);
v___x_2809_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
v_a_2799_ = v_tail_2803_;
v_a_2800_ = v___x_2809_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object* v_constName_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v_env_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; 
v___x_2817_ = lean_st_ref_get(v___y_2815_);
v_env_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc_ref(v_env_2818_);
lean_dec(v___x_2817_);
v___x_2819_ = 0;
lean_inc(v_constName_2813_);
v___x_2820_ = l_Lean_Environment_findConstVal_x3f(v_env_2818_, v_constName_2813_, v___x_2819_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_2813_, v___y_2814_, v___y_2815_);
return v___x_2821_;
}
else
{
lean_object* v_val_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_constName_2813_);
v_val_2822_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2820_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_val_2822_);
lean_dec(v___x_2820_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set_tag(v___x_2824_, 0);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_val_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object* v_constName_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
lean_inc(v_constName_2835_);
v___x_2839_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2851_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2851_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2851_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_levelParams_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v_levelParams_2844_ = lean_ctor_get(v_a_2840_, 1);
lean_inc(v_levelParams_2844_);
lean_dec(v_a_2840_);
v___x_2845_ = lean_box(0);
v___x_2846_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(v_levelParams_2844_, v___x_2845_);
v___x_2847_ = l_Lean_mkConst(v_constName_2835_, v___x_2846_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2847_);
v___x_2849_ = v___x_2842_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_constName_2835_);
v_a_2852_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2839_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2839_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object* v_constName_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_constName_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object* v_stx_2865_, lean_object* v_n_2866_, lean_object* v_expectedType_x3f_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_n_2866_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
lean_ctor_set(v___x_2874_, 1, v_stx_2865_);
v___x_2875_ = l_Lean_LocalContext_empty;
v___x_2876_ = 0;
v___x_2877_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2877_, 0, v___x_2874_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
lean_ctor_set(v___x_2877_, 2, v_expectedType_x3f_2867_);
lean_ctor_set(v___x_2877_, 3, v_a_2872_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*4, v___x_2876_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*4 + 1, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
v___x_2879_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v___x_2878_, v___y_2868_, v___y_2869_);
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_expectedType_x3f_2867_);
lean_dec(v_stx_2865_);
v_a_2880_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2871_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2871_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object* v_stx_2888_, lean_object* v_n_2889_, lean_object* v_expectedType_x3f_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_stx_2888_, v_n_2889_, v_expectedType_x3f_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
return v_res_2894_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0));
v___x_2897_ = l_Lean_stringToMessageData(v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2));
v___x_2900_ = l_Lean_stringToMessageData(v___x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object* v_attrName_2901_, lean_object* v_extraKinds_2902_, uint8_t v_builtin_2903_, lean_object* v_stx_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2908_; lean_object* v_env_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_st_ref_get(v_a_2906_);
v_env_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2908_);
v___x_2910_ = l_Lean_Attribute_Builtin_getIdent(v_stx_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2988_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2988_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2988_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___y_2917_; lean_object* v___y_2918_; 
v___x_2915_ = l_Lean_Syntax_getId(v_a_2911_);
if (v_builtin_2903_ == 0)
{
goto v___jp_2965_;
}
else
{
uint8_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = 0;
lean_inc(v___x_2915_);
lean_inc_ref(v_env_2909_);
v___x_2987_ = l_Lean_Environment_find_x3f(v_env_2909_, v___x_2915_, v___x_2986_);
if (lean_obj_tag(v___x_2987_) == 0)
{
goto v___jp_2965_;
}
else
{
lean_dec_ref_known(v___x_2987_, 1);
lean_dec_ref(v_env_2909_);
lean_dec(v_attrName_2901_);
v___y_2917_ = v_a_2905_;
v___y_2918_ = v_a_2906_;
goto v___jp_2916_;
}
}
v___jp_2916_:
{
lean_object* v___x_2919_; lean_object* v_env_2920_; uint8_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2919_ = lean_st_ref_get(v___y_2918_);
v_env_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2920_);
lean_dec(v___x_2919_);
v___x_2921_ = 1;
lean_inc(v___x_2915_);
v___x_2922_ = l_Lean_Environment_contains(v_env_2920_, v___x_2915_, v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v_a_2911_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2924_ = v___x_2913_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2915_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
uint8_t v___x_2926_; lean_object* v___x_2927_; 
lean_del_object(v___x_2913_);
v___x_2926_ = 0;
lean_inc(v___x_2915_);
v___x_2927_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v___x_2915_, v___x_2926_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2955_; 
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2956_);
v___x_2929_ = v___x_2927_;
v_isShared_2930_ = v_isSharedCheck_2955_;
goto v_resetjp_2928_;
}
else
{
lean_dec(v___x_2927_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2955_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v_infoState_2932_; uint8_t v_enabled_2933_; 
v___x_2931_ = lean_st_ref_get(v___y_2918_);
v_infoState_2932_ = lean_ctor_get(v___x_2931_, 8);
lean_inc_ref(v_infoState_2932_);
lean_dec(v___x_2931_);
v_enabled_2933_ = lean_ctor_get_uint8(v_infoState_2932_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2932_);
if (v_enabled_2933_ == 0)
{
lean_object* v___x_2935_; 
lean_dec(v_a_2911_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2915_);
v___x_2935_ = v___x_2929_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2915_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_del_object(v___x_2929_);
v___x_2937_ = lean_box(0);
lean_inc(v___x_2915_);
v___x_2938_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_a_2911_, v___x_2915_, v___x_2937_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v___x_2938_, 0);
lean_dec(v_unused_2946_);
v___x_2940_ = v___x_2938_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v___x_2938_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2915_);
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2915_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v___x_2915_);
v_a_2947_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2938_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2938_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v___x_2915_);
lean_dec(v_a_2911_);
v_a_2957_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2927_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2927_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
v___jp_2965_:
{
uint8_t v___x_2966_; 
lean_inc(v___x_2915_);
v___x_2966_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2909_, v___x_2915_);
if (v___x_2966_ == 0)
{
uint8_t v___x_2967_; 
v___x_2967_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v___x_2915_, v_extraKinds_2902_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_del_object(v___x_2913_);
lean_dec(v_a_2911_);
v___x_2968_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1);
v___x_2969_ = l_Lean_MessageData_ofName(v_attrName_2901_);
v___x_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_MessageData_ofName(v___x_2915_);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_2976_, v_a_2905_, v_a_2906_);
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
else
{
lean_dec(v_attrName_2901_);
v___y_2917_ = v_a_2905_;
v___y_2918_ = v_a_2906_;
goto v___jp_2916_;
}
}
else
{
lean_dec(v_attrName_2901_);
v___y_2917_ = v_a_2905_;
v___y_2918_ = v_a_2906_;
goto v___jp_2916_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_env_2909_);
lean_dec(v_attrName_2901_);
v_a_2989_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2910_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2910_);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object* v_attrName_2997_, lean_object* v_extraKinds_2998_, lean_object* v_builtin_2999_, lean_object* v_stx_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
uint8_t v_builtin_boxed_3004_; lean_object* v_res_3005_; 
v_builtin_boxed_3004_ = lean_unbox(v_builtin_2999_);
v_res_3005_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(v_attrName_2997_, v_extraKinds_2998_, v_builtin_boxed_3004_, v_stx_3000_, v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_extraKinds_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object* v_00_u03b2_3006_, lean_object* v_m_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_3007_, v_a_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3010_, lean_object* v_m_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(v_00_u03b2_3010_, v_m_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_m_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object* v_t_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_3014_, v___y_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object* v_t_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(v_t_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
uint8_t v___x_3027_; 
v___x_3027_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_3025_, v_x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(v_00_u03b2_3028_, v_x_3029_, v_x_3030_);
lean_dec_ref(v_x_3030_);
lean_dec_ref(v_x_3029_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3033_, lean_object* v_a_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_3034_, v_x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3037_, lean_object* v_a_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(v_00_u03b2_3037_, v_a_3038_, v_x_3039_);
lean_dec(v_x_3039_);
lean_dec(v_a_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3041_, lean_object* v_x_3042_, size_t v_x_3043_, lean_object* v_x_3044_){
_start:
{
uint8_t v___x_3045_; 
v___x_3045_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3042_, v_x_3043_, v_x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3046_, lean_object* v_x_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
size_t v_x_6265__boxed_3050_; uint8_t v_res_3051_; lean_object* v_r_3052_; 
v_x_6265__boxed_3050_ = lean_unbox_usize(v_x_3048_);
lean_dec(v_x_3048_);
v_res_3051_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3046_, v_x_3047_, v_x_6265__boxed_3050_, v_x_3049_);
lean_dec_ref(v_x_3049_);
lean_dec_ref(v_x_3047_);
v_r_3052_ = lean_box(v_res_3051_);
return v_r_3052_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_3053_, lean_object* v_keys_3054_, lean_object* v_vals_3055_, lean_object* v_heq_3056_, lean_object* v_i_3057_, lean_object* v_k_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_3054_, v_i_3057_, v_k_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3060_, lean_object* v_keys_3061_, lean_object* v_vals_3062_, lean_object* v_heq_3063_, lean_object* v_i_3064_, lean_object* v_k_3065_){
_start:
{
uint8_t v_res_3066_; lean_object* v_r_3067_; 
v_res_3066_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_3060_, v_keys_3061_, v_vals_3062_, v_heq_3063_, v_i_3064_, v_k_3065_);
lean_dec_ref(v_k_3065_);
lean_dec_ref(v_vals_3062_);
lean_dec_ref(v_keys_3061_);
v_r_3067_ = lean_box(v_res_3066_);
return v_r_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(uint8_t v_builtin_3068_, lean_object* v_declName_3069_, lean_object* v_key_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_builtin_3076_, lean_object* v_declName_3077_, lean_object* v_key_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v_builtin_boxed_3082_; lean_object* v_res_3083_; 
v_builtin_boxed_3082_ = lean_unbox(v_builtin_3076_);
v_res_3083_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(v_builtin_boxed_3082_, v_declName_3077_, v_key_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v_key_3078_);
lean_dec(v_declName_3077_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = l_Lean_Fmt_headerKind;
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3099_ = l_Lean_Fmt_cmdsKind;
v___x_3100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3102_ = l_Lean_Fmt_moduleKind;
v___x_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3101_);
return v___x_3103_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3105_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3106_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed), 7, 2);
lean_closure_set(v___x_3106_, 0, v___x_3105_);
lean_closure_set(v___x_3106_, 1, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___f_3107_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3108_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3109_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3110_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3111_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3112_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3111_);
lean_ctor_set(v___x_3113_, 2, v___x_3110_);
lean_ctor_set(v___x_3113_, 3, v___x_3109_);
lean_ctor_set(v___x_3113_, 4, v___x_3108_);
lean_ctor_set(v___x_3113_, 5, v___f_3107_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_);
v___x_3121_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_));
v___x_3122_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3120_, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2____boxed(lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3053846778____hygCtx___hyg_2_();
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object* v_constName_3130_, lean_object* v_env_3131_, lean_object* v_opts_3132_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
v___x_3134_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3131_, v_opts_3132_, v___x_3133_, v_constName_3130_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object* v_constName_3135_, lean_object* v_env_3136_, lean_object* v_opts_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(v_constName_3135_, v_env_3136_, v_opts_3137_);
lean_dec_ref(v_opts_3137_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object* v_constName_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_env_3142_; lean_object* v_opts_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v_env_3142_ = lean_ctor_get(v_a_3140_, 0);
v_opts_3143_ = lean_ctor_get(v_a_3140_, 1);
v___x_3144_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
lean_inc_ref(v_env_3142_);
v___x_3145_ = l_Lean_Environment_evalConstCheck___redArg(v_env_3142_, v_opts_3143_, v___x_3144_, v_constName_3139_);
v___x_3146_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object* v_constName_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_constName_3147_, v_a_3148_);
lean_dec_ref(v_a_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_));
v___x_3155_ = lean_st_mk_ref(v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object* v_f_3159_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3161_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3162_ = lean_st_ref_take(v___x_3161_);
v___x_3163_ = lean_array_push(v___x_3162_, v_f_3159_);
v___x_3164_ = lean_st_ref_put(v___x_3161_, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object* v_f_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_Fmt_addBuiltinStickyTermFn(v_f_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3169_){
_start:
{
lean_object* v_fst_3170_; 
v_fst_3170_ = lean_ctor_get(v_x_3169_, 0);
lean_inc(v_fst_3170_);
return v_fst_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3171_);
lean_dec_ref(v_x_3171_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3173_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_box(0);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3175_);
lean_dec_ref(v_x_3175_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3177_, lean_object* v_s_3178_){
_start:
{
lean_object* v_fst_3179_; lean_object* v___x_3180_; 
v_fst_3179_ = lean_ctor_get(v_s_3178_, 0);
lean_inc_n(v_fst_3179_, 3);
v___x_3180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3180_, 0, v_fst_3179_);
lean_ctor_set(v___x_3180_, 1, v_fst_3179_);
lean_ctor_set(v___x_3180_, 2, v_fst_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_x_3181_, lean_object* v_s_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v_x_3181_, v_s_3182_);
lean_dec_ref(v_s_3182_);
lean_dec_ref(v_x_3181_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v_x_3184_, lean_object* v_x_3185_){
_start:
{
lean_object* v_fst_3186_; lean_object* v_snd_3187_; lean_object* v_fst_3188_; lean_object* v_snd_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3198_; 
v_fst_3186_ = lean_ctor_get(v_x_3184_, 0);
lean_inc(v_fst_3186_);
v_snd_3187_ = lean_ctor_get(v_x_3184_, 1);
lean_inc(v_snd_3187_);
lean_dec_ref(v_x_3184_);
v_fst_3188_ = lean_ctor_get(v_x_3185_, 0);
v_snd_3189_ = lean_ctor_get(v_x_3185_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_x_3185_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3191_ = v_x_3185_;
v_isShared_3192_ = v_isSharedCheck_3198_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_snd_3189_);
lean_inc(v_fst_3188_);
lean_dec(v_x_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3198_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3193_ = lean_array_push(v_fst_3186_, v_fst_3188_);
v___x_3194_ = lean_array_push(v_snd_3187_, v_snd_3189_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3194_);
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3199_, lean_object* v___x_3200_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3202_ = lean_st_ref_get(v___x_3199_);
v___x_3203_ = lean_mk_empty_array_with_capacity(v___x_3200_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3206_, lean_object* v___x_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3206_, v___x_3207_);
lean_dec(v___x_3207_);
lean_dec(v___x_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(lean_object* v_as_3210_, size_t v_i_3211_, size_t v_stop_3212_, lean_object* v_b_3213_, lean_object* v___y_3214_){
_start:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_usize_dec_eq(v_i_3211_, v_stop_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_array_uget_borrowed(v_as_3210_, v_i_3211_);
lean_inc(v___x_3217_);
v___x_3218_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v___x_3217_, v___y_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = lean_array_push(v_b_3213_, v_a_3219_);
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3211_, v___x_3221_);
v_i_3211_ = v___x_3222_;
v_b_3213_ = v___x_3220_;
goto _start;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v_b_3213_);
v_a_3224_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3218_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3218_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v_b_3213_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_3233_, lean_object* v_i_3234_, lean_object* v_stop_3235_, lean_object* v_b_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
size_t v_i_boxed_3239_; size_t v_stop_boxed_3240_; lean_object* v_res_3241_; 
v_i_boxed_3239_ = lean_unbox_usize(v_i_3234_);
lean_dec(v_i_3234_);
v_stop_boxed_3240_ = lean_unbox_usize(v_stop_3235_);
lean_dec(v_stop_3235_);
v_res_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v_as_3233_, v_i_boxed_3239_, v_stop_boxed_3240_, v_b_3236_, v___y_3237_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v_as_3233_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(lean_object* v_as_3242_, size_t v_i_3243_, size_t v_stop_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_a_3249_; uint8_t v___x_3253_; 
v___x_3253_ = lean_usize_dec_eq(v_i_3243_, v_stop_3244_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = lean_array_uget_borrowed(v_as_3242_, v_i_3243_);
v___x_3256_ = lean_array_get_size(v___x_3255_);
v___x_3257_ = lean_nat_dec_lt(v___x_3254_, v___x_3256_);
if (v___x_3257_ == 0)
{
v_a_3249_ = v_b_3245_;
goto v___jp_3248_;
}
else
{
size_t v___x_3258_; size_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = ((size_t)0ULL);
v___x_3259_ = lean_usize_of_nat(v___x_3256_);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__0(v___x_3255_, v___x_3258_, v___x_3259_, v_b_3245_, v___y_3246_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v_a_3249_ = v_a_3261_;
goto v___jp_3248_;
}
else
{
return v___x_3260_;
}
}
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_b_3245_);
return v___x_3262_;
}
v___jp_3248_:
{
size_t v___x_3250_; size_t v___x_3251_; 
v___x_3250_ = ((size_t)1ULL);
v___x_3251_ = lean_usize_add(v_i_3243_, v___x_3250_);
v_i_3243_ = v___x_3251_;
v_b_3245_ = v_a_3249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_3263_, lean_object* v_i_3264_, lean_object* v_stop_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
size_t v_i_boxed_3269_; size_t v_stop_boxed_3270_; lean_object* v_res_3271_; 
v_i_boxed_3269_ = lean_unbox_usize(v_i_3264_);
lean_dec(v_i_3264_);
v_stop_boxed_3270_ = lean_unbox_usize(v_stop_3265_);
lean_dec(v_stop_3265_);
v_res_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3263_, v_i_boxed_3269_, v_stop_boxed_3270_, v_b_3266_, v___y_3267_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_as_3263_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v_as_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_a_3278_; lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3282_ = lean_st_ref_get(v___x_3273_);
v___x_3283_ = lean_array_get_size(v_as_3274_);
v___x_3284_ = lean_nat_dec_lt(v___x_3272_, v___x_3283_);
if (v___x_3284_ == 0)
{
v_a_3278_ = v___x_3282_;
goto v___jp_3277_;
}
else
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((size_t)0ULL);
v___x_3286_ = lean_usize_of_nat(v___x_3283_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__spec__1(v_as_3274_, v___x_3285_, v___x_3286_, v___x_3282_, v___y_3275_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v_a_3278_ = v_a_3288_;
goto v___jp_3277_;
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3287_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3287_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
v___jp_3277_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_mk_empty_array_with_capacity(v___x_3272_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v_a_3278_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v___x_3297_, lean_object* v___x_3298_, lean_object* v_as_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(v___x_3297_, v___x_3298_, v_as_3299_, v___y_3300_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v_as_3299_);
lean_dec(v___x_3298_);
lean_dec(v___x_3297_);
return v_res_3302_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___f_3313_; 
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_3313_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_3313_, 0, v___x_3312_);
lean_closure_set(v___f_3313_, 1, v___x_3311_);
return v___f_3313_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___f_3316_; 
v___x_3314_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_3315_ = lean_unsigned_to_nat(0u);
v___f_3316_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_3316_, 0, v___x_3315_);
lean_closure_set(v___f_3316_, 1, v___x_3314_);
return v___f_3316_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___f_3320_; lean_object* v___f_3321_; lean_object* v___f_3322_; lean_object* v___f_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3317_ = 0;
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_box(2);
v___f_3320_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3321_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3322_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___f_3323_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___f_3324_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3326_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___f_3324_);
lean_ctor_set(v___x_3326_, 2, v___f_3323_);
lean_ctor_set(v___x_3326_, 3, v___f_3322_);
lean_ctor_set(v___x_3326_, 4, v___f_3321_);
lean_ctor_set(v___x_3326_, 5, v___f_3320_);
lean_ctor_set(v___x_3326_, 6, v___x_3319_);
lean_ctor_set(v___x_3326_, 7, v___x_3318_);
lean_ctor_set_uint8(v___x_3326_, sizeof(void*)*8, v___x_3317_);
lean_ctor_set_uint8(v___x_3326_, sizeof(void*)*8 + 1, v___x_3317_);
return v___x_3326_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___f_3327_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_));
v___x_3328_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v___f_3327_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_);
v___x_3332_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2____boxed(lean_object* v_a_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_177588460____hygCtx___hyg_2_();
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_name_3335_, lean_object* v_decl_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3340_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3341_ = l_Lean_MessageData_ofName(v_name_3335_);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2_);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__0___redArg(v___x_3344_, v___y_3337_, v___y_3338_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_name_3346_, lean_object* v_decl_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_name_3346_, v_decl_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v_decl_3347_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(lean_object* v_addEntryFn_3352_, lean_object* v___x_3353_, lean_object* v_s_3354_){
_start:
{
lean_object* v_importedEntries_3355_; lean_object* v_state_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3364_; 
v_importedEntries_3355_ = lean_ctor_get(v_s_3354_, 0);
v_state_3356_ = lean_ctor_get(v_s_3354_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_s_3354_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3358_ = v_s_3354_;
v_isShared_3359_ = v_isSharedCheck_3364_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_state_3356_);
lean_inc(v_importedEntries_3355_);
lean_dec(v_s_3354_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3364_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v_state_3360_; lean_object* v___x_3362_; 
v_state_3360_ = lean_apply_2(v_addEntryFn_3352_, v_state_3356_, v___x_3353_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_state_3360_);
v___x_3362_ = v___x_3358_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_importedEntries_3355_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_state_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3366_, lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_name_3370_, lean_object* v_decl_3371_, lean_object* v_stx_3372_, uint8_t v_kind_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3372_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_dec_ref_known(v___x_3445_, 1);
if (v_builtin_3366_ == 0)
{
lean_object* v___x_3446_; 
lean_inc(v_decl_3371_);
lean_inc(v_name_3370_);
v___x_3446_ = l_Lean_ensureAttrDeclIsMeta(v_name_3370_, v_decl_3371_, v_kind_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_dec_ref_known(v___x_3446_, 1);
goto v___jp_3441_;
}
else
{
lean_dec(v_decl_3371_);
lean_dec(v_name_3370_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v___x_3367_);
return v___x_3446_;
}
}
else
{
goto v___jp_3441_;
}
}
else
{
lean_dec(v_decl_3371_);
lean_dec(v_name_3370_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v___x_3367_);
return v___x_3445_;
}
v___jp_3377_:
{
if (v_builtin_3366_ == 0)
{
lean_object* v___x_3380_; lean_object* v_env_3381_; lean_object* v___x_3382_; lean_object* v_env_3383_; lean_object* v_ref_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
v___x_3380_ = lean_st_ref_get(v___y_3379_);
v_env_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_ref(v_env_3381_);
lean_dec(v___x_3380_);
v___x_3382_ = lean_st_ref_get(v___y_3379_);
v_env_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_env_3383_);
lean_dec(v___x_3382_);
v_ref_3384_ = lean_ctor_get(v___y_3378_, 2);
v___x_3385_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3378_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_env_3383_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_inc(v_decl_3371_);
v___x_3387_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_decl_3371_, v___x_3386_);
lean_dec_ref_known(v___x_3386_, 2);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; lean_object* v_toEnvExtension_3390_; lean_object* v_addEntryFn_3391_; lean_object* v_asyncMode_3392_; uint8_t v_logWrites_3393_; lean_object* v___x_3394_; lean_object* v___f_3395_; uint8_t v___x_3396_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3390_ = lean_ctor_get(v___x_3389_, 0);
v_addEntryFn_3391_ = lean_ctor_get(v___x_3389_, 3);
v_asyncMode_3392_ = lean_ctor_get(v_toEnvExtension_3390_, 2);
v_logWrites_3393_ = lean_ctor_get_uint8(v_toEnvExtension_3390_, sizeof(void*)*6);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_decl_3371_);
lean_ctor_set(v___x_3394_, 1, v_a_3388_);
lean_inc(v_addEntryFn_3391_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_3395_, 0, v_addEntryFn_3391_);
lean_closure_set(v___f_3395_, 1, v___x_3394_);
v___x_3396_ = 1;
if (v_logWrites_3393_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_inc_ref(v_toEnvExtension_3390_);
v___x_3397_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3390_, v_env_3381_, v___f_3395_, v_asyncMode_3392_, v___x_3367_, v___x_3396_);
v___x_3398_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3397_, v___y_3379_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_inc_ref_n(v_toEnvExtension_3390_, 2);
v___x_3399_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3390_, v_env_3381_);
lean_dec_ref(v_env_3381_);
v___x_3400_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3390_, v___x_3399_, v___f_3395_, v_asyncMode_3392_, v___x_3367_, v___x_3396_);
v___x_3401_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__1___redArg(v___x_3400_, v___y_3379_);
return v___x_3401_;
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v_env_3381_);
lean_dec(v_decl_3371_);
lean_dec(v___x_3367_);
v_a_3402_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3404_ = v___x_3387_;
v_isShared_3405_ = v_isSharedCheck_3413_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3387_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3413_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3406_ = lean_io_error_to_string(v_a_3402_);
v___x_3407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
v___x_3408_ = l_Lean_MessageData_ofFormat(v___x_3407_);
lean_inc(v_ref_3384_);
v___x_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_ref_3384_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3409_);
v___x_3411_ = v___x_3404_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_dec(v___x_3367_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3415_ = l_Lean_Name_mkStr3(v___x_3368_, v___x_3369_, v___x_3414_);
v___x_3416_ = lean_box(0);
v___x_3417_ = l_Lean_mkConst(v___x_3415_, v___x_3416_);
lean_inc(v_decl_3371_);
v___x_3418_ = l_Lean_mkConst(v_decl_3371_, v___x_3416_);
v___x_3419_ = l_Lean_Expr_app___override(v___x_3417_, v___x_3418_);
v___x_3420_ = l_Lean_declareBuiltin(v_decl_3371_, v___x_3419_, v___y_3378_, v___y_3379_);
return v___x_3420_;
}
}
v___jp_3421_:
{
lean_object* v___x_3424_; 
lean_inc(v_decl_3371_);
v___x_3424_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__2(v_decl_3371_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = l_Lean_ConstantInfo_type(v_a_3425_);
lean_dec(v_a_3425_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0));
lean_inc_ref(v___x_3369_);
lean_inc_ref(v___x_3368_);
v___x_3428_ = l_Lean_Name_mkStr3(v___x_3368_, v___x_3369_, v___x_3427_);
v___x_3429_ = l_Lean_Expr_isConstOf(v___x_3426_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v___x_3367_);
v___x_3430_ = lean_box(0);
v___x_3431_ = l_Lean_mkConst(v___x_3428_, v___x_3430_);
v___x_3432_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__3___redArg(v_name_3370_, v_decl_3371_, v___x_3426_, v___x_3431_, v___y_3422_, v___y_3423_);
return v___x_3432_;
}
else
{
lean_dec(v___x_3428_);
lean_dec_ref(v___x_3426_);
lean_dec(v_name_3370_);
v___y_3378_ = v___y_3422_;
v___y_3379_ = v___y_3423_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v_decl_3371_);
lean_dec(v_name_3370_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v___x_3367_);
v_a_3433_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3424_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3424_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_3441_:
{
uint8_t v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = 0;
v___x_3443_ = l_Lean_instBEqAttributeKind_beq(v_kind_3373_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec(v_decl_3371_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v___x_3367_);
v___x_3444_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_960770660____hygCtx___hyg_2__spec__4___redArg(v_name_3370_, v_kind_3373_, v___y_3374_, v___y_3375_);
return v___x_3444_;
}
else
{
v___y_3422_ = v___y_3374_;
v___y_3423_ = v___y_3375_;
goto v___jp_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3447_, lean_object* v___x_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v_name_3451_, lean_object* v_decl_3452_, lean_object* v_stx_3453_, lean_object* v_kind_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v_builtin_boxed_3458_; uint8_t v_kind_boxed_3459_; lean_object* v_res_3460_; 
v_builtin_boxed_3458_ = lean_unbox(v_builtin_3447_);
v_kind_boxed_3459_ = lean_unbox(v_kind_3454_);
v_res_3460_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3458_, v___x_3448_, v___x_3449_, v___x_3450_, v_name_3451_, v_decl_3452_, v_stx_3453_, v_kind_boxed_3459_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(uint8_t v_builtin_3475_, lean_object* v_name_3476_){
_start:
{
lean_object* v___f_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___y_3486_; 
lean_inc_n(v_name_3476_, 2);
v___f_3478_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_3478_, 0, v_name_3476_);
v___x_3479_ = lean_box(0);
v___x_3480_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0));
v___x_3481_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1));
v___x_3482_ = lean_box(v_builtin_3475_);
v___f_3483_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_3483_, 0, v___x_3482_);
lean_closure_set(v___f_3483_, 1, v___x_3479_);
lean_closure_set(v___f_3483_, 2, v___x_3480_);
lean_closure_set(v___f_3483_, 3, v___x_3481_);
lean_closure_set(v___f_3483_, 4, v_name_3476_);
v___x_3484_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
if (v_builtin_3475_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___y_3486_ = v___x_3493_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3494_; 
v___x_3494_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___y_3486_ = v___x_3494_;
goto v___jp_3485_;
}
v___jp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3487_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
lean_inc_ref(v___y_3486_);
v___x_3488_ = lean_string_append(v___y_3486_, v___x_3487_);
v___x_3489_ = 1;
v___x_3490_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3490_, 0, v___x_3484_);
lean_ctor_set(v___x_3490_, 1, v_name_3476_);
lean_ctor_set(v___x_3490_, 2, v___x_3488_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*3, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___f_3483_);
lean_ctor_set(v___x_3491_, 2, v___f_3478_);
v___x_3492_ = l_Lean_registerBuiltinAttribute(v___x_3491_);
return v___x_3492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_builtin_3495_, lean_object* v_name_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v_builtin_boxed_3498_; lean_object* v_res_3499_; 
v_builtin_boxed_3498_ = lean_unbox(v_builtin_3495_);
v_res_3499_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v_builtin_boxed_3498_, v_name_3496_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = 1;
v___x_3508_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3509_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3507_, v___x_3508_);
if (lean_obj_tag(v___x_3509_) == 0)
{
uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref_known(v___x_3509_, 1);
v___x_3510_ = 0;
v___x_3511_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_));
v___x_3512_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_(v___x_3510_, v___x_3511_);
return v___x_3512_;
}
else
{
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2____boxed(lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1916596973____hygCtx___hyg_2_();
return v_res_3514_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object* v_t_3515_, lean_object* v_as_3516_, size_t v_i_3517_, size_t v_stop_3518_){
_start:
{
uint8_t v___x_3519_; 
v___x_3519_ = lean_usize_dec_eq(v_i_3517_, v_stop_3518_);
if (v___x_3519_ == 0)
{
lean_object* v___x_158__overap_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_158__overap_3520_ = lean_array_uget_borrowed(v_as_3516_, v_i_3517_);
lean_inc(v___x_158__overap_3520_);
lean_inc(v_t_3515_);
v___x_3521_ = lean_apply_1(v___x_158__overap_3520_, v_t_3515_);
v___x_3522_ = lean_unbox(v___x_3521_);
if (v___x_3522_ == 0)
{
size_t v___x_3523_; size_t v___x_3524_; 
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3517_, v___x_3523_);
v_i_3517_ = v___x_3524_;
goto _start;
}
else
{
uint8_t v___x_3526_; 
lean_dec(v_t_3515_);
v___x_3526_ = lean_unbox(v___x_3521_);
return v___x_3526_;
}
}
else
{
uint8_t v___x_3527_; 
lean_dec(v_t_3515_);
v___x_3527_ = 0;
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object* v_t_3528_, lean_object* v_as_3529_, lean_object* v_i_3530_, lean_object* v_stop_3531_){
_start:
{
size_t v_i_boxed_3532_; size_t v_stop_boxed_3533_; uint8_t v_res_3534_; lean_object* v_r_3535_; 
v_i_boxed_3532_ = lean_unbox_usize(v_i_3530_);
lean_dec(v_i_3530_);
v_stop_boxed_3533_ = lean_unbox_usize(v_stop_3531_);
lean_dec(v_stop_3531_);
v_res_3534_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3528_, v_as_3529_, v_i_boxed_3532_, v_stop_boxed_3533_);
lean_dec_ref(v_as_3529_);
v_r_3535_ = lean_box(v_res_3534_);
return v_r_3535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object* v_env_3536_, lean_object* v_t_3537_){
_start:
{
lean_object* v___x_3538_; lean_object* v_toEnvExtension_3539_; lean_object* v_asyncMode_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v_snd_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3538_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_3539_ = lean_ctor_get(v___x_3538_, 0);
v_asyncMode_3540_ = lean_ctor_get(v_toEnvExtension_3539_, 2);
v___x_3541_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_3542_ = lean_box(0);
v___x_3543_ = 0;
v___x_3544_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3541_, v___x_3538_, v_env_3536_, v_asyncMode_3540_, v___x_3542_, v___x_3543_);
v_snd_3545_ = lean_ctor_get(v___x_3544_, 1);
lean_inc(v_snd_3545_);
lean_dec(v___x_3544_);
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = lean_array_get_size(v_snd_3545_);
v___x_3548_ = lean_nat_dec_lt(v___x_3546_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_dec(v_snd_3545_);
lean_dec(v_t_3537_);
return v___x_3548_;
}
else
{
if (v___x_3548_ == 0)
{
lean_dec(v_snd_3545_);
lean_dec(v_t_3537_);
return v___x_3548_;
}
else
{
size_t v___x_3549_; size_t v___x_3550_; uint8_t v___x_3551_; 
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = lean_usize_of_nat(v___x_3547_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_3537_, v_snd_3545_, v___x_3549_, v___x_3550_);
lean_dec(v_snd_3545_);
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object* v_env_3552_, lean_object* v_t_3553_){
_start:
{
uint8_t v_res_3554_; lean_object* v_r_3555_; 
v_res_3554_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_3552_, v_t_3553_);
v_r_3555_ = lean_box(v_res_3554_);
return v_r_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(uint8_t v_x_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_box(v_x_3556_);
v___x_3558_ = lean_obj_tag_nat(v___x_3557_);
lean_dec(v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl___boxed(lean_object* v_x_3559_){
_start:
{
uint8_t v_x_4__boxed_3560_; lean_object* v_res_3561_; 
v_x_4__boxed_3560_ = lean_unbox(v_x_3559_);
v_res_3561_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___impl(v_x_4__boxed_3560_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object* v_k_3562_){
_start:
{
lean_inc(v_k_3562_);
return v_k_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object* v_k_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(v_k_3563_);
lean_dec(v_k_3563_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object* v_motive_3565_, lean_object* v_ctorIdx_3566_, uint8_t v_t_3567_, lean_object* v_h_3568_, lean_object* v_k_3569_){
_start:
{
lean_inc(v_k_3569_);
return v_k_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object* v_motive_3570_, lean_object* v_ctorIdx_3571_, lean_object* v_t_3572_, lean_object* v_h_3573_, lean_object* v_k_3574_){
_start:
{
uint8_t v_t_boxed_3575_; lean_object* v_res_3576_; 
v_t_boxed_3575_ = lean_unbox(v_t_3572_);
v_res_3576_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim(v_motive_3570_, v_ctorIdx_3571_, v_t_boxed_3575_, v_h_3573_, v_k_3574_);
lean_dec(v_k_3574_);
lean_dec(v_ctorIdx_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object* v_left_3577_){
_start:
{
lean_inc(v_left_3577_);
return v_left_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object* v_left_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(v_left_3578_);
lean_dec(v_left_3578_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object* v_motive_3580_, uint8_t v_t_3581_, lean_object* v_h_3582_, lean_object* v_left_3583_){
_start:
{
lean_inc(v_left_3583_);
return v_left_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object* v_motive_3584_, lean_object* v_t_3585_, lean_object* v_h_3586_, lean_object* v_left_3587_){
_start:
{
uint8_t v_t_boxed_3588_; lean_object* v_res_3589_; 
v_t_boxed_3588_ = lean_unbox(v_t_3585_);
v_res_3589_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim(v_motive_3584_, v_t_boxed_3588_, v_h_3586_, v_left_3587_);
lean_dec(v_left_3587_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object* v_right_3590_){
_start:
{
lean_inc(v_right_3590_);
return v_right_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object* v_right_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(v_right_3591_);
lean_dec(v_right_3591_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object* v_motive_3593_, uint8_t v_t_3594_, lean_object* v_h_3595_, lean_object* v_right_3596_){
_start:
{
lean_inc(v_right_3596_);
return v_right_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object* v_motive_3597_, lean_object* v_t_3598_, lean_object* v_h_3599_, lean_object* v_right_3600_){
_start:
{
uint8_t v_t_boxed_3601_; lean_object* v_res_3602_; 
v_t_boxed_3601_ = lean_unbox(v_t_3598_);
v_res_3602_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim(v_motive_3597_, v_t_boxed_3601_, v_h_3599_, v_right_3600_);
lean_dec(v_right_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object* v_middle_3603_){
_start:
{
lean_inc(v_middle_3603_);
return v_middle_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object* v_middle_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(v_middle_3604_);
lean_dec(v_middle_3604_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object* v_motive_3606_, uint8_t v_t_3607_, lean_object* v_h_3608_, lean_object* v_middle_3609_){
_start:
{
lean_inc(v_middle_3609_);
return v_middle_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object* v_motive_3610_, lean_object* v_t_3611_, lean_object* v_h_3612_, lean_object* v_middle_3613_){
_start:
{
uint8_t v_t_boxed_3614_; lean_object* v_res_3615_; 
v_t_boxed_3614_ = lean_unbox(v_t_3611_);
v_res_3615_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim(v_motive_3610_, v_t_boxed_3614_, v_h_3612_, v_middle_3613_);
lean_dec(v_middle_3613_);
return v_res_3615_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default(void){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = 0;
return v___x_3616_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity(void){
_start:
{
uint8_t v___x_3617_; 
v___x_3617_ = 0;
return v___x_3617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t v_x_3618_, uint8_t v_y_3619_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3620_ = lean_box(v_x_3618_);
v___x_3621_ = lean_obj_tag_nat(v___x_3620_);
lean_dec(v___x_3620_);
v___x_3622_ = lean_box(v_y_3619_);
v___x_3623_ = lean_obj_tag_nat(v___x_3622_);
lean_dec(v___x_3622_);
v___x_3624_ = lean_nat_dec_eq(v___x_3621_, v___x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object* v_x_3625_, lean_object* v_y_3626_){
_start:
{
uint8_t v_x_24__boxed_3627_; uint8_t v_y_25__boxed_3628_; uint8_t v_res_3629_; lean_object* v_r_3630_; 
v_x_24__boxed_3627_ = lean_unbox(v_x_3625_);
v_y_25__boxed_3628_ = lean_unbox(v_y_3626_);
v_res_3629_ = l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(v_x_24__boxed_3627_, v_y_25__boxed_3628_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
lean_object* v_prec_3639_; lean_object* v_lhsPrec_3640_; lean_object* v_rhsPrec_3641_; lean_object* v_prec_3642_; lean_object* v_lhsPrec_3643_; lean_object* v_rhsPrec_3644_; uint8_t v___x_3645_; 
v_prec_3639_ = lean_ctor_get(v_x_3637_, 0);
v_lhsPrec_3640_ = lean_ctor_get(v_x_3637_, 1);
v_rhsPrec_3641_ = lean_ctor_get(v_x_3637_, 2);
v_prec_3642_ = lean_ctor_get(v_x_3638_, 0);
v_lhsPrec_3643_ = lean_ctor_get(v_x_3638_, 1);
v_rhsPrec_3644_ = lean_ctor_get(v_x_3638_, 2);
v___x_3645_ = lean_nat_dec_eq(v_prec_3639_, v_prec_3642_);
if (v___x_3645_ == 0)
{
return v___x_3645_;
}
else
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_nat_dec_eq(v_lhsPrec_3640_, v_lhsPrec_3643_);
if (v___x_3646_ == 0)
{
return v___x_3646_;
}
else
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_nat_dec_eq(v_rhsPrec_3641_, v_rhsPrec_3644_);
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
uint8_t v_res_3650_; lean_object* v_r_3651_; 
v_res_3650_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_x_3648_, v_x_3649_);
lean_dec_ref(v_x_3649_);
lean_dec_ref(v_x_3648_);
v_r_3651_ = lean_box(v_res_3650_);
return v_r_3651_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_unsigned_to_nat(16u);
v___x_3656_ = lean_mk_array(v___x_3655_, v___x_3654_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0);
v___x_3658_ = lean_unsigned_to_nat(0u);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v___x_3657_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; 
v___x_3660_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1);
v___x_3661_ = lean_box(0);
v___x_3662_ = 0;
v___x_3663_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3660_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*2, v___x_3662_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*2 + 1, v___x_3662_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default(void){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2);
return v___x_3664_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation(void){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Fmt_instInhabitedInfixOperation_default;
return v___x_3665_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object* v_x_3666_, lean_object* v_x_3667_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
if (lean_obj_tag(v_x_3667_) == 0)
{
uint8_t v___x_3668_; 
v___x_3668_ = 1;
return v___x_3668_;
}
else
{
uint8_t v___x_3669_; 
v___x_3669_ = 0;
return v___x_3669_;
}
}
else
{
if (lean_obj_tag(v_x_3667_) == 0)
{
uint8_t v___x_3670_; 
v___x_3670_ = 0;
return v___x_3670_;
}
else
{
lean_object* v_val_3671_; lean_object* v_val_3672_; uint8_t v___x_3673_; 
v_val_3671_ = lean_ctor_get(v_x_3666_, 0);
v_val_3672_ = lean_ctor_get(v_x_3667_, 0);
v___x_3673_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_3671_, v_val_3672_);
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object* v_x_3674_, lean_object* v_x_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_x_3674_, v_x_3675_);
lean_dec(v_x_3675_);
lean_dec(v_x_3674_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
if (lean_obj_tag(v_x_3679_) == 0)
{
uint8_t v___x_3680_; 
v___x_3680_ = 1;
return v___x_3680_;
}
else
{
uint8_t v___x_3681_; 
v___x_3681_ = 0;
return v___x_3681_;
}
}
else
{
if (lean_obj_tag(v_x_3679_) == 0)
{
uint8_t v___x_3682_; 
v___x_3682_ = 0;
return v___x_3682_;
}
else
{
uint8_t v___x_3683_; 
v___x_3683_ = 1;
return v___x_3683_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v_x_3684_, v_x_3685_);
lean_dec(v_x_3685_);
lean_dec(v_x_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_m_u2082_3691_, lean_object* v___x_3692_, lean_object* v___x_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___y_3699_; uint8_t v___x_3712_; 
v___x_3696_ = lean_box(0);
v___x_3697_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v___x_3712_ = lean_nat_dec_eq(v___x_3692_, v___x_3693_);
if (v___x_3712_ == 0)
{
uint8_t v___x_3713_; 
v___x_3713_ = 1;
v___y_3699_ = v___x_3713_;
goto v___jp_3698_;
}
else
{
uint8_t v___x_3714_; 
v___x_3714_ = 0;
v___y_3699_ = v___x_3714_;
goto v___jp_3698_;
}
v___jp_3698_:
{
if (lean_obj_tag(v_a_3694_) == 0)
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_a_3695_);
return v___x_3700_;
}
else
{
lean_object* v_key_3701_; lean_object* v_value_3702_; lean_object* v_tail_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
lean_dec_ref(v_a_3695_);
v_key_3701_ = lean_ctor_get(v_a_3694_, 0);
v_value_3702_ = lean_ctor_get(v_a_3694_, 1);
v_tail_3703_ = lean_ctor_get(v_a_3694_, 2);
v___x_3704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_u2082_3691_, v_key_3701_);
lean_inc(v_value_3702_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_value_3702_);
v___x_3706_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v___x_3704_, v___x_3705_);
lean_dec_ref_known(v___x_3705_, 1);
lean_dec(v___x_3704_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3707_ = lean_box(v___y_3699_);
v___x_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
lean_ctor_set(v___x_3709_, 1, v___x_3696_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
else
{
v_a_3694_ = v_tail_3703_;
v_a_3695_ = v___x_3697_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_m_u2082_3715_, lean_object* v___x_3716_, lean_object* v___x_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3715_, v___x_3716_, v___x_3717_, v_a_3718_, v_a_3719_);
lean_dec(v_a_3718_);
lean_dec(v___x_3717_);
lean_dec(v___x_3716_);
lean_dec_ref(v_m_u2082_3715_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_m_u2082_3721_, lean_object* v___x_3722_, lean_object* v___x_3723_, lean_object* v_as_3724_, size_t v_sz_3725_, size_t v_i_3726_, lean_object* v_b_3727_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_usize_dec_lt(v_i_3726_, v_sz_3725_);
if (v___x_3728_ == 0)
{
return v_b_3727_;
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3730_; 
v_a_3729_ = lean_array_uget_borrowed(v_as_3724_, v_i_3726_);
v___x_3730_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3721_, v___x_3722_, v___x_3723_, v_a_3729_, v_b_3727_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
return v_a_3731_;
}
else
{
lean_object* v_a_3732_; size_t v___x_3733_; size_t v___x_3734_; 
v_a_3732_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3733_ = ((size_t)1ULL);
v___x_3734_ = lean_usize_add(v_i_3726_, v___x_3733_);
v_i_3726_ = v___x_3734_;
v_b_3727_ = v_a_3732_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_m_u2082_3736_, lean_object* v___x_3737_, lean_object* v___x_3738_, lean_object* v_as_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_b_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3736_, v___x_3737_, v___x_3738_, v_as_3739_, v_sz_boxed_3743_, v_i_boxed_3744_, v_b_3742_);
lean_dec_ref(v_as_3739_);
lean_dec(v___x_3738_);
lean_dec(v___x_3737_);
lean_dec_ref(v_m_u2082_3736_);
return v_res_3745_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object* v_m_u2081_3746_, lean_object* v_m_u2082_3747_){
_start:
{
lean_object* v_size_3748_; lean_object* v_buckets_3749_; lean_object* v_size_3750_; uint8_t v___x_3751_; 
v_size_3748_ = lean_ctor_get(v_m_u2081_3746_, 0);
v_buckets_3749_ = lean_ctor_get(v_m_u2081_3746_, 1);
v_size_3750_ = lean_ctor_get(v_m_u2082_3747_, 0);
v___x_3751_ = lean_nat_dec_eq(v_size_3748_, v_size_3750_);
if (v___x_3751_ == 0)
{
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; size_t v_sz_3753_; size_t v___x_3754_; lean_object* v___x_3755_; lean_object* v_fst_3756_; 
v___x_3752_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v_sz_3753_ = lean_array_size(v_buckets_3749_);
v___x_3754_ = ((size_t)0ULL);
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3747_, v_size_3748_, v_size_3750_, v_buckets_3749_, v_sz_3753_, v___x_3754_, v___x_3752_);
v_fst_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_fst_3756_);
lean_dec_ref(v___x_3755_);
if (lean_obj_tag(v_fst_3756_) == 0)
{
return v___x_3751_;
}
else
{
lean_object* v_val_3757_; uint8_t v___x_3758_; 
v_val_3757_ = lean_ctor_get(v_fst_3756_, 0);
lean_inc(v_val_3757_);
lean_dec_ref_known(v_fst_3756_, 1);
v___x_3758_ = lean_unbox(v_val_3757_);
lean_dec(v_val_3757_);
return v___x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_m_u2081_3759_, lean_object* v_m_u2082_3760_){
_start:
{
uint8_t v_res_3761_; lean_object* v_r_3762_; 
v_res_3761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3759_, v_m_u2082_3760_);
lean_dec_ref(v_m_u2082_3760_);
lean_dec_ref(v_m_u2081_3759_);
v_r_3762_ = lean_box(v_res_3761_);
return v_r_3762_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object* v_m_u2081_3763_, lean_object* v_m_u2082_3764_){
_start:
{
uint8_t v___x_3765_; 
v___x_3765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3763_, v_m_u2082_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object* v_m_u2081_3766_, lean_object* v_m_u2082_3767_){
_start:
{
uint8_t v_res_3768_; lean_object* v_r_3769_; 
v_res_3768_ = l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(v_m_u2081_3766_, v_m_u2082_3767_);
lean_dec_ref(v_m_u2082_3767_);
lean_dec_ref(v_m_u2081_3766_);
v_r_3769_ = lean_box(v_res_3768_);
return v_r_3769_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object* v_m_u2081_3770_, lean_object* v_m_u2082_3771_){
_start:
{
uint8_t v___x_3772_; 
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3770_, v_m_u2082_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object* v_m_u2081_3773_, lean_object* v_m_u2082_3774_){
_start:
{
uint8_t v_res_3775_; lean_object* v_r_3776_; 
v_res_3775_ = l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(v_m_u2081_3773_, v_m_u2082_3774_);
lean_dec_ref(v_m_u2082_3774_);
lean_dec_ref(v_m_u2081_3773_);
v_r_3776_ = lean_box(v_res_3775_);
return v_r_3776_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object* v_m_u2081_3777_, lean_object* v_m_u2082_3778_){
_start:
{
uint8_t v___x_3779_; 
v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3777_, v_m_u2082_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object* v_m_u2081_3780_, lean_object* v_m_u2082_3781_){
_start:
{
uint8_t v_res_3782_; lean_object* v_r_3783_; 
v_res_3782_ = l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(v_m_u2081_3780_, v_m_u2082_3781_);
lean_dec_ref(v_m_u2082_3781_);
lean_dec_ref(v_m_u2081_3780_);
v_r_3783_ = lean_box(v_res_3782_);
return v_r_3783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
uint8_t v_sparse_3786_; uint8_t v_separateFinalOperand_3787_; lean_object* v_precs_x3f_3788_; lean_object* v_extendedChainKinds_3789_; uint8_t v_sparse_3790_; uint8_t v_separateFinalOperand_3791_; lean_object* v_precs_x3f_3792_; lean_object* v_extendedChainKinds_3793_; 
v_sparse_3786_ = lean_ctor_get_uint8(v_x_3784_, sizeof(void*)*2);
v_separateFinalOperand_3787_ = lean_ctor_get_uint8(v_x_3784_, sizeof(void*)*2 + 1);
v_precs_x3f_3788_ = lean_ctor_get(v_x_3784_, 0);
v_extendedChainKinds_3789_ = lean_ctor_get(v_x_3784_, 1);
v_sparse_3790_ = lean_ctor_get_uint8(v_x_3785_, sizeof(void*)*2);
v_separateFinalOperand_3791_ = lean_ctor_get_uint8(v_x_3785_, sizeof(void*)*2 + 1);
v_precs_x3f_3792_ = lean_ctor_get(v_x_3785_, 0);
v_extendedChainKinds_3793_ = lean_ctor_get(v_x_3785_, 1);
if (v_sparse_3790_ == 0)
{
if (v_sparse_3786_ == 0)
{
goto v___jp_3797_;
}
else
{
return v_sparse_3790_;
}
}
else
{
if (v_sparse_3786_ == 0)
{
return v_sparse_3786_;
}
else
{
goto v___jp_3797_;
}
}
v___jp_3794_:
{
uint8_t v___x_3795_; 
v___x_3795_ = l_instBEqOption_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_precs_x3f_3788_, v_precs_x3f_3792_);
if (v___x_3795_ == 0)
{
return v___x_3795_;
}
else
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_extendedChainKinds_3789_, v_extendedChainKinds_3793_);
return v___x_3796_;
}
}
v___jp_3797_:
{
if (v_separateFinalOperand_3791_ == 0)
{
if (v_separateFinalOperand_3787_ == 0)
{
goto v___jp_3794_;
}
else
{
return v_separateFinalOperand_3791_;
}
}
else
{
if (v_separateFinalOperand_3787_ == 0)
{
return v_separateFinalOperand_3787_;
}
else
{
goto v___jp_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object* v_x_3798_, lean_object* v_x_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Lean_Fmt_instBEqInfixOperation_beq(v_x_3798_, v_x_3799_);
lean_dec_ref(v_x_3799_);
lean_dec_ref(v_x_3798_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3833_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_));
v___x_3834_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3832_, v___x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2____boxed(lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_32652951____hygCtx___hyg_2_();
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3866_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_));
v___x_3867_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3865_, v___x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2____boxed(lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_74447876____hygCtx___hyg_2_();
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(lean_object* v_x_3870_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_obj_tag_nat(v_x_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___impl___boxed(lean_object* v_x_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Fmt_QuantifierBinders_ctorIdx___impl(v_x_3872_);
lean_dec_ref(v_x_3872_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object* v_t_3874_, lean_object* v_k_3875_){
_start:
{
if (lean_obj_tag(v_t_3874_) == 0)
{
lean_object* v_group_3876_; lean_object* v___x_3877_; 
v_group_3876_ = lean_ctor_get(v_t_3874_, 0);
lean_inc_ref(v_group_3876_);
lean_dec_ref_known(v_t_3874_, 1);
v___x_3877_ = lean_apply_1(v_k_3875_, v_group_3876_);
return v___x_3877_;
}
else
{
lean_object* v_lhs_3878_; lean_object* v_rhs_3879_; lean_object* v___x_3880_; 
v_lhs_3878_ = lean_ctor_get(v_t_3874_, 0);
lean_inc(v_lhs_3878_);
v_rhs_3879_ = lean_ctor_get(v_t_3874_, 1);
lean_inc(v_rhs_3879_);
lean_dec_ref_known(v_t_3874_, 2);
v___x_3880_ = lean_apply_2(v_k_3875_, v_lhs_3878_, v_rhs_3879_);
return v___x_3880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object* v_motive_3881_, lean_object* v_ctorIdx_3882_, lean_object* v_t_3883_, lean_object* v_h_3884_, lean_object* v_k_3885_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3883_, v_k_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object* v_motive_3887_, lean_object* v_ctorIdx_3888_, lean_object* v_t_3889_, lean_object* v_h_3890_, lean_object* v_k_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_Fmt_QuantifierBinders_ctorElim(v_motive_3887_, v_ctorIdx_3888_, v_t_3889_, v_h_3890_, v_k_3891_);
lean_dec(v_ctorIdx_3888_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object* v_t_3893_, lean_object* v_binders_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3893_, v_binders_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object* v_motive_3896_, lean_object* v_t_3897_, lean_object* v_h_3898_, lean_object* v_binders_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3897_, v_binders_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object* v_t_3901_, lean_object* v_pred_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3901_, v_pred_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object* v_motive_3904_, lean_object* v_t_3905_, lean_object* v_h_3906_, lean_object* v_pred_3907_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3905_, v_pred_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3938_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_));
v___x_3939_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3937_, v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2____boxed(lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3375112485____hygCtx___hyg_2_();
return v_res_3941_;
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
