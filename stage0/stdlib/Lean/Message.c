// Lean compiler output
// Module: Lean.Message
// Imports: public import Init.Data.Slice.Array public import Lean.Util.PPExt public import Lean.Util.Sorry import Init.Data.String.Search import Init.Data.Format.Macro import Init.Data.Iterators.Consumers.Collect import Init.Data.String.Length
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_formatRawGoal(lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_instToJsonPosition_toJson(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_simpMacroScopes(lean_object*);
lean_object* l_Lean_ppConstNameWithInfos(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_ofKernelEnv(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedPosition_default;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__0 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__0_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__1 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__1_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__2 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__2_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__3 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__3_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__4 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__4_value;
static const lean_string_object l_Lean_mkErrorStringWithPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_mkErrorStringWithPos___closed__5 = (const lean_object*)&l_Lean_mkErrorStringWithPos___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedMessageSeverity;
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMessageSeverity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instBEqMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqMessageSeverity = (const lean_object*)&l_Lean_instBEqMessageSeverity___closed__0_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "information"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__0_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__0_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__1 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__1_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__2 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__3 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__3_value;
static const lean_string_object l_Lean_instToJsonMessageSeverity_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__4 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value;
static const lean_ctor_object l_Lean_instToJsonMessageSeverity_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value)}};
static const lean_object* l_Lean_instToJsonMessageSeverity_toJson___closed__5 = (const lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonMessageSeverity_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instToJsonMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonMessageSeverity = (const lean_object*)&l_Lean_instToJsonMessageSeverity___closed__0_value;
static const lean_string_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__0_value)}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__1_value;
static const lean_string_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__2 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__2_value)}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__3 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__5 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_instFromJsonMessageSeverity_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_instFromJsonMessageSeverity_fromJson___closed__6 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity_fromJson___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonMessageSeverity_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instFromJsonMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonMessageSeverity = (const lean_object*)&l_Lean_instFromJsonMessageSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringMessageSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageSeverity_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringMessageSeverity___closed__0 = (const lean_object*)&l_Lean_instToStringMessageSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringMessageSeverity = (const lean_object*)&l_Lean_instToStringMessageSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedTraceResult_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedTraceResult;
LEAN_EXPORT uint8_t l_Lean_instBEqTraceResult_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqTraceResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqTraceResult_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqTraceResult___closed__0 = (const lean_object*)&l_Lean_instBEqTraceResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqTraceResult = (const lean_object*)&l_Lean_instBEqTraceResult___closed__0_value;
static const lean_string_object l_Lean_instReprTraceResult_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.TraceResult.success"};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__0 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprTraceResult_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTraceResult_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__1 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__1_value;
static const lean_string_object l_Lean_instReprTraceResult_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.TraceResult.failure"};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__2 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprTraceResult_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTraceResult_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__3 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__3_value;
static const lean_string_object l_Lean_instReprTraceResult_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.TraceResult.error"};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__4 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprTraceResult_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprTraceResult_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprTraceResult_repr___closed__5 = (const lean_object*)&l_Lean_instReprTraceResult_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprTraceResult_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprTraceResult_repr___closed__6;
static lean_once_cell_t l_Lean_instReprTraceResult_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprTraceResult_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprTraceResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprTraceResult_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprTraceResult___closed__0 = (const lean_object*)&l_Lean_instReprTraceResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprTraceResult = (const lean_object*)&l_Lean_instReprTraceResult___closed__0_value;
static const lean_string_object l_Lean_TraceResult_toEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "✅️"};
static const lean_object* l_Lean_TraceResult_toEmoji___closed__0 = (const lean_object*)&l_Lean_TraceResult_toEmoji___closed__0_value;
static const lean_string_object l_Lean_TraceResult_toEmoji___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "❌️"};
static const lean_object* l_Lean_TraceResult_toEmoji___closed__1 = (const lean_object*)&l_Lean_TraceResult_toEmoji___closed__1_value;
static const lean_string_object l_Lean_TraceResult_toEmoji___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 2, .m_data = "💥️"};
static const lean_object* l_Lean_TraceResult_toEmoji___closed__2 = (const lean_object*)&l_Lean_TraceResult_toEmoji___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedMessageData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedMessageData_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData_default = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MessageData_nil___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_nil___closed__0;
LEAN_EXPORT lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_ofSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofSyntax___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_ofSyntax___closed__0 = (const lean_object*)&l_Lean_MessageData_ofSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_ofLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofLevel___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_ofLevel___closed__0 = (const lean_object*)&l_Lean_MessageData_ofLevel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_ofConstName___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__0 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__0_value;
static const lean_string_object l_Lean_MessageData_ofConstName___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fullNames"};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__1 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_ofConstName___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_MessageData_ofConstName___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 29, 178, 193, 83, 135, 18, 31)}};
static const lean_object* l_Lean_MessageData_ofConstName___lam__1___closed__2 = (const lean_object*)&l_Lean_MessageData_ofConstName___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_withExprHover___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l_Lean_MessageData_withExprHover___closed__0 = (const lean_object*)&l_Lean_MessageData_withExprHover___closed__0_value;
static const lean_string_object l_Lean_MessageData_withExprHover___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withExprHover"};
static const lean_object* l_Lean_MessageData_withExprHover___closed__1 = (const lean_object*)&l_Lean_MessageData_withExprHover___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_withExprHover___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_withExprHover___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
static const lean_ctor_object l_Lean_MessageData_withExprHover___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_withExprHover___closed__2_value_aux_0),((lean_object*)&l_Lean_MessageData_withExprHover___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 205, 246, 77, 218, 147, 213, 253)}};
static const lean_object* l_Lean_MessageData_withExprHover___closed__2 = (const lean_object*)&l_Lean_MessageData_withExprHover___closed__2_value;
static const lean_ctor_object l_Lean_MessageData_withExprHover___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MessageData_withExprHover___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MessageData_withExprHover___closed__3 = (const lean_object*)&l_Lean_MessageData_withExprHover___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0;
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1;
static lean_once_cell_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "maxTraceChildren"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 113, 99, 32, 64, 25, 169, 239)}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Maximum number of trace node children to display"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(175, 61, 140, 215, 80, 247, 40, 222)}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_maxTraceChildren;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_mkErrorStringWithPos___closed__1_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__0 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__0_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_MessageData_formatAux___closed__1 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__1_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__2 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__2_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_MessageData_formatAux___closed__3 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__3_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__4 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__4_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_MessageData_formatAux___closed__5 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__5_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__5_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__6 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__6_value;
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_MessageData_formatAux___closed__7;
static const lean_string_object l_Lean_MessageData_formatAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_MessageData_formatAux___closed__8 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__8_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__8_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__9 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__9_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.Message"};
static const lean_object* l_Lean_MessageData_formatAux___closed__10 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__10_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.MessageData.formatAux"};
static const lean_object* l_Lean_MessageData_formatAux___closed__11 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__11_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "MessageData.ofLazy: expected MessageData in Dynamic, got "};
static const lean_object* l_Lean_MessageData_formatAux___closed__12 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MessageData_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MessageData_format___closed__0 = (const lean_object*)&l_Lean_MessageData_format___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instAppend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instAppend___closed__0 = (const lean_object*)&l_Lean_MessageData_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instAppend = (const lean_object*)&l_Lean_MessageData_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofFormat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
static const lean_closure_object l_Lean_MessageData_instCoeString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value),((lean_object*)&l_Lean_MessageData_instCoeString___closed__0_value)} };
static const lean_object* l_Lean_MessageData_instCoeString___closed__2 = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeString = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeFormat = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
static const lean_closure_object l_Lean_MessageData_instCoeLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofLevel, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeLevel___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeLevel = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeExpr = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeName___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeName = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
static const lean_closure_object l_Lean_MessageData_instCoeSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofSyntax, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeSyntax___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeSyntax = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeMVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeMVarId___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeMVarId = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
static const lean_string_object l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeOptionExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeOptionExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeOptionExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeOptionExpr = (const lean_object*)&l_Lean_MessageData_instCoeOptionExpr___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__0;
static const lean_string_object l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__1 = (const lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_arrayExpr_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__1_value)}};
static const lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__2 = (const lean_object*)&l_Lean_MessageData_arrayExpr_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeArrayExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeArrayExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeArrayExpr = (const lean_object*)&l_Lean_MessageData_instCoeArrayExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_ofList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_Lean_MessageData_ofList___closed__0 = (const lean_object*)&l_Lean_MessageData_ofList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_ofList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_ofList___closed__1 = (const lean_object*)&l_Lean_MessageData_ofList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__2;
static const lean_string_object l_Lean_MessageData_ofList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_MessageData_ofList___closed__3 = (const lean_object*)&l_Lean_MessageData_ofList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_ofList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_ofList___closed__4 = (const lean_object*)&l_Lean_MessageData_ofList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__5;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__6;
static lean_once_cell_t l_Lean_MessageData_ofList___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofList___closed__7;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object*);
static const lean_string_object l_Lean_MessageData_orList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "– none –"};
static const lean_object* l_Lean_MessageData_orList___closed__0 = (const lean_object*)&l_Lean_MessageData_orList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__1 = (const lean_object*)&l_Lean_MessageData_orList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__2;
static const lean_string_object l_Lean_MessageData_orList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l_Lean_MessageData_orList___closed__3 = (const lean_object*)&l_Lean_MessageData_orList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__4 = (const lean_object*)&l_Lean_MessageData_orList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__5;
static const lean_string_object l_Lean_MessageData_orList___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", or "};
static const lean_object* l_Lean_MessageData_orList___closed__6 = (const lean_object*)&l_Lean_MessageData_orList___closed__6_value;
static const lean_ctor_object l_Lean_MessageData_orList___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_orList___closed__6_value)}};
static const lean_object* l_Lean_MessageData_orList___closed__7 = (const lean_object*)&l_Lean_MessageData_orList___closed__7_value;
static lean_once_cell_t l_Lean_MessageData_orList___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_orList___closed__8;
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object*);
static const lean_string_object l_Lean_MessageData_andList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lean_MessageData_andList___closed__0 = (const lean_object*)&l_Lean_MessageData_andList___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_andList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_andList___closed__0_value)}};
static const lean_object* l_Lean_MessageData_andList___closed__1 = (const lean_object*)&l_Lean_MessageData_andList___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_andList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_andList___closed__2;
static const lean_string_object l_Lean_MessageData_andList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", and "};
static const lean_object* l_Lean_MessageData_andList___closed__3 = (const lean_object*)&l_Lean_MessageData_andList___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_andList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_andList___closed__3_value)}};
static const lean_object* l_Lean_MessageData_andList___closed__4 = (const lean_object*)&l_Lean_MessageData_andList___closed__4_value;
static lean_once_cell_t l_Lean_MessageData_andList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_andList___closed__5;
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object*);
static lean_once_cell_t l_Lean_MessageData_note___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__0;
static const lean_string_object l_Lean_MessageData_note___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Note: "};
static const lean_object* l_Lean_MessageData_note___closed__1 = (const lean_object*)&l_Lean_MessageData_note___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_note___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_note___closed__1_value)}};
static const lean_object* l_Lean_MessageData_note___closed__2 = (const lean_object*)&l_Lean_MessageData_note___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_note___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__3;
static lean_once_cell_t l_Lean_MessageData_note___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_note___closed__4;
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object*);
static const lean_string_object l_Lean_MessageData_hint_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Hint: "};
static const lean_object* l_Lean_MessageData_hint_x27___closed__0 = (const lean_object*)&l_Lean_MessageData_hint_x27___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_hint_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_hint_x27___closed__0_value)}};
static const lean_object* l_Lean_MessageData_hint_x27___closed__1 = (const lean_object*)&l_Lean_MessageData_hint_x27___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_hint_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_hint_x27___closed__2;
static lean_once_cell_t l_Lean_MessageData_hint_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_hint_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofList, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeList___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeList___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeList = (const lean_object*)&l_Lean_MessageData_instCoeList___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_MessageData_instCoeListExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_instCoeListExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_instCoeListExpr___closed__0 = (const lean_object*)&l_Lean_MessageData_instCoeListExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageData_instCoeListExpr = (const lean_object*)&l_Lean_MessageData_instCoeListExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPosition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "endPos"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "keepFullRange"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isSilent"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caption"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value;
static const lean_string_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value;
static const lean_closure_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9_value;
static const lean_array_object l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10 = (const lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0_value;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "BaseMessage"};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 105, 232, 242, 0, 63, 252, 70)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 201, 140, 230, 1, 55, 95, 217)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8;
static const lean_string_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10;
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonPosition_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value;
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value)} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 71, 4, 163, 123, 133, 137, 84)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20;
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21_value;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 109, 20, 206, 1, 23, 246, 165)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(220, 87, 21, 107, 78, 188, 130, 35)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(6, 63, 220, 237, 219, 125, 166, 5)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(42, 121, 35, 234, 39, 185, 10, 205)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37;
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(157, 185, 242, 82, 251, 25, 14, 198)}};
static const lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38 = (const lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38_value;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40;
static lean_once_cell_t l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41;
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToJsonSerialMessage_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_instToJsonSerialMessage_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonSerialMessage_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonSerialMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonSerialMessage_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonSerialMessage___closed__0 = (const lean_object*)&l_Lean_instToJsonSerialMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonSerialMessage = (const lean_object*)&l_Lean_instToJsonSerialMessage___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SerialMessage"};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 10, 29, 109, 171, 11, 228, 164)}};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__2;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__3;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__4;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__6;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__7;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__8;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__9;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__10;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__11;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__12;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__13;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__14;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__15;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__16;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__17;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__18;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__19;
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonSerialMessage_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 186, 66, 236, 16, 221, 215, 158)}};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__20 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__21;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__22;
static lean_once_cell_t l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonSerialMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonSerialMessage_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonSerialMessage___closed__0 = (const lean_object*)&l_Lean_instFromJsonSerialMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonSerialMessage = (const lean_object*)&l_Lean_instFromJsonSerialMessage___closed__0_value;
static const lean_string_object l_Lean_errorNameSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_errorNameSuffix___closed__0 = (const lean_object*)&l_Lean_errorNameSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_errorNameSuffix = (const lean_object*)&l_Lean_errorNameSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nested"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0 = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object*);
static const lean_ctor_object l_Lean_SerialMessage_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__2_value)}};
static const lean_object* l_Lean_SerialMessage_toString___closed__0 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__0_value;
static const lean_ctor_object l_Lean_SerialMessage_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToJsonMessageSeverity_toJson___closed__4_value)}};
static const lean_object* l_Lean_SerialMessage_toString___closed__1 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__1_value;
static const lean_string_object l_Lean_SerialMessage_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l_Lean_SerialMessage_toString___closed__2 = (const lean_object*)&l_Lean_SerialMessage_toString___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_SerialMessage_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SerialMessage_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SerialMessage_instToString___closed__0 = (const lean_object*)&l_Lean_SerialMessage_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SerialMessage_instToString = (const lean_object*)&l_Lean_SerialMessage_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedMessageLog_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageLog_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedMessageLog_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageLog_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedMessageLog_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageLog_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog;
LEAN_EXPORT lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageLog_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageLog_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageLog_instAppend___closed__0 = (const lean_object*)&l_Lean_MessageLog_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_MessageLog_instAppend = (const lean_object*)&l_Lean_MessageLog_instAppend___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__0;
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__1_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__2 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__3;
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__4 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__4_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__5 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_inlineExprTrailing___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_inlineExprTrailing___lam__0___closed__0 = (const lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_inlineExprTrailing___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__0_value)}};
static const lean_object* l_Lean_inlineExprTrailing___lam__0___closed__1 = (const lean_object*)&l_Lean_inlineExprTrailing___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_inlineExprTrailing___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExprTrailing___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object*, lean_object*);
static const lean_string_object l_Lean_aquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "「"};
static const lean_object* l_Lean_aquote___closed__0 = (const lean_object*)&l_Lean_aquote___closed__0_value;
static const lean_ctor_object l_Lean_aquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_aquote___closed__0_value)}};
static const lean_object* l_Lean_aquote___closed__1 = (const lean_object*)&l_Lean_aquote___closed__1_value;
static lean_once_cell_t l_Lean_aquote___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_aquote___closed__2;
static const lean_string_object l_Lean_aquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "」"};
static const lean_object* l_Lean_aquote___closed__3 = (const lean_object*)&l_Lean_aquote___closed__3_value;
static const lean_ctor_object l_Lean_aquote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_aquote___closed__3_value)}};
static const lean_object* l_Lean_aquote___closed__4 = (const lean_object*)&l_Lean_aquote___closed__4_value;
static lean_once_cell_t l_Lean_aquote___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_aquote___closed__5;
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_stringToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_stringToMessageData___closed__0 = (const lean_object*)&l_Lean_stringToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataExpr = (const lean_object*)&l_Lean_MessageData_instCoeExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataLevel = (const lean_object*)&l_Lean_MessageData_instCoeLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataName = (const lean_object*)&l_Lean_MessageData_instCoeName___closed__0_value;
static const lean_closure_object l_Lean_instToMessageDataString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_stringToMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataString___closed__0 = (const lean_object*)&l_Lean_instToMessageDataString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataString = (const lean_object*)&l_Lean_instToMessageDataString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataSyntax = (const lean_object*)&l_Lean_MessageData_instCoeSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataFormat = (const lean_object*)&l_Lean_MessageData_instCoeString___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataMVarId = (const lean_object*)&l_Lean_MessageData_instCoeMVarId___closed__0_value;
static const lean_closure_object l_Lean_instToMessageDataMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToMessageDataMessageData___closed__0 = (const lean_object*)&l_Lean_instToMessageDataMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataMessageData = (const lean_object*)&l_Lean_instToMessageDataMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToMessageDataSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMessageDataSubarray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataSubarray___redArg___closed__0 = (const lean_object*)&l_Lean_instToMessageDataSubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "some ("};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToMessageDataOption___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_mkErrorStringWithPos___closed__4_value)}};
static const lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_instToMessageDataOption___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOption___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToMessageDataOptionExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMessageDataOptionExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToMessageDataOptionExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMessageDataOptionExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToMessageDataOptionExpr___closed__0 = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToMessageDataOptionExpr = (const lean_object*)&l_Lean_instToMessageDataOptionExpr___closed__0_value;
static const lean_string_object l_Lean_termM_x21___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean_termM_x21___00__closed__0 = (const lean_object*)&l_Lean_termM_x21___00__closed__0_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__1_value_aux_0),((lean_object*)&l_Lean_termM_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean_termM_x21___00__closed__1 = (const lean_object*)&l_Lean_termM_x21___00__closed__1_value;
static const lean_string_object l_Lean_termM_x21___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termM_x21___00__closed__2 = (const lean_object*)&l_Lean_termM_x21___00__closed__2_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termM_x21___00__closed__3 = (const lean_object*)&l_Lean_termM_x21___00__closed__3_value;
static const lean_string_object l_Lean_termM_x21___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean_termM_x21___00__closed__4 = (const lean_object*)&l_Lean_termM_x21___00__closed__4_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__4_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__5 = (const lean_object*)&l_Lean_termM_x21___00__closed__5_value;
static const lean_string_object l_Lean_termM_x21___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_termM_x21___00__closed__6 = (const lean_object*)&l_Lean_termM_x21___00__closed__6_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_termM_x21___00__closed__7 = (const lean_object*)&l_Lean_termM_x21___00__closed__7_value;
static const lean_string_object l_Lean_termM_x21___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_termM_x21___00__closed__8 = (const lean_object*)&l_Lean_termM_x21___00__closed__8_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_termM_x21___00__closed__9 = (const lean_object*)&l_Lean_termM_x21___00__closed__9_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termM_x21___00__closed__10 = (const lean_object*)&l_Lean_termM_x21___00__closed__10_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__7_value),((lean_object*)&l_Lean_termM_x21___00__closed__10_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__11 = (const lean_object*)&l_Lean_termM_x21___00__closed__11_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__3_value),((lean_object*)&l_Lean_termM_x21___00__closed__5_value),((lean_object*)&l_Lean_termM_x21___00__closed__11_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__12 = (const lean_object*)&l_Lean_termM_x21___00__closed__12_value;
static const lean_ctor_object l_Lean_termM_x21___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termM_x21___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_termM_x21___00__closed__12_value)}};
static const lean_object* l_Lean_termM_x21___00__closed__13 = (const lean_object*)&l_Lean_termM_x21___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_termM_x21__ = (const lean_object*)&l_Lean_termM_x21___00__closed__13_value;
static lean_once_cell_t l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__4_value)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5_value;
static const lean_string_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toMessageData"};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value;
static lean_once_cell_t l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(214, 4, 57, 33, 167, 136, 170, 64)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8_value;
static const lean_string_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ToMessageData"};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(14, 83, 41, 225, 154, 14, 42, 20)}};
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 56, 87, 160, 191, 253, 244, 156)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_toMessageList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_toMessageList___closed__0 = (const lean_object*)&l_Lean_toMessageList___closed__0_value;
static lean_once_cell_t l_Lean_toMessageList___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toMessageList___closed__1;
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "(kernel) declaration type mismatch, '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "' has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nbut it is expected to have type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__0;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__1;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) unknown constant '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__2 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__3;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__4 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__4_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__5;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "(kernel) constant has already been declared '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__6 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__6_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__7;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) declaration type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__8 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__8_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__8_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__9 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__10;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) declaration has metavariables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__11 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__11_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__12;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "(kernel) declaration has free variables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__13 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__13_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__14;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', expression: "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__15 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__15_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__16;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) function expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__17 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__17_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__18;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "(kernel) type expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__19 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__19_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__20;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) let-declaration type mismatch '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__21 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__21_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__22;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "(kernel) type mismatch at"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__23 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__23_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__24;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) application type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__25 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__25_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__26;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nargument has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__27 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__27_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__28;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nbut function has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__29 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__29_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__30;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) invalid projection"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__31 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__31_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__32;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) type of theorem '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__33 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__33_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__34;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "' is not a proposition"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__35 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__35_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__36;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "(kernel) "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__37 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__37_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__38;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "(kernel) deterministic timeout"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__39 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__39_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__39_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__40 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__41;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "(kernel) excessive memory consumption detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__42 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__42_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__42_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__43 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__44;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "(kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__45 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__45_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__45_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__46 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__47;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "(kernel) interrupted"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__48 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__48_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__48_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__49 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__50;
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object* v_fileName_7_, lean_object* v_pos_8_, lean_object* v_msg_9_, lean_object* v_endPos_10_, lean_object* v_kind_11_, lean_object* v_name_12_){
_start:
{
lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_32_; lean_object* v___y_33_; lean_object* v___y_34_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___y_53_; uint8_t v___y_54_; lean_object* v___y_70_; 
if (lean_obj_tag(v_endPos_10_) == 0)
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_70_ = v___x_74_;
goto v___jp_69_;
}
else
{
lean_object* v_val_75_; lean_object* v_line_76_; lean_object* v_column_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_val_75_ = lean_ctor_get(v_endPos_10_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_endPos_10_, 1);
v_line_76_ = lean_ctor_get(v_val_75_, 0);
lean_inc(v_line_76_);
v_column_77_ = lean_ctor_get(v_val_75_, 1);
lean_inc(v_column_77_);
lean_dec(v_val_75_);
v___x_78_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__5));
v___x_79_ = l_Nat_reprFast(v_line_76_);
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
v___x_83_ = l_Nat_reprFast(v_column_77_);
v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
lean_dec_ref(v___x_83_);
v___y_70_ = v___x_84_;
goto v___jp_69_;
}
v___jp_13_:
{
lean_object* v_line_16_; lean_object* v_column_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_line_16_ = lean_ctor_get(v_pos_8_, 0);
lean_inc(v_line_16_);
v_column_17_ = lean_ctor_get(v_pos_8_, 1);
lean_inc(v_column_17_);
lean_dec_ref(v_pos_8_);
v___x_18_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
v___x_19_ = lean_string_append(v_fileName_7_, v___x_18_);
v___x_20_ = l_Nat_reprFast(v_line_16_);
v___x_21_ = lean_string_append(v___x_19_, v___x_20_);
lean_dec_ref(v___x_20_);
v___x_22_ = lean_string_append(v___x_21_, v___x_18_);
v___x_23_ = l_Nat_reprFast(v_column_17_);
v___x_24_ = lean_string_append(v___x_22_, v___x_23_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_string_append(v___x_24_, v___y_14_);
lean_dec_ref(v___y_14_);
v___x_26_ = lean_string_append(v___x_25_, v___x_18_);
v___x_27_ = lean_string_append(v___x_26_, v___y_15_);
lean_dec_ref(v___y_15_);
v___x_28_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__1));
v___x_29_ = lean_string_append(v___x_27_, v___x_28_);
v___x_30_ = lean_string_append(v___x_29_, v_msg_9_);
return v___x_30_;
}
v___jp_31_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_string_append(v___y_33_, v___y_34_);
lean_dec_ref(v___y_34_);
v___x_36_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
v___y_14_ = v___y_32_;
v___y_15_ = v___x_37_;
goto v___jp_13_;
}
v___jp_38_:
{
lean_object* v___x_43_; 
lean_inc_ref(v___y_40_);
v___x_43_ = lean_string_append(v___y_40_, v___y_42_);
if (lean_obj_tag(v___y_41_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___y_39_;
v___y_33_ = v___x_43_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_41_, 1);
v___y_32_ = v___y_39_;
v___y_33_ = v___x_43_;
v___y_34_ = v_val_45_;
goto v___jp_31_;
}
}
v___jp_46_:
{
lean_object* v___x_49_; 
v___x_49_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__1));
if (lean_obj_tag(v_kind_11_) == 0)
{
lean_object* v___x_50_; 
v___x_50_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_39_ = v___y_47_;
v___y_40_ = v___x_49_;
v___y_41_ = v___y_48_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___y_47_;
v___y_40_ = v___x_49_;
v___y_41_ = v___y_48_;
v___y_42_ = v_val_51_;
goto v___jp_38_;
}
}
v___jp_52_:
{
if (lean_obj_tag(v_name_12_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(0);
v___y_47_ = v___y_53_;
v___y_48_ = v___x_55_;
goto v___jp_46_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_68_; 
v_val_56_ = lean_ctor_get(v_name_12_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_name_12_);
if (v_isSharedCheck_68_ == 0)
{
v___x_58_ = v_name_12_;
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_name_12_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_68_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_60_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_61_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_56_, v___y_54_);
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
lean_dec_ref(v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_64_ = lean_string_append(v___x_62_, v___x_63_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_64_);
v___x_66_ = v___x_58_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
v___y_47_ = v___y_53_;
v___y_48_ = v___x_66_;
goto v___jp_46_;
}
}
}
}
v___jp_69_:
{
if (lean_obj_tag(v_name_12_) == 0)
{
if (lean_obj_tag(v_kind_11_) == 0)
{
lean_object* v___x_71_; 
v___x_71_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_14_ = v___y_70_;
v___y_15_ = v___x_71_;
goto v___jp_13_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 1;
v___y_53_ = v___y_70_;
v___y_54_ = v___x_72_;
goto v___jp_52_;
}
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 1;
v___y_53_ = v___y_70_;
v___y_54_ = v___x_73_;
goto v___jp_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* v_fileName_85_, lean_object* v_pos_86_, lean_object* v_msg_87_, lean_object* v_endPos_88_, lean_object* v_kind_89_, lean_object* v_name_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_mkErrorStringWithPos(v_fileName_85_, v_pos_86_, v_msg_87_, v_endPos_88_, v_kind_89_, v_name_90_);
lean_dec(v_kind_89_);
lean_dec_ref(v_msg_87_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl(uint8_t v_x_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(v_x_92_);
v___x_94_ = lean_obj_tag_nat(v___x_93_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl___boxed(lean_object* v_x_95_){
_start:
{
uint8_t v_x_4__boxed_96_; lean_object* v_res_97_; 
v_x_4__boxed_96_ = lean_unbox(v_x_95_);
v_res_97_ = l_Lean_MessageSeverity_ctorIdx___impl(v_x_4__boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* v_k_98_){
_start:
{
lean_inc(v_k_98_);
return v_k_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* v_k_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_MessageSeverity_ctorElim___redArg(v_k_99_);
lean_dec(v_k_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_101_, lean_object* v_ctorIdx_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_inc(v_k_105_);
return v_k_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_106_, lean_object* v_ctorIdx_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_k_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l_Lean_MessageSeverity_ctorElim(v_motive_106_, v_ctorIdx_107_, v_t_boxed_111_, v_h_109_, v_k_110_);
lean_dec(v_k_110_);
lean_dec(v_ctorIdx_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_113_){
_start:
{
lean_inc(v_information_113_);
return v_information_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_114_);
lean_dec(v_information_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_information_119_){
_start:
{
lean_inc(v_information_119_);
return v_information_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_information_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l_Lean_MessageSeverity_information_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_information_123_);
lean_dec(v_information_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_126_){
_start:
{
lean_inc(v_warning_126_);
return v_warning_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_127_);
lean_dec(v_warning_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_129_, uint8_t v_t_130_, lean_object* v_h_131_, lean_object* v_warning_132_){
_start:
{
lean_inc(v_warning_132_);
return v_warning_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_warning_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l_Lean_MessageSeverity_warning_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_warning_136_);
lean_dec(v_warning_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* v_error_139_){
_start:
{
lean_inc(v_error_139_);
return v_error_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* v_error_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MessageSeverity_error_elim___redArg(v_error_140_);
lean_dec(v_error_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_142_, uint8_t v_t_143_, lean_object* v_h_144_, lean_object* v_error_145_){
_start:
{
lean_inc(v_error_145_);
return v_error_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_error_149_){
_start:
{
uint8_t v_t_boxed_150_; lean_object* v_res_151_; 
v_t_boxed_150_ = lean_unbox(v_t_147_);
v_res_151_ = l_Lean_MessageSeverity_error_elim(v_motive_146_, v_t_boxed_150_, v_h_148_, v_error_149_);
lean_dec(v_error_149_);
return v_res_151_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_154_, uint8_t v_y_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_156_ = lean_box(v_x_154_);
v___x_157_ = lean_obj_tag_nat(v___x_156_);
lean_dec(v___x_156_);
v___x_158_ = lean_box(v_y_155_);
v___x_159_ = lean_obj_tag_nat(v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_nat_dec_eq(v___x_157_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_161_, lean_object* v_y_162_){
_start:
{
uint8_t v_x_24__boxed_163_; uint8_t v_y_25__boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_x_24__boxed_163_ = lean_unbox(v_x_161_);
v_y_25__boxed_164_ = lean_unbox(v_y_162_);
v_res_165_ = l_Lean_instBEqMessageSeverity_beq(v_x_24__boxed_163_, v_y_25__boxed_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_178_){
_start:
{
switch(v_x_178_)
{
case 0:
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_179_;
}
case 1:
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_180_;
}
default: 
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_x_67__boxed_183_; lean_object* v_res_184_; 
v_x_67__boxed_183_ = lean_unbox(v_x_182_);
v_res_184_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Json_getTag_x3f(v_json_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
v___x_206_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_207_ = lean_string_dec_eq(v_val_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_209_ = lean_string_dec_eq(v_val_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_211_ = lean_string_dec_eq(v_val_205_, v___x_210_);
lean_dec(v_val_205_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_212_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_val_205_);
v___x_214_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v_val_205_);
v___x_215_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_218_){
_start:
{
switch(v_x_218_)
{
case 0:
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_219_;
}
case 1:
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_220_;
}
default: 
{
lean_object* v___x_221_; 
v___x_221_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_222_){
_start:
{
uint8_t v_x_28__boxed_223_; lean_object* v_res_224_; 
v_x_28__boxed_223_ = lean_unbox(v_x_222_);
v_res_224_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl(uint8_t v_x_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(v_x_227_);
v___x_229_ = lean_obj_tag_nat(v___x_228_);
lean_dec(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl___boxed(lean_object* v_x_230_){
_start:
{
uint8_t v_x_4__boxed_231_; lean_object* v_res_232_; 
v_x_4__boxed_231_ = lean_unbox(v_x_230_);
v_res_232_ = l_Lean_TraceResult_ctorIdx___impl(v_x_4__boxed_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg(lean_object* v_k_233_){
_start:
{
lean_inc(v_k_233_);
return v_k_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg___boxed(lean_object* v_k_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_TraceResult_ctorElim___redArg(v_k_234_);
lean_dec(v_k_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim(lean_object* v_motive_236_, lean_object* v_ctorIdx_237_, uint8_t v_t_238_, lean_object* v_h_239_, lean_object* v_k_240_){
_start:
{
lean_inc(v_k_240_);
return v_k_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___boxed(lean_object* v_motive_241_, lean_object* v_ctorIdx_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_k_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Lean_TraceResult_ctorElim(v_motive_241_, v_ctorIdx_242_, v_t_boxed_246_, v_h_244_, v_k_245_);
lean_dec(v_k_245_);
lean_dec(v_ctorIdx_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg(lean_object* v_success_248_){
_start:
{
lean_inc(v_success_248_);
return v_success_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg___boxed(lean_object* v_success_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_TraceResult_success_elim___redArg(v_success_249_);
lean_dec(v_success_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_success_254_){
_start:
{
lean_inc(v_success_254_);
return v_success_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___boxed(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_success_258_){
_start:
{
uint8_t v_t_boxed_259_; lean_object* v_res_260_; 
v_t_boxed_259_ = lean_unbox(v_t_256_);
v_res_260_ = l_Lean_TraceResult_success_elim(v_motive_255_, v_t_boxed_259_, v_h_257_, v_success_258_);
lean_dec(v_success_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg(lean_object* v_failure_261_){
_start:
{
lean_inc(v_failure_261_);
return v_failure_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg___boxed(lean_object* v_failure_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_TraceResult_failure_elim___redArg(v_failure_262_);
lean_dec(v_failure_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim(lean_object* v_motive_264_, uint8_t v_t_265_, lean_object* v_h_266_, lean_object* v_failure_267_){
_start:
{
lean_inc(v_failure_267_);
return v_failure_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___boxed(lean_object* v_motive_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_failure_271_){
_start:
{
uint8_t v_t_boxed_272_; lean_object* v_res_273_; 
v_t_boxed_272_ = lean_unbox(v_t_269_);
v_res_273_ = l_Lean_TraceResult_failure_elim(v_motive_268_, v_t_boxed_272_, v_h_270_, v_failure_271_);
lean_dec(v_failure_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg(lean_object* v_error_274_){
_start:
{
lean_inc(v_error_274_);
return v_error_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg___boxed(lean_object* v_error_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_TraceResult_error_elim___redArg(v_error_275_);
lean_dec(v_error_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim(lean_object* v_motive_277_, uint8_t v_t_278_, lean_object* v_h_279_, lean_object* v_error_280_){
_start:
{
lean_inc(v_error_280_);
return v_error_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___boxed(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_error_284_){
_start:
{
uint8_t v_t_boxed_285_; lean_object* v_res_286_; 
v_t_boxed_285_ = lean_unbox(v_t_282_);
v_res_286_ = l_Lean_TraceResult_error_elim(v_motive_281_, v_t_boxed_285_, v_h_283_, v_error_284_);
lean_dec(v_error_284_);
return v_res_286_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult_default(void){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult(void){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTraceResult_beq(uint8_t v_x_289_, uint8_t v_y_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_291_ = lean_box(v_x_289_);
v___x_292_ = lean_obj_tag_nat(v___x_291_);
lean_dec(v___x_291_);
v___x_293_ = lean_box(v_y_290_);
v___x_294_ = lean_obj_tag_nat(v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_nat_dec_eq(v___x_292_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_296_, lean_object* v_y_297_){
_start:
{
uint8_t v_x_24__boxed_298_; uint8_t v_y_25__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_x_24__boxed_298_ = lean_unbox(v_x_296_);
v_y_25__boxed_299_ = lean_unbox(v_y_297_);
v_res_300_ = l_Lean_instBEqTraceResult_beq(v_x_24__boxed_298_, v_y_25__boxed_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_317_, lean_object* v_prec_318_){
_start:
{
lean_object* v___y_320_; lean_object* v___y_327_; lean_object* v___y_334_; 
switch(v_x_317_)
{
case 0:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v_prec_318_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_320_ = v___x_342_;
goto v___jp_319_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_320_ = v___x_343_;
goto v___jp_319_;
}
}
case 1:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_318_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_327_ = v___x_346_;
goto v___jp_326_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_327_ = v___x_347_;
goto v___jp_326_;
}
}
default: 
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1024u);
v___x_349_ = lean_nat_dec_le(v___x_348_, v_prec_318_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_334_ = v___x_350_;
goto v___jp_333_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_334_ = v___x_351_;
goto v___jp_333_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_320_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = 0;
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_323_);
v___x_325_ = l_Repr_addAppParen(v___x_324_, v_prec_318_);
return v___x_325_;
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___y_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v_prec_318_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_318_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_352_, lean_object* v_prec_353_){
_start:
{
uint8_t v_x_171__boxed_354_; lean_object* v_res_355_; 
v_x_171__boxed_354_ = lean_unbox(v_x_352_);
v_res_355_ = l_Lean_instReprTraceResult_repr(v_x_171__boxed_354_, v_prec_353_);
lean_dec(v_prec_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_361_){
_start:
{
switch(v_x_361_)
{
case 0:
{
lean_object* v___x_362_; 
v___x_362_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_362_;
}
case 1:
{
lean_object* v___x_363_; 
v___x_363_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_363_;
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_365_){
_start:
{
uint8_t v_x_31__boxed_366_; lean_object* v_res_367_; 
v_x_31__boxed_366_ = lean_unbox(v_x_365_);
v_res_367_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl(lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_tag_nat(v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl___boxed(lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MessageData_ctorIdx___impl(v_x_370_);
lean_dec_ref(v_x_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_372_, lean_object* v_k_373_){
_start:
{
switch(lean_obj_tag(v_t_372_))
{
case 0:
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_374_);
lean_dec_ref_known(v_t_372_, 1);
v___x_375_ = lean_apply_1(v_k_373_, v_a_374_);
return v___x_375_;
}
case 1:
{
lean_object* v_a_376_; lean_object* v___x_377_; 
v_a_376_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_t_372_, 1);
v___x_377_ = lean_apply_1(v_k_373_, v_a_376_);
return v___x_377_;
}
case 5:
{
lean_object* v_a_378_; lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_378_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_378_);
v_a_379_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_379_);
lean_dec_ref_known(v_t_372_, 2);
v___x_380_ = lean_apply_2(v_k_373_, v_a_378_, v_a_379_);
return v___x_380_;
}
case 6:
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_381_);
lean_dec_ref_known(v_t_372_, 1);
v___x_382_ = lean_apply_1(v_k_373_, v_a_381_);
return v___x_382_;
}
case 8:
{
lean_object* v_a_383_; lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_383_);
v_a_384_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_t_372_, 2);
v___x_385_ = lean_apply_2(v_k_373_, v_a_383_, v_a_384_);
return v___x_385_;
}
case 9:
{
lean_object* v_data_386_; lean_object* v_msg_387_; lean_object* v_children_388_; lean_object* v___x_389_; 
v_data_386_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_data_386_);
v_msg_387_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_msg_387_);
v_children_388_ = lean_ctor_get(v_t_372_, 2);
lean_inc_ref(v_children_388_);
lean_dec_ref_known(v_t_372_, 3);
v___x_389_ = lean_apply_3(v_k_373_, v_data_386_, v_msg_387_, v_children_388_);
return v___x_389_;
}
case 11:
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_390_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_390_);
v_a_391_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_391_);
lean_dec_ref_known(v_t_372_, 2);
v___x_392_ = lean_apply_2(v_k_373_, v_a_390_, v_a_391_);
return v___x_392_;
}
default: 
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_393_);
v_a_394_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_394_);
lean_dec_ref(v_t_372_);
v___x_395_ = lean_apply_2(v_k_373_, v_a_393_, v_a_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_396_, lean_object* v_ctorIdx_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_MessageData_ctorElim___redArg(v_t_398_, v_k_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_MessageData_ctorElim(v_motive__1_402_, v_ctorIdx_403_, v_t_404_, v_h_405_, v_k_406_);
lean_dec(v_ctorIdx_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_408_, lean_object* v_ofFormatWithInfos_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_MessageData_ctorElim___redArg(v_t_408_, v_ofFormatWithInfos_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_ofFormatWithInfos_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_MessageData_ctorElim___redArg(v_t_412_, v_ofFormatWithInfos_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_416_, lean_object* v_ofGoal_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MessageData_ctorElim___redArg(v_t_416_, v_ofGoal_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_ofGoal_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_MessageData_ctorElim___redArg(v_t_420_, v_ofGoal_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_424_, lean_object* v_ofWidget_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_MessageData_ctorElim___redArg(v_t_424_, v_ofWidget_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_ofWidget_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MessageData_ctorElim___redArg(v_t_428_, v_ofWidget_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_432_, lean_object* v_withContext_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MessageData_ctorElim___redArg(v_t_432_, v_withContext_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_withContext_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MessageData_ctorElim___redArg(v_t_436_, v_withContext_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_440_, lean_object* v_withNamingContext_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_MessageData_ctorElim___redArg(v_t_440_, v_withNamingContext_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_withNamingContext_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_MessageData_ctorElim___redArg(v_t_444_, v_withNamingContext_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_448_, lean_object* v_nest_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_MessageData_ctorElim___redArg(v_t_448_, v_nest_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_nest_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MessageData_ctorElim___redArg(v_t_452_, v_nest_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_456_, lean_object* v_group_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MessageData_ctorElim___redArg(v_t_456_, v_group_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_group_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_MessageData_ctorElim___redArg(v_t_460_, v_group_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_464_, lean_object* v_compose_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_MessageData_ctorElim___redArg(v_t_464_, v_compose_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_compose_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MessageData_ctorElim___redArg(v_t_468_, v_compose_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_472_, lean_object* v_tagged_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_MessageData_ctorElim___redArg(v_t_472_, v_tagged_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_tagged_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MessageData_ctorElim___redArg(v_t_476_, v_tagged_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_480_, lean_object* v_trace_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MessageData_ctorElim___redArg(v_t_480_, v_trace_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_trace_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MessageData_ctorElim___redArg(v_t_484_, v_trace_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_488_, lean_object* v_ofLazy_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_MessageData_ctorElim___redArg(v_t_488_, v_ofLazy_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_ofLazy_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MessageData_ctorElim___redArg(v_t_492_, v_ofLazy_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_496_, lean_object* v_ofOriginatingSyntax_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_MessageData_ctorElim___redArg(v_t_496_, v_ofOriginatingSyntax_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_ofOriginatingSyntax_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_MessageData_ctorElim___redArg(v_t_500_, v_ofOriginatingSyntax_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_box(1);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_fmt_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_519_, lean_object* v_onMissingContext_520_, lean_object* v_f_521_, lean_object* v_ctx_x3f_522_){
_start:
{
lean_object* v_msg_525_; 
if (lean_obj_tag(v_ctx_x3f_522_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_f_521_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_2(v_onMissingContext_520_, v___x_527_, lean_box(0));
v_msg_525_ = v___x_528_;
goto v___jp_524_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; 
lean_dec_ref(v_onMissingContext_520_);
v_val_529_ = lean_ctor_get(v_ctx_x3f_522_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v_ctx_x3f_522_, 1);
v___x_530_ = lean_apply_2(v_f_521_, v_val_529_, lean_box(0));
v_msg_525_ = v___x_530_;
goto v___jp_524_;
}
v___jp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_519_);
lean_ctor_set(v___x_526_, 1, v_msg_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_531_, lean_object* v_onMissingContext_532_, lean_object* v_f_533_, lean_object* v_ctx_x3f_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_MessageData_lazy___lam__0(v___x_531_, v_onMissingContext_532_, v_f_533_, v_ctx_x3f_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_537_, lean_object* v_hasSyntheticSorry_538_, lean_object* v_onMissingContext_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_541_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_541_, 0, v___x_540_);
lean_closure_set(v___f_541_, 1, v_onMissingContext_539_);
lean_closure_set(v___f_541_, 2, v_f_537_);
v___x_542_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_542_, 0, v___f_541_);
lean_ctor_set(v___x_542_, 1, v_hasSyntheticSorry_538_);
return v___x_542_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_543_, lean_object* v_x_544_){
_start:
{
switch(lean_obj_tag(v_x_544_))
{
case 3:
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_545_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_545_;
goto _start;
}
case 4:
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_547_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_547_;
goto _start;
}
case 5:
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_549_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_549_;
goto _start;
}
case 6:
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_a_551_);
lean_dec_ref_known(v_x_544_, 1);
v_x_544_ = v_a_551_;
goto _start;
}
case 7:
{
lean_object* v_a_553_; lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_553_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_a_553_);
v_a_554_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_554_);
lean_dec_ref_known(v_x_544_, 2);
lean_inc_ref(v_p_543_);
v___x_555_ = l_Lean_MessageData_hasTag(v_p_543_, v_a_553_);
if (v___x_555_ == 0)
{
v_x_544_ = v_a_554_;
goto _start;
}
else
{
lean_dec_ref(v_a_554_);
lean_dec_ref(v_p_543_);
return v___x_555_;
}
}
case 8:
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_a_557_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_557_);
v_a_558_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_558_);
lean_dec_ref_known(v_x_544_, 2);
lean_inc_ref(v_p_543_);
v___x_559_ = lean_apply_1(v_p_543_, v_a_557_);
v___x_560_ = lean_unbox(v___x_559_);
if (v___x_560_ == 0)
{
v_x_544_ = v_a_558_;
goto _start;
}
else
{
uint8_t v___x_562_; 
lean_dec_ref(v_a_558_);
lean_dec_ref(v_p_543_);
v___x_562_ = lean_unbox(v___x_559_);
return v___x_562_;
}
}
case 9:
{
lean_object* v_data_563_; lean_object* v_msg_564_; lean_object* v_children_565_; lean_object* v_cls_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_data_563_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_data_563_);
v_msg_564_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_msg_564_);
v_children_565_ = lean_ctor_get(v_x_544_, 2);
lean_inc_ref(v_children_565_);
lean_dec_ref_known(v_x_544_, 3);
v_cls_566_ = lean_ctor_get(v_data_563_, 0);
lean_inc(v_cls_566_);
lean_dec_ref(v_data_563_);
lean_inc_ref(v_p_543_);
v___x_567_ = lean_apply_1(v_p_543_, v_cls_566_);
v___x_568_ = lean_unbox(v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; 
lean_inc_ref(v_p_543_);
v___x_569_ = l_Lean_MessageData_hasTag(v_p_543_, v_msg_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_size(v_children_565_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_572_;
}
else
{
if (v___x_572_ == 0)
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_572_;
}
else
{
size_t v___x_573_; size_t v___x_574_; uint8_t v___x_575_; 
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_571_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_543_, v_children_565_, v___x_573_, v___x_574_);
lean_dec_ref(v_children_565_);
return v___x_575_;
}
}
}
else
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_569_;
}
}
else
{
uint8_t v___x_576_; 
lean_dec_ref(v_children_565_);
lean_dec_ref(v_msg_564_);
lean_dec_ref(v_p_543_);
v___x_576_ = lean_unbox(v___x_567_);
return v___x_576_;
}
}
case 11:
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_577_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_577_;
goto _start;
}
default: 
{
uint8_t v___x_579_; 
lean_dec_ref(v_x_544_);
lean_dec_ref(v_p_543_);
v___x_579_ = 0;
return v___x_579_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_580_, lean_object* v_as_581_, size_t v_i_582_, size_t v_stop_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_usize_dec_eq(v_i_582_, v_stop_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_array_uget_borrowed(v_as_581_, v_i_582_);
lean_inc(v___x_585_);
lean_inc_ref(v_p_580_);
v___x_586_ = l_Lean_MessageData_hasTag(v_p_580_, v___x_585_);
if (v___x_586_ == 0)
{
size_t v___x_587_; size_t v___x_588_; 
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_582_, v___x_587_);
v_i_582_ = v___x_588_;
goto _start;
}
else
{
lean_dec_ref(v_p_580_);
return v___x_586_;
}
}
else
{
uint8_t v___x_590_; 
lean_dec_ref(v_p_580_);
v___x_590_ = 0;
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_stop_594_){
_start:
{
size_t v_i_boxed_595_; size_t v_stop_boxed_596_; uint8_t v_res_597_; lean_object* v_r_598_; 
v_i_boxed_595_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_stop_boxed_596_ = lean_unbox_usize(v_stop_594_);
lean_dec(v_stop_594_);
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_591_, v_as_592_, v_i_boxed_595_, v_stop_boxed_596_);
lean_dec_ref(v_as_592_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_MessageData_hasTag(v_p_599_, v_x_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 3:
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_604_;
goto _start;
}
case 4:
{
lean_object* v_a_606_; 
v_a_606_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_606_;
goto _start;
}
case 8:
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_608_);
return v_a_608_;
}
case 9:
{
lean_object* v_data_609_; lean_object* v_cls_610_; 
v_data_609_ = lean_ctor_get(v_x_603_, 0);
v_cls_610_ = lean_ctor_get(v_data_609_, 0);
lean_inc(v_cls_610_);
return v_cls_610_;
}
case 11:
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_611_;
goto _start;
}
default: 
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_MessageData_kind(v_x_614_);
lean_dec_ref(v_x_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 11)
{
lean_object* v_a_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_a_617_ = lean_ctor_get(v_x_616_, 0);
v_a_618_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_inc(v_a_617_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_a_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 0);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_a_618_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_x_616_);
return v___x_628_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_629_){
_start:
{
switch(lean_obj_tag(v_x_629_))
{
case 3:
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_630_;
goto _start;
}
case 4:
{
lean_object* v_a_632_; 
v_a_632_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_632_;
goto _start;
}
case 8:
{
lean_object* v_a_634_; 
v_a_634_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_634_;
goto _start;
}
case 9:
{
uint8_t v___x_636_; 
v___x_636_ = 1;
return v___x_636_;
}
case 11:
{
lean_object* v_a_637_; 
v_a_637_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_637_;
goto _start;
}
default: 
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_MessageData_isTrace(v_x_640_);
lean_dec_ref(v_x_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
switch(lean_obj_tag(v_x_643_))
{
case 3:
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_a_645_ = lean_ctor_get(v_x_643_, 0);
v_a_646_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_x_643_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_inc(v_a_645_);
lean_dec(v_x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_MessageData_composePreservingKind(v_a_646_, v_x_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
case 4:
{
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_655_ = lean_ctor_get(v_x_643_, 0);
v_a_656_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_x_643_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v_x_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_MessageData_composePreservingKind(v_a_656_, v_x_644_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
case 8:
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v_x_643_, 0);
v_a_666_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_x_643_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v_x_643_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 7);
lean_ctor_set(v___x_668_, 1, v_x_644_);
lean_ctor_set(v___x_668_, 0, v_a_666_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_x_644_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_672_, 0, v_a_665_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
return v___x_672_;
}
}
}
case 11:
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_a_675_ = lean_ctor_get(v_x_643_, 0);
v_a_676_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_643_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v_x_643_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_MessageData_composePreservingKind(v_a_676_, v_x_644_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
default: 
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v_x_643_);
lean_ctor_set(v___x_685_, 1, v_x_644_);
return v___x_685_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(0);
v___x_687_ = l_Lean_MessageData_ofFormat(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_689_, lean_object* v_ctx_690_){
_start:
{
lean_object* v_env_691_; lean_object* v_mctx_692_; lean_object* v_lctx_693_; lean_object* v_opts_694_; lean_object* v_currNamespace_695_; lean_object* v_openDecls_696_; lean_object* v___x_697_; 
v_env_691_ = lean_ctor_get(v_ctx_690_, 0);
v_mctx_692_ = lean_ctor_get(v_ctx_690_, 1);
v_lctx_693_ = lean_ctor_get(v_ctx_690_, 2);
v_opts_694_ = lean_ctor_get(v_ctx_690_, 3);
v_currNamespace_695_ = lean_ctor_get(v_nCtx_689_, 0);
v_openDecls_696_ = lean_ctor_get(v_nCtx_689_, 1);
lean_inc(v_openDecls_696_);
lean_inc(v_currNamespace_695_);
lean_inc_ref(v_opts_694_);
lean_inc_ref(v_lctx_693_);
lean_inc_ref(v_mctx_692_);
lean_inc_ref(v_env_691_);
v___x_697_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_697_, 0, v_env_691_);
lean_ctor_set(v___x_697_, 1, v_mctx_692_);
lean_ctor_set(v___x_697_, 2, v_lctx_693_);
lean_ctor_set(v___x_697_, 3, v_opts_694_);
lean_ctor_set(v___x_697_, 4, v_currNamespace_695_);
lean_ctor_set(v___x_697_, 5, v_openDecls_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_698_, lean_object* v_ctx_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_MessageData_mkPPContext(v_nCtx_698_, v_ctx_699_);
lean_dec_ref(v_ctx_699_);
lean_dec_ref(v_nCtx_698_);
return v_res_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_703_);
lean_dec_ref(v_x_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_706_, lean_object* v_stx_707_, lean_object* v_ctx_x3f_708_){
_start:
{
lean_object* v_val_711_; 
if (lean_obj_tag(v_ctx_x3f_708_) == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
v___x_715_ = 0;
v___x_716_ = l_Lean_Syntax_formatStx(v_stx_707_, v___x_714_, v___x_715_);
v_val_711_ = v___x_716_;
goto v___jp_710_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_718_; 
v_val_717_ = lean_ctor_get(v_ctx_x3f_708_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_ctx_x3f_708_, 1);
v___x_718_ = l_Lean_ppTerm(v_val_717_, v_stx_707_);
v_val_711_ = v___x_718_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Lean_MessageData_ofFormat(v_val_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_706_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_719_, lean_object* v_stx_720_, lean_object* v_ctx_x3f_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_719_, v_stx_720_, v_ctx_x3f_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_725_){
_start:
{
lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_stx_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v___f_726_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_727_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_728_ = lean_box(0);
v_stx_729_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_725_, v___x_728_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_730_, 0, v___x_727_);
lean_closure_set(v___f_730_, 1, v_stx_729_);
v___x_731_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_731_, 0, v___f_730_);
lean_ctor_set(v___x_731_, 1, v___f_726_);
return v___x_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_732_, lean_object* v_mctx_733_){
_start:
{
lean_object* v___x_734_; lean_object* v_fst_735_; uint8_t v___x_736_; 
v___x_734_ = l_Lean_instantiateMVarsCore(v_mctx_733_, v_e_732_);
v_fst_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_fst_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_Lean_Expr_hasSyntheticSorry(v_fst_735_);
lean_dec(v_fst_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_737_, lean_object* v_mctx_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_MessageData_ofExpr___lam__0(v_e_737_, v_mctx_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_741_, lean_object* v_e_742_, lean_object* v_ctx_x3f_743_){
_start:
{
lean_object* v_val_746_; 
if (lean_obj_tag(v_ctx_x3f_743_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_expr_dbg_to_string(v_e_742_);
lean_dec_ref(v_e_742_);
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = lean_box(1);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v_val_746_ = v___x_752_;
goto v___jp_745_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
v_val_753_ = lean_ctor_get(v_ctx_x3f_743_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_ctx_x3f_743_, 1);
v___x_754_ = l_Lean_ppExprWithInfos(v_val_753_, v_e_742_);
v_val_746_ = v___x_754_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_val_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_741_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_755_, lean_object* v_e_756_, lean_object* v_ctx_x3f_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_MessageData_ofExpr___lam__1(v___x_755_, v_e_756_, v_ctx_x3f_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_760_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
lean_inc_ref(v_e_760_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_761_, 0, v_e_760_);
v___x_762_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_763_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_763_, 0, v___x_762_);
lean_closure_set(v___f_763_, 1, v_e_760_);
v___x_764_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_764_, 0, v___f_763_);
lean_ctor_set(v___x_764_, 1, v___f_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_box(0);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_MessageData_ofLevel___lam__0(v_x_767_);
lean_dec(v_x_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_769_, lean_object* v_l_770_, lean_object* v___f_771_, lean_object* v_ctx_x3f_772_){
_start:
{
lean_object* v_val_775_; 
if (lean_obj_tag(v_ctx_x3f_772_) == 0)
{
uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = 1;
v___x_779_ = l_Lean_Level_format(v_l_770_, v___x_778_, v___f_771_);
v_val_775_ = v___x_779_;
goto v___jp_774_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_781_; 
lean_dec_ref(v___f_771_);
v_val_780_ = lean_ctor_get(v_ctx_x3f_772_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_ctx_x3f_772_, 1);
v___x_781_ = l_Lean_ppLevel(v_val_780_, v_l_770_);
v_val_775_ = v___x_781_;
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Lean_MessageData_ofFormat(v_val_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_769_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_782_, lean_object* v_l_783_, lean_object* v___f_784_, lean_object* v_ctx_x3f_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_MessageData_ofLevel___lam__2(v___x_782_, v_l_783_, v___f_784_, v_ctx_x3f_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_789_){
_start:
{
lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_790_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_791_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_792_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_793_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_793_, 0, v___x_792_);
lean_closure_set(v___f_793_, 1, v_l_789_);
lean_closure_set(v___f_793_, 2, v___f_790_);
v___x_794_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_794_, 0, v___f_793_);
lean_ctor_set(v___x_794_, 1, v___f_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_795_){
_start:
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = 1;
v___x_797_ = l_Lean_Name_toString(v_n_795_, v___x_796_);
v___x_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = l_Lean_MessageData_ofFormat(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_803_, lean_object* v_k_804_, uint8_t v_v_805_){
_start:
{
lean_object* v_map_806_; uint8_t v_hasTrace_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_821_; 
v_map_806_ = lean_ctor_get(v_o_803_, 0);
v_hasTrace_807_ = lean_ctor_get_uint8(v_o_803_, sizeof(void*)*1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_o_803_);
if (v_isSharedCheck_821_ == 0)
{
v___x_809_ = v_o_803_;
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_map_806_);
lean_dec(v_o_803_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_811_, 0, v_v_805_);
lean_inc(v_k_804_);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_804_, v___x_811_, v_map_806_);
if (v_hasTrace_807_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_816_; 
v___x_813_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_814_ = l_Lean_Name_isPrefixOf(v___x_813_, v_k_804_);
lean_dec(v_k_804_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_812_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_814_);
return v___x_816_;
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_k_804_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_819_ = v___x_809_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*1, v_hasTrace_807_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_822_, lean_object* v_k_823_, lean_object* v_v_824_){
_start:
{
uint8_t v_v_boxed_825_; lean_object* v_res_826_; 
v_v_boxed_825_ = lean_unbox(v_v_824_);
v_res_826_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_822_, v_k_823_, v_v_boxed_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_832_, lean_object* v_constName_833_, uint8_t v_fullNames_834_, lean_object* v_ctx_x3f_835_){
_start:
{
lean_object* v_val_838_; lean_object* v___y_842_; 
if (lean_obj_tag(v_ctx_x3f_835_) == 0)
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = 1;
v___x_844_ = l_Lean_Name_toString(v_constName_833_, v___x_843_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_box(1);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v_val_838_ = v___x_847_;
goto v___jp_837_;
}
else
{
if (v_fullNames_834_ == 0)
{
lean_object* v_val_848_; lean_object* v___x_849_; 
v_val_848_ = lean_ctor_get(v_ctx_x3f_835_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_ctx_x3f_835_, 1);
v___x_849_ = l_Lean_ppConstNameWithInfos(v_val_848_, v_constName_833_);
v___y_842_ = v___x_849_;
goto v___jp_841_;
}
else
{
lean_object* v_val_850_; lean_object* v_env_851_; lean_object* v_mctx_852_; lean_object* v_lctx_853_; lean_object* v_opts_854_; lean_object* v_currNamespace_855_; lean_object* v_openDecls_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_val_850_ = lean_ctor_get(v_ctx_x3f_835_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_ctx_x3f_835_, 1);
v_env_851_ = lean_ctor_get(v_val_850_, 0);
v_mctx_852_ = lean_ctor_get(v_val_850_, 1);
v_lctx_853_ = lean_ctor_get(v_val_850_, 2);
v_opts_854_ = lean_ctor_get(v_val_850_, 3);
v_currNamespace_855_ = lean_ctor_get(v_val_850_, 4);
v_openDecls_856_ = lean_ctor_get(v_val_850_, 5);
v_isSharedCheck_866_ = !lean_is_exclusive(v_val_850_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v_val_850_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_openDecls_856_);
lean_inc(v_currNamespace_855_);
lean_inc(v_opts_854_);
lean_inc(v_lctx_853_);
lean_inc(v_mctx_852_);
lean_inc(v_env_851_);
lean_dec(v_val_850_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_861_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_854_, v___x_860_, v_fullNames_834_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 3, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_env_851_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_mctx_852_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_lctx_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_currNamespace_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v_openDecls_856_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_ppConstNameWithInfos(v___x_863_, v_constName_833_);
v___y_842_ = v___x_864_;
goto v___jp_841_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_val_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_832_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
v___jp_841_:
{
v_val_838_ = v___y_842_;
goto v___jp_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_867_, lean_object* v_constName_868_, lean_object* v_fullNames_869_, lean_object* v_ctx_x3f_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_fullNames_boxed_872_; lean_object* v_res_873_; 
v_fullNames_boxed_872_ = lean_unbox(v_fullNames_869_);
v_res_873_ = l_Lean_MessageData_ofConstName___lam__1(v___x_867_, v_constName_868_, v_fullNames_boxed_872_, v_ctx_x3f_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_874_, uint8_t v_fullNames_875_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; 
v___f_876_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_877_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_878_ = lean_box(v_fullNames_875_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_879_, 0, v___x_877_);
lean_closure_set(v___f_879_, 1, v_constName_874_);
lean_closure_set(v___f_879_, 2, v___x_878_);
v___x_880_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_880_, 0, v___f_879_);
lean_ctor_set(v___x_880_, 1, v___f_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_881_, lean_object* v_fullNames_882_){
_start:
{
uint8_t v_fullNames_boxed_883_; lean_object* v_res_884_; 
v_fullNames_boxed_883_ = lean_unbox(v_fullNames_882_);
v_res_884_ = l_Lean_MessageData_ofConstName(v_constName_881_, v_fullNames_boxed_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_val_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_MessageData_withExprHover___lam__0(v_val_889_, v___y_890_);
lean_dec_ref(v___y_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_893_, lean_object* v_v_894_, lean_object* v_t_895_){
_start:
{
if (lean_obj_tag(v_t_895_) == 0)
{
lean_object* v_size_896_; lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_l_899_; lean_object* v_r_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_1181_; 
v_size_896_ = lean_ctor_get(v_t_895_, 0);
v_k_897_ = lean_ctor_get(v_t_895_, 1);
v_v_898_ = lean_ctor_get(v_t_895_, 2);
v_l_899_ = lean_ctor_get(v_t_895_, 3);
v_r_900_ = lean_ctor_get(v_t_895_, 4);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_t_895_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_902_ = v_t_895_;
v_isShared_903_ = v_isSharedCheck_1181_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_r_900_);
lean_inc(v_l_899_);
lean_inc(v_v_898_);
lean_inc(v_k_897_);
lean_inc(v_size_896_);
lean_dec(v_t_895_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_1181_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_lt(v_k_893_, v_k_897_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_eq(v_k_893_, v_k_897_);
if (v___x_905_ == 0)
{
lean_object* v_impl_906_; lean_object* v___x_907_; 
lean_dec(v_size_896_);
v_impl_906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_893_, v_v_894_, v_r_900_);
v___x_907_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_899_) == 0)
{
lean_object* v_size_908_; lean_object* v_size_909_; lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_l_912_; lean_object* v_r_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_size_908_ = lean_ctor_get(v_l_899_, 0);
v_size_909_ = lean_ctor_get(v_impl_906_, 0);
v_k_910_ = lean_ctor_get(v_impl_906_, 1);
v_v_911_ = lean_ctor_get(v_impl_906_, 2);
v_l_912_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_912_);
v_r_913_ = lean_ctor_get(v_impl_906_, 4);
v___x_914_ = lean_unsigned_to_nat(3u);
v___x_915_ = lean_nat_mul(v___x_914_, v_size_908_);
v___x_916_ = lean_nat_dec_lt(v___x_915_, v_size_909_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec(v_l_912_);
v___x_917_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_918_ = lean_nat_add(v___x_917_, v_size_909_);
lean_dec(v___x_917_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_impl_906_);
lean_ctor_set(v___x_902_, 0, v___x_918_);
v___x_920_ = v___x_902_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_impl_906_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_985_; 
lean_inc(v_r_913_);
lean_inc(v_v_911_);
lean_inc(v_k_910_);
lean_inc(v_size_909_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_impl_906_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_impl_906_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_990_);
v___x_923_ = v_impl_906_;
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_impl_906_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_size_925_; lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_l_928_; lean_object* v_r_929_; lean_object* v_size_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_size_925_ = lean_ctor_get(v_l_912_, 0);
v_k_926_ = lean_ctor_get(v_l_912_, 1);
v_v_927_ = lean_ctor_get(v_l_912_, 2);
v_l_928_ = lean_ctor_get(v_l_912_, 3);
v_r_929_ = lean_ctor_get(v_l_912_, 4);
v_size_930_ = lean_ctor_get(v_r_913_, 0);
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = lean_nat_mul(v___x_931_, v_size_930_);
v___x_933_ = lean_nat_dec_lt(v_size_925_, v___x_932_);
lean_dec(v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_r_929_);
lean_inc(v_l_928_);
lean_inc(v_v_927_);
lean_inc(v_k_926_);
v_isSharedCheck_961_ = !lean_is_exclusive(v_l_912_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_962_ = lean_ctor_get(v_l_912_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_912_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_912_, 2);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_912_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_l_912_, 0);
lean_dec(v_unused_966_);
v___x_935_ = v_l_912_;
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_l_912_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_951_; 
v___x_937_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_938_ = lean_nat_add(v___x_937_, v_size_909_);
lean_dec(v_size_909_);
if (lean_obj_tag(v_l_928_) == 0)
{
lean_object* v_size_959_; 
v_size_959_ = lean_ctor_get(v_l_928_, 0);
lean_inc(v_size_959_);
v___y_951_ = v_size_959_;
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___y_951_ = v___x_960_;
goto v___jp_950_;
}
v___jp_939_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_nat_add(v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_r_913_);
lean_ctor_set(v___x_935_, 3, v_r_929_);
lean_ctor_set(v___x_935_, 2, v_v_911_);
lean_ctor_set(v___x_935_, 1, v_k_910_);
lean_ctor_set(v___x_935_, 0, v___x_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_r_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_r_913_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v___x_945_);
lean_ctor_set(v___x_923_, 3, v___y_940_);
lean_ctor_set(v___x_923_, 2, v_v_927_);
lean_ctor_set(v___x_923_, 1, v_k_926_);
lean_ctor_set(v___x_923_, 0, v___x_938_);
v___x_947_ = v___x_923_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v___y_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_950_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v___x_937_, v___y_951_);
lean_dec(v___y_951_);
lean_dec(v___x_937_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_l_928_);
lean_ctor_set(v___x_902_, 0, v___x_952_);
v___x_954_ = v___x_902_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_l_928_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = lean_nat_add(v___x_907_, v_size_930_);
if (lean_obj_tag(v_r_929_) == 0)
{
lean_object* v_size_956_; 
v_size_956_ = lean_ctor_get(v_r_929_, 0);
lean_inc(v_size_956_);
v___y_940_ = v___x_954_;
v___y_941_ = v___x_955_;
v___y_942_ = v_size_956_;
goto v___jp_939_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___y_940_ = v___x_954_;
v___y_941_ = v___x_955_;
v___y_942_ = v___x_957_;
goto v___jp_939_;
}
}
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_del_object(v___x_902_);
v___x_967_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_968_ = lean_nat_add(v___x_967_, v_size_909_);
lean_dec(v_size_909_);
v___x_969_ = lean_nat_add(v___x_967_, v_size_925_);
lean_dec(v___x_967_);
lean_inc_ref(v_l_899_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v_l_912_);
lean_ctor_set(v___x_923_, 3, v_l_899_);
lean_ctor_set(v___x_923_, 2, v_v_898_);
lean_ctor_set(v___x_923_, 1, v_k_897_);
lean_ctor_set(v___x_923_, 0, v___x_969_);
v___x_971_ = v___x_923_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_l_912_);
v___x_971_ = v_reuseFailAlloc_984_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_isSharedCheck_978_ = !lean_is_exclusive(v_l_899_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_979_ = lean_ctor_get(v_l_899_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_899_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_899_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_899_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_899_, 0);
lean_dec(v_unused_983_);
v___x_973_ = v_l_899_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_dec(v_l_899_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 4, v_r_913_);
lean_ctor_set(v___x_973_, 3, v___x_971_);
lean_ctor_set(v___x_973_, 2, v_v_911_);
lean_ctor_set(v___x_973_, 1, v_k_910_);
lean_ctor_set(v___x_973_, 0, v___x_968_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_r_913_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_991_; 
v_l_991_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_991_);
if (lean_obj_tag(v_l_991_) == 0)
{
lean_object* v_r_992_; lean_object* v_k_993_; lean_object* v_v_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1017_; 
v_r_992_ = lean_ctor_get(v_impl_906_, 4);
v_k_993_ = lean_ctor_get(v_impl_906_, 1);
v_v_994_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1019_);
v___x_996_ = v_impl_906_;
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_r_992_);
lean_inc(v_v_994_);
lean_inc(v_k_993_);
lean_dec(v_impl_906_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
v_k_998_ = lean_ctor_get(v_l_991_, 1);
v_v_999_ = lean_ctor_get(v_l_991_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_l_991_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1014_ = lean_ctor_get(v_l_991_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_l_991_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_l_991_, 0);
lean_dec(v_unused_1016_);
v___x_1001_ = v_l_991_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_v_999_);
lean_inc(v_k_998_);
lean_dec(v_l_991_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_992_, 2);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v_r_992_);
lean_ctor_set(v___x_1001_, 3, v_r_992_);
lean_ctor_set(v___x_1001_, 2, v_v_898_);
lean_ctor_set(v___x_1001_, 1, v_k_897_);
lean_ctor_set(v___x_1001_, 0, v___x_907_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_r_992_);
v___x_1005_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
lean_inc(v_r_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 3, v_r_992_);
lean_ctor_set(v___x_996_, 0, v___x_907_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_993_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_994_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_992_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1007_);
lean_ctor_set(v___x_902_, 3, v___x_1005_);
lean_ctor_set(v___x_902_, 2, v_v_999_);
lean_ctor_set(v___x_902_, 1, v_k_998_);
lean_ctor_set(v___x_902_, 0, v___x_1003_);
v___x_1009_ = v___x_902_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
else
{
lean_object* v_r_1020_; 
v_r_1020_ = lean_ctor_get(v_impl_906_, 4);
lean_inc(v_r_1020_);
if (lean_obj_tag(v_r_1020_) == 0)
{
lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1033_; 
v_k_1021_ = lean_ctor_get(v_impl_906_, 1);
v_v_1022_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1034_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1036_);
v___x_1024_ = v_impl_906_;
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
lean_dec(v_impl_906_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(3u);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_l_991_);
lean_ctor_set(v___x_1024_, 2, v_v_898_);
lean_ctor_set(v___x_1024_, 1, v_k_897_);
lean_ctor_set(v___x_1024_, 0, v___x_907_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_l_991_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_l_991_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_1020_);
lean_ctor_set(v___x_902_, 3, v___x_1028_);
lean_ctor_set(v___x_902_, 2, v_v_1022_);
lean_ctor_set(v___x_902_, 1, v_k_1021_);
lean_ctor_set(v___x_902_, 0, v___x_1026_);
v___x_1030_ = v___x_902_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_r_1020_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_unsigned_to_nat(2u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_impl_906_);
lean_ctor_set(v___x_902_, 3, v_r_1020_);
lean_ctor_set(v___x_902_, 0, v___x_1037_);
v___x_1039_ = v___x_902_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_1020_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_impl_906_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
else
{
lean_object* v___x_1042_; 
lean_dec(v_v_898_);
lean_dec(v_k_897_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v_v_894_);
lean_ctor_set(v___x_902_, 1, v_k_893_);
v___x_1042_ = v___x_902_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_896_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_893_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_894_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_r_900_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_impl_1044_; lean_object* v___x_1045_; 
lean_dec(v_size_896_);
v_impl_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_893_, v_v_894_, v_l_899_);
v___x_1045_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_900_) == 0)
{
lean_object* v_size_1046_; lean_object* v_size_1047_; lean_object* v_k_1048_; lean_object* v_v_1049_; lean_object* v_l_1050_; lean_object* v_r_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_size_1046_ = lean_ctor_get(v_r_900_, 0);
v_size_1047_ = lean_ctor_get(v_impl_1044_, 0);
v_k_1048_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1049_ = lean_ctor_get(v_impl_1044_, 2);
v_l_1050_ = lean_ctor_get(v_impl_1044_, 3);
v_r_1051_ = lean_ctor_get(v_impl_1044_, 4);
lean_inc(v_r_1051_);
v___x_1052_ = lean_unsigned_to_nat(3u);
v___x_1053_ = lean_nat_mul(v___x_1052_, v_size_1046_);
v___x_1054_ = lean_nat_dec_lt(v___x_1053_, v_size_1047_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec(v_r_1051_);
v___x_1055_ = lean_nat_add(v___x_1045_, v_size_1047_);
v___x_1056_ = lean_nat_add(v___x_1055_, v_size_1046_);
lean_dec(v___x_1055_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 3, v_impl_1044_);
lean_ctor_set(v___x_902_, 0, v___x_1056_);
v___x_1058_ = v___x_902_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_impl_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v_r_900_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1125_; 
lean_inc(v_l_1050_);
lean_inc(v_v_1049_);
lean_inc(v_k_1048_);
lean_inc(v_size_1047_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; 
v_unused_1126_ = lean_ctor_get(v_impl_1044_, 4);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_impl_1044_, 2);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_impl_1044_, 1);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1130_);
v___x_1061_ = v_impl_1044_;
v_isShared_1062_ = v_isSharedCheck_1125_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_impl_1044_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1125_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_size_1063_; lean_object* v_size_1064_; lean_object* v_k_1065_; lean_object* v_v_1066_; lean_object* v_l_1067_; lean_object* v_r_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_size_1063_ = lean_ctor_get(v_l_1050_, 0);
v_size_1064_ = lean_ctor_get(v_r_1051_, 0);
v_k_1065_ = lean_ctor_get(v_r_1051_, 1);
v_v_1066_ = lean_ctor_get(v_r_1051_, 2);
v_l_1067_ = lean_ctor_get(v_r_1051_, 3);
v_r_1068_ = lean_ctor_get(v_r_1051_, 4);
v___x_1069_ = lean_unsigned_to_nat(2u);
v___x_1070_ = lean_nat_mul(v___x_1069_, v_size_1063_);
v___x_1071_ = lean_nat_dec_lt(v_size_1064_, v___x_1070_);
lean_dec(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1100_; 
lean_inc(v_r_1068_);
lean_inc(v_l_1067_);
lean_inc(v_v_1066_);
lean_inc(v_k_1065_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_r_1051_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1101_ = lean_ctor_get(v_r_1051_, 4);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_r_1051_, 3);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_r_1051_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_1051_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_r_1051_, 0);
lean_dec(v_unused_1105_);
v___x_1073_ = v_r_1051_;
v_isShared_1074_ = v_isSharedCheck_1100_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_r_1051_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1100_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___x_1088_; lean_object* v___y_1090_; 
v___x_1075_ = lean_nat_add(v___x_1045_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1076_ = lean_nat_add(v___x_1075_, v_size_1046_);
lean_dec(v___x_1075_);
v___x_1088_ = lean_nat_add(v___x_1045_, v_size_1063_);
if (lean_obj_tag(v_l_1067_) == 0)
{
lean_object* v_size_1098_; 
v_size_1098_ = lean_ctor_get(v_l_1067_, 0);
lean_inc(v_size_1098_);
v___y_1090_ = v_size_1098_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___y_1090_ = v___x_1099_;
goto v___jp_1089_;
}
v___jp_1077_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_nat_add(v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v_r_900_);
lean_ctor_set(v___x_1073_, 3, v_r_1068_);
lean_ctor_set(v___x_1073_, 2, v_v_898_);
lean_ctor_set(v___x_1073_, 1, v_k_897_);
lean_ctor_set(v___x_1073_, 0, v___x_1081_);
v___x_1083_ = v___x_1073_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_r_1068_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_r_900_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v___x_1083_);
lean_ctor_set(v___x_1061_, 3, v___y_1078_);
lean_ctor_set(v___x_1061_, 2, v_v_1066_);
lean_ctor_set(v___x_1061_, 1, v_k_1065_);
lean_ctor_set(v___x_1061_, 0, v___x_1076_);
v___x_1085_ = v___x_1061_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_1065_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_1066_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___y_1078_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_nat_add(v___x_1088_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec(v___x_1088_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_l_1067_);
lean_ctor_set(v___x_902_, 3, v_l_1050_);
lean_ctor_set(v___x_902_, 2, v_v_1049_);
lean_ctor_set(v___x_902_, 1, v_k_1048_);
lean_ctor_set(v___x_902_, 0, v___x_1091_);
v___x_1093_ = v___x_902_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_l_1067_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_nat_add(v___x_1045_, v_size_1046_);
if (lean_obj_tag(v_r_1068_) == 0)
{
lean_object* v_size_1095_; 
v_size_1095_ = lean_ctor_get(v_r_1068_, 0);
lean_inc(v_size_1095_);
v___y_1078_ = v___x_1093_;
v___y_1079_ = v___x_1094_;
v___y_1080_ = v_size_1095_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___y_1078_ = v___x_1093_;
v___y_1079_ = v___x_1094_;
v___y_1080_ = v___x_1096_;
goto v___jp_1077_;
}
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_del_object(v___x_902_);
v___x_1106_ = lean_nat_add(v___x_1045_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_size_1046_);
lean_dec(v___x_1106_);
v___x_1108_ = lean_nat_add(v___x_1045_, v_size_1046_);
v___x_1109_ = lean_nat_add(v___x_1108_, v_size_1064_);
lean_dec(v___x_1108_);
lean_inc_ref(v_r_900_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v_r_900_);
lean_ctor_set(v___x_1061_, 3, v_r_1051_);
lean_ctor_set(v___x_1061_, 2, v_v_898_);
lean_ctor_set(v___x_1061_, 1, v_k_897_);
lean_ctor_set(v___x_1061_, 0, v___x_1109_);
v___x_1111_ = v___x_1061_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_r_1051_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_r_900_);
v___x_1111_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_isSharedCheck_1118_ = !lean_is_exclusive(v_r_900_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1119_ = lean_ctor_get(v_r_900_, 4);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_900_, 3);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_r_900_, 2);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_r_900_, 1);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_r_900_, 0);
lean_dec(v_unused_1123_);
v___x_1113_ = v_r_900_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v_r_900_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 4, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v_l_1050_);
lean_ctor_set(v___x_1113_, 2, v_v_1049_);
lean_ctor_set(v___x_1113_, 1, v_k_1048_);
lean_ctor_set(v___x_1113_, 0, v___x_1107_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___x_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1131_; 
v_l_1131_ = lean_ctor_get(v_impl_1044_, 3);
if (lean_obj_tag(v_l_1131_) == 0)
{
lean_object* v_r_1132_; lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1145_; 
lean_inc_ref(v_l_1131_);
v_r_1132_ = lean_ctor_get(v_impl_1044_, 4);
v_k_1133_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1134_ = lean_ctor_get(v_impl_1044_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1146_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1147_);
v___x_1136_ = v_impl_1044_;
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_r_1132_);
lean_inc(v_v_1134_);
lean_inc(v_k_1133_);
lean_dec(v_impl_1044_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1132_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 3, v_r_1132_);
lean_ctor_set(v___x_1136_, 2, v_v_898_);
lean_ctor_set(v___x_1136_, 1, v_k_897_);
lean_ctor_set(v___x_1136_, 0, v___x_1045_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_r_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1132_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1140_);
lean_ctor_set(v___x_902_, 3, v_l_1131_);
lean_ctor_set(v___x_902_, 2, v_v_1134_);
lean_ctor_set(v___x_902_, 1, v_k_1133_);
lean_ctor_set(v___x_902_, 0, v___x_1138_);
v___x_1142_ = v___x_902_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_r_1148_; 
v_r_1148_ = lean_ctor_get(v_impl_1044_, 4);
lean_inc(v_r_1148_);
if (lean_obj_tag(v_r_1148_) == 0)
{
lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1173_; 
lean_inc(v_l_1131_);
v_k_1149_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1150_ = lean_ctor_get(v_impl_1044_, 2);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1174_ = lean_ctor_get(v_impl_1044_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1176_);
v___x_1152_ = v_impl_1044_;
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
lean_dec(v_impl_1044_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_k_1154_; lean_object* v_v_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1169_; 
v_k_1154_ = lean_ctor_get(v_r_1148_, 1);
v_v_1155_ = lean_ctor_get(v_r_1148_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_r_1148_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1170_ = lean_ctor_get(v_r_1148_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_1148_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_r_1148_, 0);
lean_dec(v_unused_1172_);
v___x_1157_ = v_r_1148_;
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_v_1155_);
lean_inc(v_k_1154_);
lean_dec(v_r_1148_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(3u);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 4, v_l_1131_);
lean_ctor_set(v___x_1157_, 3, v_l_1131_);
lean_ctor_set(v___x_1157_, 2, v_v_1150_);
lean_ctor_set(v___x_1157_, 1, v_k_1149_);
lean_ctor_set(v___x_1157_, 0, v___x_1045_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_l_1131_);
v___x_1161_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 4, v_l_1131_);
lean_ctor_set(v___x_1152_, 2, v_v_898_);
lean_ctor_set(v___x_1152_, 1, v_k_897_);
lean_ctor_set(v___x_1152_, 0, v___x_1045_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_l_1131_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1163_);
lean_ctor_set(v___x_902_, 3, v___x_1161_);
lean_ctor_set(v___x_902_, 2, v_v_1155_);
lean_ctor_set(v___x_902_, 1, v_k_1154_);
lean_ctor_set(v___x_902_, 0, v___x_1159_);
v___x_1165_ = v___x_902_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(2u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_1148_);
lean_ctor_set(v___x_902_, 3, v_impl_1044_);
lean_ctor_set(v___x_902_, 0, v___x_1177_);
v___x_1179_ = v___x_902_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_impl_1044_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_r_1148_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_k_893_);
lean_ctor_set(v___x_1183_, 2, v_v_894_);
lean_ctor_set(v___x_1183_, 3, v_t_895_);
lean_ctor_set(v___x_1183_, 4, v_t_895_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1184_, lean_object* v_b_1185_){
_start:
{
if (lean_obj_tag(v_as_x27_1184_) == 0)
{
return v_b_1185_;
}
else
{
lean_object* v_head_1186_; lean_object* v_tail_1187_; lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v_r_1190_; 
v_head_1186_ = lean_ctor_get(v_as_x27_1184_, 0);
v_tail_1187_ = lean_ctor_get(v_as_x27_1184_, 1);
v_fst_1188_ = lean_ctor_get(v_head_1186_, 0);
v_snd_1189_ = lean_ctor_get(v_head_1186_, 1);
lean_inc(v_snd_1189_);
lean_inc(v_fst_1188_);
v_r_1190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1188_, v_snd_1189_, v_b_1185_);
v_as_x27_1184_ = v_tail_1187_;
v_b_1185_ = v_r_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1192_, lean_object* v_b_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1192_, v_b_1193_);
lean_dec(v_as_x27_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1203_, lean_object* v_expr_1204_, lean_object* v_lctx_1205_, lean_object* v_location_x3f_1206_, lean_object* v_docString_x3f_1207_, lean_object* v_mkDocString_x3f_1208_, uint8_t v_explicit_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___y_1217_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_fmt_1203_);
v___x_1212_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1213_ = lean_box(0);
v___x_1214_ = 0;
v___x_1215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1215_, 0, v___x_1212_);
lean_ctor_set(v___x_1215_, 1, v_lctx_1205_);
lean_ctor_set(v___x_1215_, 2, v___x_1213_);
lean_ctor_set(v___x_1215_, 3, v_expr_1204_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*4, v___x_1214_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*4 + 1, v___x_1214_);
if (lean_obj_tag(v_mkDocString_x3f_1208_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1207_) == 0)
{
v___y_1217_ = v_mkDocString_x3f_1208_;
goto v___jp_1216_;
}
else
{
lean_object* v_val_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_val_1227_ = lean_ctor_get(v_docString_x3f_1207_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_docString_x3f_1207_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_docString_x3f_1207_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_val_1227_);
lean_dec(v_docString_x3f_1207_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___f_1231_; lean_object* v___x_1233_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1231_, 0, v_val_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___f_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___f_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v___y_1217_ = v___x_1233_;
goto v___jp_1216_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1207_);
v___y_1217_ = v_mkDocString_x3f_1208_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_r_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1218_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1218_, 0, v___x_1215_);
lean_ctor_set(v___x_1218_, 1, v_location_x3f_1206_);
lean_ctor_set(v___x_1218_, 2, v___y_1217_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*3, v_explicit_1209_);
v___x_1219_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1210_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v_r_1223_ = lean_box(1);
v___x_1224_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1222_, v_r_1223_);
lean_dec_ref_known(v___x_1222_, 2);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1211_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1236_, lean_object* v_expr_1237_, lean_object* v_lctx_1238_, lean_object* v_location_x3f_1239_, lean_object* v_docString_x3f_1240_, lean_object* v_mkDocString_x3f_1241_, lean_object* v_explicit_1242_){
_start:
{
uint8_t v_explicit_boxed_1243_; lean_object* v_res_1244_; 
v_explicit_boxed_1243_ = lean_unbox(v_explicit_1242_);
v_res_1244_ = l_Lean_MessageData_withExprHover(v_fmt_1236_, v_expr_1237_, v_lctx_1238_, v_location_x3f_1239_, v_docString_x3f_1240_, v_mkDocString_x3f_1241_, v_explicit_boxed_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1245_, lean_object* v_k_1246_, lean_object* v_v_1247_, lean_object* v_t_1248_, lean_object* v_hl_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1246_, v_v_1247_, v_t_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1251_, lean_object* v_as_x27_1252_, lean_object* v_b_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1252_, v_b_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1256_, lean_object* v_as_x27_1257_, lean_object* v_b_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1256_, v_as_x27_1257_, v_b_1258_, v_a_1259_);
lean_dec(v_as_x27_1257_);
lean_dec(v_as_1256_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1261_, lean_object* v_expr_1262_, lean_object* v_location_x3f_1263_, lean_object* v_docString_x3f_1264_, lean_object* v_mkDocString_x3f_1265_, uint8_t v_explicit_1266_, lean_object* v_toPure_1267_, lean_object* v_lctx_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_MessageData_withExprHover(v_fmt_1261_, v_expr_1262_, v_lctx_1268_, v_location_x3f_1263_, v_docString_x3f_1264_, v_mkDocString_x3f_1265_, v_explicit_1266_);
v___x_1270_ = lean_apply_2(v_toPure_1267_, lean_box(0), v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1271_, lean_object* v_expr_1272_, lean_object* v_location_x3f_1273_, lean_object* v_docString_x3f_1274_, lean_object* v_mkDocString_x3f_1275_, lean_object* v_explicit_1276_, lean_object* v_toPure_1277_, lean_object* v_lctx_1278_){
_start:
{
uint8_t v_explicit_boxed_1279_; lean_object* v_res_1280_; 
v_explicit_boxed_1279_ = lean_unbox(v_explicit_1276_);
v_res_1280_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1271_, v_expr_1272_, v_location_x3f_1273_, v_docString_x3f_1274_, v_mkDocString_x3f_1275_, v_explicit_boxed_1279_, v_toPure_1277_, v_lctx_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_fmt_1283_, lean_object* v_expr_1284_, lean_object* v_lctx_x3f_1285_, lean_object* v_location_x3f_1286_, lean_object* v_docString_x3f_1287_, lean_object* v_mkDocString_x3f_1288_, uint8_t v_explicit_1289_){
_start:
{
lean_object* v_toApplicative_1290_; lean_object* v_toBind_1291_; lean_object* v_toPure_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; 
v_toApplicative_1290_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1290_);
v_toBind_1291_ = lean_ctor_get(v_inst_1281_, 1);
lean_inc(v_toBind_1291_);
lean_dec_ref(v_inst_1281_);
v_toPure_1292_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_inc_n(v_toPure_1292_, 2);
lean_dec_ref(v_toApplicative_1290_);
v___x_1293_ = lean_box(v_explicit_1289_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1294_, 0, v_fmt_1283_);
lean_closure_set(v___f_1294_, 1, v_expr_1284_);
lean_closure_set(v___f_1294_, 2, v_location_x3f_1286_);
lean_closure_set(v___f_1294_, 3, v_docString_x3f_1287_);
lean_closure_set(v___f_1294_, 4, v_mkDocString_x3f_1288_);
lean_closure_set(v___f_1294_, 5, v___x_1293_);
lean_closure_set(v___f_1294_, 6, v_toPure_1292_);
if (lean_obj_tag(v_lctx_x3f_1285_) == 0)
{
lean_object* v___x_1295_; 
lean_dec(v_toPure_1292_);
v___x_1295_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v_inst_1282_, v___f_1294_);
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_inst_1282_);
v_val_1296_ = lean_ctor_get(v_lctx_x3f_1285_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_lctx_x3f_1285_, 1);
v___x_1297_ = lean_apply_2(v_toPure_1292_, lean_box(0), v_val_1296_);
v___x_1298_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v___x_1297_, v___f_1294_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_fmt_1301_, lean_object* v_expr_1302_, lean_object* v_lctx_x3f_1303_, lean_object* v_location_x3f_1304_, lean_object* v_docString_x3f_1305_, lean_object* v_mkDocString_x3f_1306_, lean_object* v_explicit_1307_){
_start:
{
uint8_t v_explicit_boxed_1308_; lean_object* v_res_1309_; 
v_explicit_boxed_1308_ = lean_unbox(v_explicit_1307_);
v_res_1309_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1299_, v_inst_1300_, v_fmt_1301_, v_expr_1302_, v_lctx_x3f_1303_, v_location_x3f_1304_, v_docString_x3f_1305_, v_mkDocString_x3f_1306_, v_explicit_boxed_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_fmt_1313_, lean_object* v_expr_1314_, lean_object* v_lctx_x3f_1315_, lean_object* v_location_x3f_1316_, lean_object* v_docString_x3f_1317_, lean_object* v_mkDocString_x3f_1318_, uint8_t v_explicit_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1311_, v_inst_1312_, v_fmt_1313_, v_expr_1314_, v_lctx_x3f_1315_, v_location_x3f_1316_, v_docString_x3f_1317_, v_mkDocString_x3f_1318_, v_explicit_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_fmt_1324_, lean_object* v_expr_1325_, lean_object* v_lctx_x3f_1326_, lean_object* v_location_x3f_1327_, lean_object* v_docString_x3f_1328_, lean_object* v_mkDocString_x3f_1329_, lean_object* v_explicit_1330_){
_start:
{
uint8_t v_explicit_boxed_1331_; lean_object* v_res_1332_; 
v_explicit_boxed_1331_ = lean_unbox(v_explicit_1330_);
v_res_1332_ = l_Lean_MessageData_withExprHoverM(v_m_1321_, v_inst_1322_, v_inst_1323_, v_fmt_1324_, v_expr_1325_, v_lctx_x3f_1326_, v_location_x3f_1327_, v_docString_x3f_1328_, v_mkDocString_x3f_1329_, v_explicit_boxed_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1333_, lean_object* v_display_1334_, lean_object* v_toPure_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_____do__lift_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1338_, v_userName_1333_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_inst_1337_);
lean_dec_ref(v_inst_1336_);
v___x_1340_ = l_Lean_MessageData_ofName(v_display_1334_);
v___x_1341_ = lean_apply_2(v_toPure_1335_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_toPure_1335_);
v_val_1342_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1344_ = v___x_1339_;
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v___x_1339_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = 1;
v___x_1347_ = l_Lean_Name_toString(v_display_1334_, v___x_1346_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 3);
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1350_ = l_Lean_LocalDecl_fvarId(v_val_1342_);
lean_dec(v_val_1342_);
v___x_1351_ = l_Lean_Expr_fvar___override(v___x_1350_);
v___x_1352_ = lean_box(0);
v___x_1353_ = 0;
v___x_1354_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1336_, v_inst_1337_, v___x_1349_, v___x_1351_, v___x_1352_, v___x_1352_, v___x_1352_, v___x_1352_, v___x_1353_);
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1357_, lean_object* v_display_1358_, lean_object* v_toPure_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_____do__lift_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1357_, v_display_1358_, v_toPure_1359_, v_inst_1360_, v_inst_1361_, v_____do__lift_1362_);
lean_dec_ref(v_____do__lift_1362_);
lean_dec(v_userName_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_userName_1366_){
_start:
{
lean_object* v_toApplicative_1367_; lean_object* v_toBind_1368_; lean_object* v_toPure_1369_; lean_object* v_display_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; 
v_toApplicative_1367_ = lean_ctor_get(v_inst_1364_, 0);
v_toBind_1368_ = lean_ctor_get(v_inst_1364_, 1);
lean_inc(v_toBind_1368_);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1367_, 1);
lean_inc(v_toPure_1369_);
lean_inc(v_userName_1366_);
v_display_1370_ = l_Lean_Name_simpMacroScopes(v_userName_1366_);
lean_inc(v_inst_1365_);
v___f_1371_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1371_, 0, v_userName_1366_);
lean_closure_set(v___f_1371_, 1, v_display_1370_);
lean_closure_set(v___f_1371_, 2, v_toPure_1369_);
lean_closure_set(v___f_1371_, 3, v_inst_1364_);
lean_closure_set(v___f_1371_, 4, v_inst_1365_);
v___x_1372_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v_inst_1365_, v___f_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_userName_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1374_, v_inst_1375_, v_userName_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1378_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
lean_ctor_set(v___x_1383_, 3, v___x_1382_);
lean_ctor_set(v___x_1383_, 4, v___x_1381_);
lean_ctor_set(v___x_1383_, 5, v___x_1381_);
lean_ctor_set(v___x_1383_, 6, v___x_1381_);
lean_ctor_set(v___x_1383_, 7, v___x_1381_);
lean_ctor_set(v___x_1383_, 8, v___x_1381_);
lean_ctor_set(v___x_1383_, 9, v___x_1381_);
lean_ctor_set(v___x_1383_, 10, v___x_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1384_, lean_object* v_a_1385_){
_start:
{
switch(lean_obj_tag(v_a_1385_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1384_) == 0)
{
lean_object* v_hasSyntheticSorry_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_hasSyntheticSorry_1386_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_hasSyntheticSorry_1386_);
lean_dec_ref_known(v_a_1385_, 2);
v___x_1387_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1388_ = lean_apply_1(v_hasSyntheticSorry_1386_, v___x_1387_);
v___x_1389_ = lean_unbox(v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v_hasSyntheticSorry_1390_; lean_object* v_val_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_hasSyntheticSorry_1390_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_hasSyntheticSorry_1390_);
lean_dec_ref_known(v_a_1385_, 2);
v_val_1391_ = lean_ctor_get(v_mctx_x3f_1384_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v_mctx_x3f_1384_, 1);
v___x_1392_ = lean_apply_1(v_hasSyntheticSorry_1390_, v_val_1391_);
v___x_1393_ = lean_unbox(v___x_1392_);
return v___x_1393_;
}
}
case 3:
{
lean_object* v_a_1394_; lean_object* v_a_1395_; lean_object* v_mctx_1396_; lean_object* v___x_1397_; 
lean_dec(v_mctx_x3f_1384_);
v_a_1394_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1394_);
v_a_1395_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1395_);
lean_dec_ref_known(v_a_1385_, 2);
v_mctx_1396_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_mctx_1396_);
lean_dec_ref(v_a_1394_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_mctx_1396_);
v_mctx_x3f_1384_ = v___x_1397_;
v_a_1385_ = v_a_1395_;
goto _start;
}
case 4:
{
lean_object* v_a_1399_; 
v_a_1399_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1399_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1399_;
goto _start;
}
case 5:
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1401_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1401_;
goto _start;
}
case 6:
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1403_);
lean_dec_ref_known(v_a_1385_, 1);
v_a_1385_ = v_a_1403_;
goto _start;
}
case 7:
{
lean_object* v_a_1405_; lean_object* v_a_1406_; uint8_t v___x_1407_; 
v_a_1405_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1405_);
v_a_1406_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1406_);
lean_dec_ref_known(v_a_1385_, 2);
lean_inc(v_mctx_x3f_1384_);
v___x_1407_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1384_, v_a_1405_);
if (v___x_1407_ == 0)
{
v_a_1385_ = v_a_1406_;
goto _start;
}
else
{
lean_dec_ref(v_a_1406_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1407_;
}
}
case 8:
{
lean_object* v_a_1409_; 
v_a_1409_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1409_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1409_;
goto _start;
}
case 11:
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1411_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1411_;
goto _start;
}
case 9:
{
lean_object* v_msg_1413_; lean_object* v_children_1414_; uint8_t v___x_1415_; 
v_msg_1413_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_msg_1413_);
v_children_1414_ = lean_ctor_get(v_a_1385_, 2);
lean_inc_ref(v_children_1414_);
lean_dec_ref_known(v_a_1385_, 3);
lean_inc(v_mctx_x3f_1384_);
v___x_1415_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1384_, v_msg_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_children_1414_);
v___x_1418_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1418_;
}
else
{
if (v___x_1418_ == 0)
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1417_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1384_, v_children_1414_, v___x_1419_, v___x_1420_);
lean_dec_ref(v_children_1414_);
return v___x_1421_;
}
}
}
else
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1415_;
}
}
default: 
{
uint8_t v___x_1422_; 
lean_dec_ref(v_a_1385_);
lean_dec(v_mctx_x3f_1384_);
v___x_1422_ = 0;
return v___x_1422_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1423_, lean_object* v_as_1424_, size_t v_i_1425_, size_t v_stop_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_eq(v_i_1425_, v_stop_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_array_uget_borrowed(v_as_1424_, v_i_1425_);
lean_inc(v___x_1428_);
lean_inc(v_mctx_x3f_1423_);
v___x_1429_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1423_, v___x_1428_);
if (v___x_1429_ == 0)
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1425_, v___x_1430_);
v_i_1425_ = v___x_1431_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1423_);
return v___x_1429_;
}
}
else
{
uint8_t v___x_1433_; 
lean_dec(v_mctx_x3f_1423_);
v___x_1433_ = 0;
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1434_, lean_object* v_as_1435_, lean_object* v_i_1436_, lean_object* v_stop_1437_){
_start:
{
size_t v_i_boxed_1438_; size_t v_stop_boxed_1439_; uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_stop_boxed_1439_ = lean_unbox_usize(v_stop_1437_);
lean_dec(v_stop_1437_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1434_, v_as_1435_, v_i_boxed_1438_, v_stop_boxed_1439_);
lean_dec_ref(v_as_1435_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1442_, lean_object* v_a_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1442_, v_a_1443_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_box(0);
v___x_1448_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1447_, v_msg_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1449_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object* v_name_1452_, lean_object* v_decl_1453_, lean_object* v_ref_1454_){
_start:
{
lean_object* v_defValue_1456_; lean_object* v_descr_1457_; lean_object* v_deprecation_x3f_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_defValue_1456_ = lean_ctor_get(v_decl_1453_, 0);
v_descr_1457_ = lean_ctor_get(v_decl_1453_, 1);
v_deprecation_x3f_1458_ = lean_ctor_get(v_decl_1453_, 2);
lean_inc(v_defValue_1456_);
v___x_1459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_defValue_1456_);
lean_inc(v_deprecation_x3f_1458_);
lean_inc_ref(v_descr_1457_);
lean_inc_n(v_name_1452_, 2);
v___x_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1460_, 0, v_name_1452_);
lean_ctor_set(v___x_1460_, 1, v_ref_1454_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
lean_ctor_set(v___x_1460_, 3, v_descr_1457_);
lean_ctor_set(v___x_1460_, 4, v_deprecation_x3f_1458_);
v___x_1461_ = lean_register_option(v_name_1452_, v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1470_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_inc(v_defValue_1456_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_name_1452_);
lean_ctor_set(v___x_1465_, 1, v_defValue_1456_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_name_1452_);
v_a_1471_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1461_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1461_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1479_, lean_object* v_decl_1480_, lean_object* v_ref_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1479_, v_decl_1480_, v_ref_1481_);
lean_dec_ref(v_decl_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1498_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1499_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1500_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v___x_1497_, v___x_1498_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_nat_to_int(v_a_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = l_instMonadBaseIO;
v___x_1507_ = l_instInhabitedOfMonad___redArg(v___x_1506_, v___x_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1610__overap_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1610__overap_1511_ = lean_panic_fn_borrowed(v___x_1510_, v_msg_1508_);
v___x_1512_ = lean_apply_1(v___x_1610__overap_1511_, lean_box(0));
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_dec(v_x_1516_);
return v_x_1517_;
}
else
{
lean_object* v_head_1519_; lean_object* v_tail_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
v_head_1519_ = lean_ctor_get(v_x_1518_, 0);
v_tail_1520_ = lean_ctor_get(v_x_1518_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_x_1518_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1522_ = v_x_1518_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_tail_1520_);
lean_inc(v_head_1519_);
lean_dec(v_x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
lean_inc(v_x_1516_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 5);
lean_ctor_set(v___x_1522_, 1, v_x_1516_);
lean_ctor_set(v___x_1522_, 0, v_x_1517_);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_x_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_x_1516_);
v___x_1525_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_head_1519_);
v_x_1517_ = v___x_1526_;
v_x_1518_ = v_tail_1520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
if (lean_obj_tag(v_x_1530_) == 0)
{
lean_object* v___x_1532_; 
lean_dec(v_x_1531_);
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
else
{
lean_object* v_tail_1533_; 
v_tail_1533_ = lean_ctor_get(v_x_1530_, 1);
if (lean_obj_tag(v_tail_1533_) == 0)
{
lean_object* v_head_1534_; 
lean_dec(v_x_1531_);
v_head_1534_ = lean_ctor_get(v_x_1530_, 0);
lean_inc(v_head_1534_);
lean_dec_ref_known(v_x_1530_, 2);
return v_head_1534_;
}
else
{
lean_object* v_head_1535_; lean_object* v___x_1536_; 
lean_inc(v_tail_1533_);
v_head_1535_ = lean_ctor_get(v_x_1530_, 0);
lean_inc(v_head_1535_);
lean_dec_ref_known(v_x_1530_, 2);
v___x_1536_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1531_, v_head_1535_, v_tail_1533_);
return v___x_1536_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__7(void){
_start:
{
lean_object* v___x_1548_; double v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_float_of_nat(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_){
_start:
{
switch(lean_obj_tag(v_x_1558_))
{
case 0:
{
lean_object* v_a_1560_; lean_object* v_fmt_1561_; 
lean_dec(v_x_1557_);
lean_dec_ref(v_x_1556_);
v_a_1560_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_a_1560_);
lean_dec_ref_known(v_x_1558_, 1);
v_fmt_1561_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_fmt_1561_);
lean_dec_ref(v_a_1560_);
return v_fmt_1561_;
}
case 1:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v_x_1556_);
v_a_1562_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v_x_1558_, 1);
v___x_1563_ = l_Lean_formatRawGoal(v_a_1562_);
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v_val_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_a_1564_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v_x_1558_, 1);
v_val_1565_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v_x_1557_, 1);
v___x_1566_ = l_Lean_MessageData_mkPPContext(v_x_1556_, v_val_1565_);
lean_dec(v_val_1565_);
lean_dec_ref(v_x_1556_);
v___x_1567_ = l_Lean_ppGoal(v___x_1566_, v_a_1564_);
return v___x_1567_;
}
}
case 3:
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1570_; 
lean_dec(v_x_1557_);
v_a_1568_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_a_1568_);
v_a_1569_ = lean_ctor_get(v_x_1558_, 1);
lean_inc_ref(v_a_1569_);
lean_dec_ref_known(v_x_1558_, 2);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1568_);
v_x_1557_ = v___x_1570_;
v_x_1558_ = v_a_1569_;
goto _start;
}
case 4:
{
lean_object* v_a_1572_; lean_object* v_a_1573_; 
lean_dec_ref(v_x_1556_);
v_a_1572_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_a_1572_);
v_a_1573_ = lean_ctor_get(v_x_1558_, 1);
lean_inc_ref(v_a_1573_);
lean_dec_ref_known(v_x_1558_, 2);
v_x_1556_ = v_a_1572_;
v_x_1558_ = v_a_1573_;
goto _start;
}
case 5:
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v_a_1575_ = lean_ctor_get(v_x_1558_, 0);
v_a_1576_ = lean_ctor_get(v_x_1558_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v_x_1558_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v_x_1558_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = l_Lean_MessageData_formatAux(v_x_1556_, v_x_1557_, v_a_1576_);
v___x_1581_ = lean_nat_to_int(v_a_1575_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 4);
lean_ctor_set(v___x_1578_, 1, v___x_1580_);
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1580_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
case 6:
{
lean_object* v_a_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; 
v_a_1586_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_a_1586_);
lean_dec_ref_known(v_x_1558_, 1);
v___x_1587_ = l_Lean_MessageData_formatAux(v_x_1556_, v_x_1557_, v_a_1586_);
v___x_1588_ = 0;
v___x_1589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*1, v___x_1588_);
return v___x_1589_;
}
case 7:
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1600_; 
v_a_1590_ = lean_ctor_get(v_x_1558_, 0);
v_a_1591_ = lean_ctor_get(v_x_1558_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1593_ = v_x_1558_;
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_inc(v_a_1590_);
lean_dec(v_x_1558_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_inc(v_x_1557_);
lean_inc_ref(v_x_1556_);
v___x_1595_ = l_Lean_MessageData_formatAux(v_x_1556_, v_x_1557_, v_a_1590_);
v___x_1596_ = l_Lean_MessageData_formatAux(v_x_1556_, v_x_1557_, v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 5);
lean_ctor_set(v___x_1593_, 1, v___x_1596_);
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
case 9:
{
lean_object* v_data_1601_; lean_object* v_msg_1602_; lean_object* v_children_1603_; size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v_cls_1620_; lean_object* v_result_x3f_1621_; double v_startTime_1622_; double v_stopTime_1623_; lean_object* v_msg_1625_; uint8_t v___x_1640_; 
v_data_1601_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_data_1601_);
v_msg_1602_ = lean_ctor_get(v_x_1558_, 1);
lean_inc_ref(v_msg_1602_);
v_children_1603_ = lean_ctor_get(v_x_1558_, 2);
lean_inc_ref(v_children_1603_);
lean_dec_ref_known(v_x_1558_, 3);
v_sz_1604_ = lean_array_size(v_children_1603_);
v___x_1605_ = ((size_t)0ULL);
lean_inc(v_x_1557_);
lean_inc_ref(v_x_1556_);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1556_, v_x_1557_, v_sz_1604_, v___x_1605_, v_children_1603_);
v_cls_1620_ = lean_ctor_get(v_data_1601_, 0);
lean_inc(v_cls_1620_);
v_result_x3f_1621_ = lean_ctor_get(v_data_1601_, 1);
lean_inc(v_result_x3f_1621_);
v_startTime_1622_ = lean_ctor_get_float(v_data_1601_, sizeof(void*)*3);
v_stopTime_1623_ = lean_ctor_get_float(v_data_1601_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1601_);
v___x_1640_ = l_Lean_Name_isAnonymous(v_cls_1620_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; double v___x_1648_; uint8_t v___x_1649_; 
v___x_1641_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1642_ = 1;
v___x_1643_ = l_Lean_Name_toString(v_cls_1620_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1641_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__7, &l_Lean_MessageData_formatAux___closed__7_once, _init_l_Lean_MessageData_formatAux___closed__7);
v___x_1649_ = lean_float_beq(v_startTime_1622_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; double v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__9));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1647_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_float_sub(v_stopTime_1623_, v_startTime_1622_);
v___x_1653_ = lean_float_to_string(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1651_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1646_);
v_msg_1625_ = v___x_1656_;
goto v___jp_1624_;
}
else
{
v_msg_1625_ = v___x_1647_;
goto v___jp_1624_;
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_result_x3f_1621_);
lean_dec(v_cls_1620_);
lean_dec_ref(v_msg_1602_);
lean_dec(v_x_1557_);
lean_dec_ref(v_x_1556_);
v___x_1657_ = lean_array_to_list(v___x_1606_);
v___x_1658_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1659_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1657_, v___x_1658_);
return v___x_1659_;
}
v___jp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1610_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___y_1609_);
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1611_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_array_to_list(v___x_1606_);
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1618_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1616_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1612_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
v___jp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_MessageData_formatAux(v_x_1556_, v_x_1557_, v_msg_1602_);
if (lean_obj_tag(v_result_x3f_1621_) == 0)
{
v___y_1608_ = v_msg_1625_;
v___y_1609_ = v___x_1626_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1639_; 
v_val_1627_ = lean_ctor_get(v_result_x3f_1621_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_result_x3f_1621_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1629_ = v_result_x3f_1621_;
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_val_1627_);
lean_dec(v_result_x3f_1621_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = lean_unbox(v_val_1627_);
lean_dec(v_val_1627_);
v___x_1632_ = l_Lean_TraceResult_toEmoji(v___x_1631_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 3);
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1634_ = v___x_1629_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1626_);
v___y_1608_ = v_msg_1625_;
v___y_1609_ = v___x_1637_;
goto v___jp_1607_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1660_; lean_object* v___x_1661_; lean_object* v___y_1663_; 
v_f_1660_ = lean_ctor_get(v_x_1558_, 0);
lean_inc_ref(v_f_1660_);
lean_dec_ref_known(v_x_1558_, 2);
v___x_1661_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_box(0);
v___y_1663_ = v___x_1679_;
goto v___jp_1662_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_val_1680_ = lean_ctor_get(v_x_1557_, 0);
v___x_1681_ = l_Lean_MessageData_mkPPContext(v_x_1556_, v_val_1680_);
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
v___y_1663_ = v___x_1682_;
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_apply_2(v_f_1660_, v___y_1663_, lean_box(0));
v___x_1665_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1664_, v___x_1661_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_val_1666_; 
lean_dec(v___x_1664_);
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v_x_1558_ = v_val_1666_;
goto _start;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1665_);
lean_dec(v_x_1557_);
lean_dec_ref(v_x_1556_);
v___x_1668_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1669_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1670_ = lean_unsigned_to_nat(409u);
v___x_1671_ = lean_unsigned_to_nat(8u);
v___x_1672_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1673_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1664_);
lean_dec(v___x_1664_);
v___x_1674_ = 1;
v___x_1675_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_string_append(v___x_1672_, v___x_1675_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = l_mkPanicMessageWithDecl(v___x_1668_, v___x_1669_, v___x_1670_, v___x_1671_, v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1677_);
return v___x_1678_;
}
}
}
default: 
{
lean_object* v_a_1683_; 
v_a_1683_ = lean_ctor_get(v_x_1558_, 1);
lean_inc_ref(v_a_1683_);
lean_dec_ref(v_x_1558_);
v_x_1558_ = v_a_1683_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1685_, lean_object* v_x_1686_, size_t v_sz_1687_, size_t v_i_1688_, lean_object* v_bs_1689_){
_start:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_usize_dec_lt(v_i_1688_, v_sz_1687_);
if (v___x_1691_ == 0)
{
lean_dec(v_x_1686_);
lean_dec_ref(v_x_1685_);
return v_bs_1689_;
}
else
{
lean_object* v_v_1692_; lean_object* v___x_1693_; lean_object* v_bs_x27_1694_; lean_object* v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v_v_1692_ = lean_array_uget(v_bs_1689_, v_i_1688_);
v___x_1693_ = lean_unsigned_to_nat(0u);
v_bs_x27_1694_ = lean_array_uset(v_bs_1689_, v_i_1688_, v___x_1693_);
lean_inc(v_x_1686_);
lean_inc_ref(v_x_1685_);
v___x_1695_ = l_Lean_MessageData_formatAux(v_x_1685_, v_x_1686_, v_v_1692_);
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_add(v_i_1688_, v___x_1696_);
v___x_1698_ = lean_array_uset(v_bs_x27_1694_, v_i_1688_, v___x_1695_);
v_i_1688_ = v___x_1697_;
v_bs_1689_ = v___x_1698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_bs_1704_, lean_object* v___y_1705_){
_start:
{
size_t v_sz_boxed_1706_; size_t v_i_boxed_1707_; lean_object* v_res_1708_; 
v_sz_boxed_1706_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1707_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1700_, v_x_1701_, v_sz_boxed_1706_, v_i_boxed_1707_, v_bs_1704_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_MessageData_formatAux(v_x_1709_, v_x_1710_, v_x_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1717_, lean_object* v_ctx_x3f_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1721_ = l_Lean_MessageData_formatAux(v___x_1720_, v_ctx_x3f_1718_, v_msgData_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1722_, lean_object* v_ctx_x3f_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_MessageData_format(v_msgData_1722_, v_ctx_x3f_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Lean_MessageData_format(v_msgData_1726_, v___x_1728_);
v___x_1730_ = l_Std_Format_defWidth;
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = l_Std_Format_pretty(v___x_1729_, v___x_1730_, v___x_1731_, v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_MessageData_toString(v_msgData_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1736_);
lean_ctor_set(v___x_1738_, 1, v_a_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_s_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_a_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1766_ = l_Lean_MessageData_ofFormat(v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1767_){
_start:
{
if (lean_obj_tag(v_o_1767_) == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
v_val_1769_ = lean_ctor_get(v_o_1767_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v_o_1767_, 1);
v___x_1770_ = l_Lean_MessageData_ofExpr(v_val_1769_);
return v___x_1770_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1774_ = l_Lean_MessageData_ofFormat(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1779_ = l_Lean_MessageData_ofFormat(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1780_, lean_object* v_i_1781_, lean_object* v_acc_1782_){
_start:
{
lean_object* v___y_1784_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_array_get_size(v_es_1780_);
v___x_1789_ = lean_nat_dec_lt(v_i_1781_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec(v_i_1781_);
v___x_1790_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_acc_1782_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v_e_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_e_1792_ = lean_array_fget_borrowed(v_es_1780_, v_i_1781_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v_i_1781_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_acc_1782_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
lean_inc(v_e_1792_);
v___x_1797_ = l_Lean_MessageData_ofExpr(v_e_1792_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___y_1784_ = v___x_1798_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_inc(v_e_1792_);
v___x_1799_ = l_Lean_MessageData_ofExpr(v_e_1792_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_acc_1782_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___y_1784_ = v___x_1800_;
goto v___jp_1783_;
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = lean_nat_add(v_i_1781_, v___x_1785_);
lean_dec(v_i_1781_);
v_i_1781_ = v___x_1786_;
v_acc_1782_ = v___y_1784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1801_, lean_object* v_i_1802_, lean_object* v_acc_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1801_, v_i_1802_, v_acc_1803_);
lean_dec_ref(v_es_1801_);
return v_res_1804_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1809_ = l_Lean_MessageData_ofFormat(v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1813_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1810_, v___x_1811_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1814_);
lean_dec_ref(v_es_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1818_, lean_object* v_f_1819_, lean_object* v_r_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1821_ = lean_string_length(v_l_1818_);
v___x_1822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_l_1818_);
v___x_1823_ = l_Lean_MessageData_ofFormat(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v_f_1819_);
v___x_1825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_r_1820_);
v___x_1826_ = l_Lean_MessageData_ofFormat(v___x_1825_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1824_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1821_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1832_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1833_ = l_Lean_MessageData_bracket(v___x_1831_, v_f_1830_, v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1836_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1837_ = l_Lean_MessageData_bracket(v___x_1835_, v_f_1834_, v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_object* v___x_1840_; 
lean_dec_ref(v_x_1839_);
v___x_1840_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1840_;
}
else
{
lean_object* v_tail_1841_; 
v_tail_1841_ = lean_ctor_get(v_x_1838_, 1);
if (lean_obj_tag(v_tail_1841_) == 0)
{
lean_object* v_head_1842_; 
lean_dec_ref(v_x_1839_);
v_head_1842_ = lean_ctor_get(v_x_1838_, 0);
lean_inc(v_head_1842_);
lean_dec_ref_known(v_x_1838_, 2);
return v_head_1842_;
}
else
{
lean_object* v_head_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1852_; 
lean_inc(v_tail_1841_);
v_head_1843_ = lean_ctor_get(v_x_1838_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v_x_1838_, 1);
lean_dec(v_unused_1853_);
v___x_1845_ = v_x_1838_;
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_head_1843_);
lean_dec(v_x_1838_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
lean_inc_ref(v_x_1839_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 7);
lean_ctor_set(v___x_1845_, 1, v_x_1839_);
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_head_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_x_1839_);
v___x_1848_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = l_Lean_MessageData_joinSep(v_tail_1841_, v_x_1839_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
return v___x_1850_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1858_ = l_Lean_MessageData_ofFormat(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_box(1);
v___x_1865_ = l_Lean_MessageData_ofFormat(v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1867_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1869_){
_start:
{
if (lean_obj_tag(v_x_1869_) == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1872_ = l_Lean_MessageData_joinSep(v_x_1869_, v___x_1871_);
v___x_1873_ = l_Lean_MessageData_sbracket(v___x_1872_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_array_to_list(v_msgs_1874_);
v___x_1876_ = l_Lean_MessageData_ofList(v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1881_ = l_Lean_MessageData_ofFormat(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1886_ = l_Lean_MessageData_ofFormat(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1891_ = l_Lean_MessageData_ofFormat(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1892_){
_start:
{
if (lean_obj_tag(v_xs_1892_) == 0)
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1893_;
}
else
{
lean_object* v_tail_1894_; 
v_tail_1894_ = lean_ctor_get(v_xs_1892_, 1);
lean_inc(v_tail_1894_);
if (lean_obj_tag(v_tail_1894_) == 0)
{
lean_object* v_head_1895_; 
v_head_1895_ = lean_ctor_get(v_xs_1892_, 0);
lean_inc(v_head_1895_);
lean_dec_ref_known(v_xs_1892_, 2);
return v_head_1895_;
}
else
{
lean_object* v_tail_1896_; 
v_tail_1896_ = lean_ctor_get(v_tail_1894_, 1);
if (lean_obj_tag(v_tail_1896_) == 0)
{
lean_object* v_head_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1914_; 
v_head_1897_ = lean_ctor_get(v_xs_1892_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_xs_1892_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_xs_1892_, 1);
lean_dec(v_unused_1915_);
v___x_1899_ = v_xs_1892_;
v_isShared_1900_ = v_isSharedCheck_1914_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_head_1897_);
lean_dec(v_xs_1892_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1914_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_head_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v_head_1901_ = lean_ctor_get(v_tail_1894_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_tail_1894_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_tail_1894_, 1);
lean_dec(v_unused_1913_);
v___x_1903_ = v_tail_1894_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_head_1901_);
lean_dec(v_tail_1894_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 7);
lean_ctor_set(v___x_1903_, 1, v___x_1905_);
lean_ctor_set(v___x_1903_, 0, v_head_1897_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_head_1897_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 7);
lean_ctor_set(v___x_1899_, 1, v_head_1901_);
lean_ctor_set(v___x_1899_, 0, v___x_1907_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_head_1901_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v_tail_1894_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; lean_object* v_unused_1941_; 
v_unused_1940_ = lean_ctor_get(v_tail_1894_, 1);
lean_dec(v_unused_1940_);
v_unused_1941_ = lean_ctor_get(v_tail_1894_, 0);
lean_dec(v_unused_1941_);
v___x_1917_ = v_tail_1894_;
v_isShared_1918_ = v_isSharedCheck_1939_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v_tail_1894_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1939_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1919_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1892_);
v___x_1920_ = lean_array_mk(v_xs_1892_);
v___x_1921_ = lean_array_pop(v___x_1920_);
v___x_1922_ = lean_array_to_list(v___x_1921_);
v___x_1923_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1924_ = l_Lean_MessageData_joinSep(v___x_1922_, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 7);
lean_ctor_set(v___x_1917_, 1, v___x_1925_);
lean_ctor_set(v___x_1917_, 0, v___x_1924_);
v___x_1927_ = v___x_1917_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v___x_1928_ = l_List_getLast_x21___redArg(v___x_1919_, v_xs_1892_);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_xs_1892_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1936_ = lean_ctor_get(v_xs_1892_, 1);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_xs_1892_, 0);
lean_dec(v_unused_1937_);
v___x_1930_ = v_xs_1892_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_dec(v_xs_1892_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 7);
lean_ctor_set(v___x_1930_, 1, v___x_1928_);
lean_ctor_set(v___x_1930_, 0, v___x_1927_);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__2(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1946_ = l_Lean_MessageData_ofFormat(v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1951_ = l_Lean_MessageData_ofFormat(v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1952_){
_start:
{
if (lean_obj_tag(v_xs_1952_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1953_;
}
else
{
lean_object* v_tail_1954_; 
v_tail_1954_ = lean_ctor_get(v_xs_1952_, 1);
lean_inc(v_tail_1954_);
if (lean_obj_tag(v_tail_1954_) == 0)
{
lean_object* v_head_1955_; 
v_head_1955_ = lean_ctor_get(v_xs_1952_, 0);
lean_inc(v_head_1955_);
lean_dec_ref_known(v_xs_1952_, 2);
return v_head_1955_;
}
else
{
lean_object* v_tail_1956_; 
v_tail_1956_ = lean_ctor_get(v_tail_1954_, 1);
if (lean_obj_tag(v_tail_1956_) == 0)
{
lean_object* v_head_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1974_; 
v_head_1957_ = lean_ctor_get(v_xs_1952_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_xs_1952_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_xs_1952_, 1);
lean_dec(v_unused_1975_);
v___x_1959_ = v_xs_1952_;
v_isShared_1960_ = v_isSharedCheck_1974_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_head_1957_);
lean_dec(v_xs_1952_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1974_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_head_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1972_; 
v_head_1961_ = lean_ctor_get(v_tail_1954_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_tail_1954_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_tail_1954_, 1);
lean_dec(v_unused_1973_);
v___x_1963_ = v_tail_1954_;
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_head_1961_);
lean_dec(v_tail_1954_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 7);
lean_ctor_set(v___x_1963_, 1, v___x_1965_);
lean_ctor_set(v___x_1963_, 0, v_head_1957_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_head_1957_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 7);
lean_ctor_set(v___x_1959_, 1, v_head_1961_);
lean_ctor_set(v___x_1959_, 0, v___x_1967_);
v___x_1969_ = v___x_1959_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_head_1961_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
else
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1999_; 
v_isSharedCheck_1999_ = !lean_is_exclusive(v_tail_1954_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; 
v_unused_2000_ = lean_ctor_get(v_tail_1954_, 1);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_tail_1954_, 0);
lean_dec(v_unused_2001_);
v___x_1977_ = v_tail_1954_;
v_isShared_1978_ = v_isSharedCheck_1999_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_tail_1954_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1999_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1979_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1952_);
v___x_1980_ = lean_array_mk(v_xs_1952_);
v___x_1981_ = lean_array_pop(v___x_1980_);
v___x_1982_ = lean_array_to_list(v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1984_ = l_Lean_MessageData_joinSep(v___x_1982_, v___x_1983_);
v___x_1985_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_1985_);
lean_ctor_set(v___x_1977_, 0, v___x_1984_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v___x_1988_ = l_List_getLast_x21___redArg(v___x_1979_, v_xs_1952_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_xs_1952_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1996_ = lean_ctor_get(v_xs_1952_, 1);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_xs_1952_, 0);
lean_dec(v_unused_1997_);
v___x_1990_ = v_xs_1952_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v_xs_1952_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 7);
lean_ctor_set(v___x_1990_, 1, v___x_1988_);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__0(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2010_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_note_2012_);
return v___x_2014_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2019_ = l_Lean_MessageData_ofFormat(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2021_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___x_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v_hint_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2030_ = lean_box(0);
v___x_2031_ = l_List_mapTR_loop___redArg(v___x_2029_, v_es_2028_, v___x_2030_);
v___x_2032_ = l_Lean_MessageData_ofList(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2036_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2037_ = l_Lean_instInhabitedPosition_default;
v___x_2038_ = lean_box(0);
v___x_2039_ = 0;
v___x_2040_ = 2;
v___x_2041_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2041_, 0, v___x_2036_);
lean_ctor_set(v___x_2041_, 1, v___x_2037_);
lean_ctor_set(v___x_2041_, 2, v___x_2038_);
lean_ctor_set(v___x_2041_, 3, v___x_2036_);
lean_ctor_set(v___x_2041_, 4, v_inst_2035_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*5, v___x_2039_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*5 + 1, v___x_2040_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*5 + 2, v___x_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2042_, lean_object* v_inst_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2047_, lean_object* v_inst_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v_fileName_2064_; lean_object* v_pos_2065_; lean_object* v_endPos_2066_; uint8_t v_keepFullRange_2067_; uint8_t v_severity_2068_; uint8_t v_isSilent_2069_; lean_object* v_caption_2070_; lean_object* v_data_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_fileName_2064_ = lean_ctor_get(v_x_2063_, 0);
lean_inc_ref(v_fileName_2064_);
v_pos_2065_ = lean_ctor_get(v_x_2063_, 1);
lean_inc_ref(v_pos_2065_);
v_endPos_2066_ = lean_ctor_get(v_x_2063_, 2);
lean_inc(v_endPos_2066_);
v_keepFullRange_2067_ = lean_ctor_get_uint8(v_x_2063_, sizeof(void*)*5);
v_severity_2068_ = lean_ctor_get_uint8(v_x_2063_, sizeof(void*)*5 + 1);
v_isSilent_2069_ = lean_ctor_get_uint8(v_x_2063_, sizeof(void*)*5 + 2);
v_caption_2070_ = lean_ctor_get(v_x_2063_, 3);
lean_inc_ref(v_caption_2070_);
v_data_2071_ = lean_ctor_get(v_x_2063_, 4);
lean_inc(v_data_2071_);
lean_dec_ref(v_x_2063_);
v___x_2072_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2073_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_fileName_2064_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2079_ = l_Lean_instToJsonPosition_toJson(v_pos_2065_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2076_);
v___x_2082_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2083_ = l_Lean_Option_toJson___redArg(v___x_2072_, v_endPos_2066_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2076_);
v___x_2086_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2087_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2087_, 0, v_keepFullRange_2067_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2076_);
v___x_2090_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2091_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2068_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2076_);
v___x_2094_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2095_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2095_, 0, v_isSilent_2069_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2076_);
v___x_2098_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_caption_2070_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2076_);
v___x_2102_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2103_ = lean_apply_1(v_inst_2062_, v_data_2071_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2076_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2076_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2101_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2097_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2093_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2089_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2085_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2081_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2077_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2115_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2116_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2114_, v___x_2113_, v___x_2115_);
v___x_2117_ = l_Lean_Json_mkObj(v___x_2116_);
lean_dec(v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2118_, lean_object* v_inst_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2119_, v_x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2123_, 0, lean_box(0));
lean_closure_set(v___x_2123_, 1, v_inst_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2124_, lean_object* v_inst_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2126_, 0, lean_box(0));
lean_closure_set(v___x_2126_, 1, v_inst_2125_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = 1;
v___x_2133_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2134_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2133_, v___x_2132_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2137_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2138_ = lean_string_append(v___x_2137_, v___x_2136_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = 1;
v___x_2142_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2143_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2142_, v___x_2141_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2145_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2146_ = lean_string_append(v___x_2145_, v___x_2144_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2149_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2150_ = lean_string_append(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = 1;
v___x_2157_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2160_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2161_ = lean_string_append(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2163_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2164_ = lean_string_append(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = 1;
v___x_2168_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2171_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2174_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2175_ = lean_string_append(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = 1;
v___x_2180_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2183_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2184_ = lean_string_append(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2186_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2187_ = lean_string_append(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = 1;
v___x_2191_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2194_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2195_ = lean_string_append(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2197_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2198_ = lean_string_append(v___x_2197_, v___x_2196_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = 1;
v___x_2202_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2205_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2206_ = lean_string_append(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2208_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2209_ = lean_string_append(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = 1;
v___x_2213_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2216_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2217_ = lean_string_append(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2219_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2220_ = lean_string_append(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = 1;
v___x_2224_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2225_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2224_, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2227_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2228_ = lean_string_append(v___x_2227_, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2230_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2231_ = lean_string_append(v___x_2230_, v___x_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2232_, lean_object* v_json_2233_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2235_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2233_);
v___x_2236_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2234_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2242_ = lean_string_append(v___x_2241_, v_a_2237_);
lean_dec(v_a_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_a_2247_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2248_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2249_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2250_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2233_);
v___x_2251_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2248_, v___x_2250_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2261_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2256_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2257_ = lean_string_append(v___x_2256_, v_a_2252_);
lean_dec(v_a_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2262_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2263_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2233_);
v___x_2264_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2249_, v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2274_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2274_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2269_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2270_ = lean_string_append(v___x_2269_, v_a_2265_);
lean_dec(v_a_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2270_);
v___x_2272_ = v___x_2267_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_a_2275_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2276_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2277_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2233_);
v___x_2278_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2276_, v___x_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_a_2275_);
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2288_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2288_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2284_ = lean_string_append(v___x_2283_, v_a_2279_);
lean_dec(v_a_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2284_);
v___x_2286_ = v___x_2281_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2289_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2290_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2291_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2233_);
v___x_2292_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2290_, v___x_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_a_2289_);
lean_dec(v_a_2275_);
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2297_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2298_ = lean_string_append(v___x_2297_, v_a_2293_);
lean_dec(v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2303_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2304_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2233_);
v___x_2305_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2276_, v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2303_);
lean_dec(v_a_2289_);
lean_dec(v_a_2275_);
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2315_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2315_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2310_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2311_ = lean_string_append(v___x_2310_, v_a_2306_);
lean_dec(v_a_2306_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2311_);
v___x_2313_ = v___x_2308_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_a_2316_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2317_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2233_);
v___x_2318_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v___x_2234_, v___x_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2303_);
lean_dec(v_a_2289_);
lean_dec(v_a_2275_);
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
lean_dec(v_json_2233_);
lean_dec_ref(v_inst_2232_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2328_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2324_ = lean_string_append(v___x_2323_, v_a_2319_);
lean_dec(v_a_2319_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2329_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2330_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2331_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2233_, v_inst_2232_, v___x_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2329_);
lean_dec(v_a_2316_);
lean_dec(v_a_2303_);
lean_dec(v_a_2289_);
lean_dec(v_a_2275_);
lean_dec(v_a_2262_);
lean_dec(v_a_2247_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2341_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2341_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2336_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2337_ = lean_string_append(v___x_2336_, v_a_2332_);
lean_dec(v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2337_);
v___x_2339_ = v___x_2334_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2353_; 
v_a_2342_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2344_ = v___x_2331_;
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2331_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; uint8_t v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2351_; 
v___x_2346_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2346_, 0, v_a_2247_);
lean_ctor_set(v___x_2346_, 1, v_a_2262_);
lean_ctor_set(v___x_2346_, 2, v_a_2275_);
lean_ctor_set(v___x_2346_, 3, v_a_2329_);
lean_ctor_set(v___x_2346_, 4, v_a_2342_);
v___x_2347_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*5, v___x_2347_);
v___x_2348_ = lean_unbox(v_a_2303_);
lean_dec(v_a_2303_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*5 + 1, v___x_2348_);
v___x_2349_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*5 + 2, v___x_2349_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2346_);
v___x_2351_ = v___x_2344_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2354_, lean_object* v_inst_2355_, lean_object* v_json_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2355_, v_json_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2359_, 0, lean_box(0));
lean_closure_set(v___x_2359_, 1, v_inst_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2360_, lean_object* v_inst_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2362_, 0, lean_box(0));
lean_closure_set(v___x_2362_, 1, v_inst_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2363_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_box(0);
return v___x_2364_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2366_; 
v_val_2365_ = lean_ctor_get(v_x_2363_, 0);
lean_inc(v_val_2365_);
lean_dec_ref_known(v_x_2363_, 1);
v___x_2366_ = l_Lean_instToJsonPosition_toJson(v_val_2365_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
if (lean_obj_tag(v_a_2367_) == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_array_to_list(v_a_2368_);
return v___x_2369_;
}
else
{
lean_object* v_head_2370_; lean_object* v_tail_2371_; lean_object* v___x_2372_; 
v_head_2370_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_head_2370_);
v_tail_2371_ = lean_ctor_get(v_a_2367_, 1);
lean_inc(v_tail_2371_);
lean_dec_ref_known(v_a_2367_, 2);
v___x_2372_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2368_, v_head_2370_);
v_a_2367_ = v_tail_2371_;
v_a_2368_ = v___x_2372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2375_){
_start:
{
lean_object* v_toBaseMessage_2376_; lean_object* v_kind_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2442_; 
v_toBaseMessage_2376_ = lean_ctor_get(v_x_2375_, 0);
v_kind_2377_ = lean_ctor_get(v_x_2375_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_x_2375_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2379_ = v_x_2375_;
v_isShared_2380_ = v_isSharedCheck_2442_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_kind_2377_);
lean_inc(v_toBaseMessage_2376_);
lean_dec(v_x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2442_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_fileName_2381_; lean_object* v_pos_2382_; lean_object* v_endPos_2383_; uint8_t v_keepFullRange_2384_; uint8_t v_severity_2385_; uint8_t v_isSilent_2386_; lean_object* v_caption_2387_; lean_object* v_data_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v_fileName_2381_ = lean_ctor_get(v_toBaseMessage_2376_, 0);
lean_inc_ref(v_fileName_2381_);
v_pos_2382_ = lean_ctor_get(v_toBaseMessage_2376_, 1);
lean_inc_ref(v_pos_2382_);
v_endPos_2383_ = lean_ctor_get(v_toBaseMessage_2376_, 2);
lean_inc(v_endPos_2383_);
v_keepFullRange_2384_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5);
v_severity_2385_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5 + 1);
v_isSilent_2386_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5 + 2);
v_caption_2387_ = lean_ctor_get(v_toBaseMessage_2376_, 3);
lean_inc_ref(v_caption_2387_);
v_data_2388_ = lean_ctor_get(v_toBaseMessage_2376_, 4);
lean_inc(v_data_2388_);
lean_dec_ref(v_toBaseMessage_2376_);
v___x_2389_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_fileName_2381_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___x_2390_);
lean_ctor_set(v___x_2379_, 0, v___x_2389_);
v___x_2392_ = v___x_2379_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2396_ = l_Lean_instToJsonPosition_toJson(v_pos_2382_);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v___x_2393_);
v___x_2399_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2400_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2383_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2393_);
v___x_2403_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2404_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2404_, 0, v_keepFullRange_2384_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2393_);
v___x_2407_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2408_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2385_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v___x_2393_);
v___x_2411_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2412_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2412_, 0, v_isSilent_2386_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v___x_2393_);
v___x_2415_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_caption_2387_);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2393_);
v___x_2419_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_data_2388_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___x_2393_);
v___x_2423_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2424_ = 1;
v___x_2425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2377_, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2423_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2393_);
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2393_);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2422_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2418_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2414_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2410_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2406_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2402_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2398_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2394_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2439_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2437_, v___x_2438_);
v___x_2440_ = l_Lean_Json_mkObj(v___x_2439_);
lean_dec(v___x_2439_);
return v___x_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = l_Lean_Json_getObjValD(v_j_2445_, v_k_2446_);
v___x_2448_ = l_Lean_Json_getStr_x3f(v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2449_, lean_object* v_k_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2449_, v_k_2450_);
lean_dec_ref(v_k_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2452_, lean_object* v_k_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = l_Lean_Json_getObjValD(v_j_2452_, v_k_2453_);
v___x_2455_ = l_Lean_instFromJsonPosition_fromJson(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2456_, lean_object* v_k_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2456_, v_k_2457_);
lean_dec_ref(v_k_2457_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2459_, lean_object* v_k_2460_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = l_Lean_Json_getObjValD(v_j_2459_, v_k_2460_);
v___x_2462_ = l_Lean_Json_getBool_x3f(v___x_2461_);
lean_dec(v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2463_, lean_object* v_k_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2463_, v_k_2464_);
lean_dec_ref(v_k_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2466_, lean_object* v_k_2467_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = l_Lean_Json_getObjValD(v_j_2466_, v_k_2467_);
v___x_2469_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2470_, lean_object* v_k_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2470_, v_k_2471_);
lean_dec_ref(v_k_2471_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2473_, lean_object* v_k_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = l_Lean_Json_getObjValD(v_j_2473_, v_k_2474_);
v___x_2476_ = l_Lean_Name_fromJson_x3f(v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2477_, lean_object* v_k_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2477_, v_k_2478_);
lean_dec_ref(v_k_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2482_){
_start:
{
if (lean_obj_tag(v_x_2482_) == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_instFromJsonPosition_fromJson(v_x_2482_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2501_; 
v_a_2493_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2495_ = v___x_2484_;
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2484_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2493_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2497_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = l_Lean_Json_getObjValD(v_j_2502_, v_k_2503_);
v___x_2505_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2506_, lean_object* v_k_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2506_, v_k_2507_);
lean_dec_ref(v_k_2507_);
return v_res_2508_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = 1;
v___x_2514_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2515_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2514_, v___x_2513_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2517_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2518_ = lean_string_append(v___x_2517_, v___x_2516_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2520_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2521_ = lean_string_append(v___x_2520_, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2523_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2524_ = lean_string_append(v___x_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2526_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2527_ = lean_string_append(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2529_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2530_ = lean_string_append(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2532_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2533_ = lean_string_append(v___x_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2535_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2536_ = lean_string_append(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2538_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2539_ = lean_string_append(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2541_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2542_ = lean_string_append(v___x_2541_, v___x_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2544_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2545_ = lean_string_append(v___x_2544_, v___x_2543_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2547_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2548_ = lean_string_append(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2550_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2551_ = lean_string_append(v___x_2550_, v___x_2549_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2553_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2554_ = lean_string_append(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2556_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2557_ = lean_string_append(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2559_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2560_ = lean_string_append(v___x_2559_, v___x_2558_);
return v___x_2560_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2562_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2563_ = lean_string_append(v___x_2562_, v___x_2561_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2565_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2566_ = lean_string_append(v___x_2565_, v___x_2564_);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = 1;
v___x_2570_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2571_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2570_, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2573_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2574_ = lean_string_append(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2576_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2577_ = lean_string_append(v___x_2576_, v___x_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2578_);
v___x_2580_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2578_, v___x_2579_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_json_2578_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2586_ = lean_string_append(v___x_2585_, v_a_2581_);
lean_dec(v_a_2581_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2586_);
v___x_2588_ = v___x_2583_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_a_2591_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2592_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2578_);
v___x_2593_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2578_, v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2598_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2599_ = lean_string_append(v___x_2598_, v_a_2594_);
lean_dec(v_a_2594_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2599_);
v___x_2601_ = v___x_2596_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_a_2604_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2605_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2578_);
v___x_2606_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2578_, v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2616_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2611_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2612_ = lean_string_append(v___x_2611_, v_a_2607_);
lean_dec(v_a_2607_);
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
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2618_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2578_);
v___x_2619_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2578_, v___x_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2625_ = lean_string_append(v___x_2624_, v_a_2620_);
lean_dec(v_a_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_a_2630_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2619_, 1);
v___x_2631_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2578_);
v___x_2632_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2578_, v___x_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2630_);
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2642_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2642_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2637_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2638_ = lean_string_append(v___x_2637_, v_a_2633_);
lean_dec(v_a_2633_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2638_);
v___x_2640_ = v___x_2635_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v_a_2643_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2644_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2578_);
v___x_2645_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2578_, v___x_2644_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_a_2643_);
lean_dec(v_a_2630_);
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2655_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2655_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2651_ = lean_string_append(v___x_2650_, v_a_2646_);
lean_dec(v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2656_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2657_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2578_);
v___x_2658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2578_, v___x_2657_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2656_);
lean_dec(v_a_2643_);
lean_dec(v_a_2630_);
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2664_ = lean_string_append(v___x_2663_, v_a_2659_);
lean_dec(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2669_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2670_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2578_);
v___x_2671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2578_, v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_a_2669_);
lean_dec(v_a_2656_);
lean_dec(v_a_2643_);
lean_dec(v_a_2630_);
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
lean_dec(v_json_2578_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2681_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2681_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2676_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2677_ = lean_string_append(v___x_2676_, v_a_2672_);
lean_dec(v_a_2672_);
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
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2682_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2683_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2684_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2578_, v___x_2683_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_a_2682_);
lean_dec(v_a_2669_);
lean_dec(v_a_2656_);
lean_dec(v_a_2643_);
lean_dec(v_a_2630_);
lean_dec(v_a_2617_);
lean_dec(v_a_2604_);
lean_dec(v_a_2591_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2694_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2694_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2689_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2690_ = lean_string_append(v___x_2689_, v_a_2685_);
lean_dec(v_a_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2690_);
v___x_2692_ = v___x_2687_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2707_; 
v_a_2695_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2697_ = v___x_2684_;
v_isShared_2698_ = v_isSharedCheck_2707_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2684_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2707_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; uint8_t v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2699_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2699_, 0, v_a_2591_);
lean_ctor_set(v___x_2699_, 1, v_a_2604_);
lean_ctor_set(v___x_2699_, 2, v_a_2617_);
lean_ctor_set(v___x_2699_, 3, v_a_2669_);
lean_ctor_set(v___x_2699_, 4, v_a_2682_);
v___x_2700_ = lean_unbox(v_a_2630_);
lean_dec(v_a_2630_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*5, v___x_2700_);
v___x_2701_ = lean_unbox(v_a_2643_);
lean_dec(v_a_2643_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*5 + 1, v___x_2701_);
v___x_2702_ = lean_unbox(v_a_2656_);
lean_dec(v_a_2656_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*5 + 2, v___x_2702_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2699_);
lean_ctor_set(v___x_2703_, 1, v_a_2695_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2703_);
v___x_2705_ = v___x_2697_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2712_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2714_ = l_Lean_Name_str___override(v_errorName_2712_, v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2715_, lean_object* v_name_2716_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = l_Lean_kindOfErrorName(v_name_2716_);
v___x_2718_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_msg_2715_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2720_){
_start:
{
switch(lean_obj_tag(v_a_2720_))
{
case 0:
{
return v_a_2720_;
}
case 1:
{
lean_object* v_pre_2721_; lean_object* v_str_2722_; lean_object* v_p_x27_2723_; uint8_t v___x_2724_; 
v_pre_2721_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_pre_2721_);
v_str_2722_ = lean_ctor_get(v_a_2720_, 1);
lean_inc_ref(v_str_2722_);
lean_dec_ref_known(v_a_2720_, 2);
v_p_x27_2723_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2721_);
v___x_2724_ = l_Lean_Name_isAnonymous(v_p_x27_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Name_str___override(v_p_x27_2723_, v_str_2722_);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2727_ = lean_string_dec_eq(v_str_2722_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Name_str___override(v_p_x27_2723_, v_str_2722_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; 
lean_dec(v_p_x27_2723_);
lean_dec_ref(v_str_2722_);
v___x_2729_ = lean_box(0);
return v___x_2729_;
}
}
}
default: 
{
lean_object* v_pre_2730_; lean_object* v_i_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_pre_2730_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_pre_2730_);
v_i_2731_ = lean_ctor_get(v_a_2720_, 1);
lean_inc(v_i_2731_);
lean_dec_ref_known(v_a_2720_, 2);
v___x_2732_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2730_);
v___x_2733_ = l_Lean_Name_num___override(v___x_2732_, v_i_2731_);
return v___x_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2734_){
_start:
{
switch(lean_obj_tag(v_x_2734_))
{
case 3:
{
lean_object* v_a_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2744_; 
v_a_2735_ = lean_ctor_get(v_x_2734_, 0);
v_a_2736_ = lean_ctor_get(v_x_2734_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2738_ = v_x_2734_;
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_inc(v_a_2735_);
lean_dec(v_x_2734_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = l_Lean_MessageData_stripNestedTags(v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2735_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
case 4:
{
lean_object* v_a_2745_; lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2754_; 
v_a_2745_ = lean_ctor_get(v_x_2734_, 0);
v_a_2746_ = lean_ctor_get(v_x_2734_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2748_ = v_x_2734_;
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_inc(v_a_2745_);
lean_dec(v_x_2734_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = l_Lean_MessageData_stripNestedTags(v_a_2746_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v___x_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2745_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
case 8:
{
lean_object* v_a_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2764_; 
v_a_2755_ = lean_ctor_get(v_x_2734_, 0);
v_a_2756_ = lean_ctor_get(v_x_2734_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2758_ = v_x_2734_;
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_inc(v_a_2755_);
lean_dec(v_x_2734_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2755_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2760_);
v___x_2762_ = v___x_2758_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_a_2756_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
case 11:
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2774_; 
v_a_2765_ = lean_ctor_get(v_x_2734_, 0);
v_a_2766_ = lean_ctor_get(v_x_2734_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2768_ = v_x_2734_;
v_isShared_2769_ = v_isSharedCheck_2774_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_inc(v_a_2765_);
lean_dec(v_x_2734_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2774_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = l_Lean_MessageData_stripNestedTags(v_a_2766_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2770_);
v___x_2772_ = v___x_2768_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2765_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
default: 
{
return v_x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2775_){
_start:
{
if (lean_obj_tag(v_x_2775_) == 1)
{
lean_object* v_pre_2776_; lean_object* v_str_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_pre_2776_ = lean_ctor_get(v_x_2775_, 0);
v_str_2777_ = lean_ctor_get(v_x_2775_, 1);
v___x_2778_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2779_ = lean_string_dec_eq(v_str_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_box(0);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; 
lean_inc(v_pre_2776_);
v___x_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_pre_2776_);
return v___x_2781_;
}
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_box(0);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_errorNameOfKind_x3f(v_x_2783_);
lean_dec(v_x_2783_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = l_Lean_MessageData_kind(v_msg_2785_);
v___x_2787_ = l_Lean_errorNameOfKind_x3f(v___x_2786_);
lean_dec(v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_MessageData_errorName_x3f(v_msg_2788_);
lean_dec_ref(v_msg_2788_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2790_){
_start:
{
lean_object* v_data_2791_; lean_object* v___x_2792_; 
v_data_2791_ = lean_ctor_get(v_msg_2790_, 4);
v___x_2792_ = l_Lean_MessageData_errorName_x3f(v_data_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Message_errorName_x3f(v_msg_2793_);
lean_dec_ref(v_msg_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2795_){
_start:
{
lean_object* v_toBaseMessage_2796_; lean_object* v_fileName_2797_; lean_object* v_pos_2798_; lean_object* v_endPos_2799_; uint8_t v_keepFullRange_2800_; uint8_t v_severity_2801_; uint8_t v_isSilent_2802_; lean_object* v_caption_2803_; lean_object* v_data_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2813_; 
v_toBaseMessage_2796_ = lean_ctor_get(v_msg_2795_, 0);
lean_inc_ref(v_toBaseMessage_2796_);
lean_dec_ref(v_msg_2795_);
v_fileName_2797_ = lean_ctor_get(v_toBaseMessage_2796_, 0);
v_pos_2798_ = lean_ctor_get(v_toBaseMessage_2796_, 1);
v_endPos_2799_ = lean_ctor_get(v_toBaseMessage_2796_, 2);
v_keepFullRange_2800_ = lean_ctor_get_uint8(v_toBaseMessage_2796_, sizeof(void*)*5);
v_severity_2801_ = lean_ctor_get_uint8(v_toBaseMessage_2796_, sizeof(void*)*5 + 1);
v_isSilent_2802_ = lean_ctor_get_uint8(v_toBaseMessage_2796_, sizeof(void*)*5 + 2);
v_caption_2803_ = lean_ctor_get(v_toBaseMessage_2796_, 3);
v_data_2804_ = lean_ctor_get(v_toBaseMessage_2796_, 4);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_toBaseMessage_2796_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2806_ = v_toBaseMessage_2796_;
v_isShared_2807_ = v_isSharedCheck_2813_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_data_2804_);
lean_inc(v_caption_2803_);
lean_inc(v_endPos_2799_);
lean_inc(v_pos_2798_);
lean_inc(v_fileName_2797_);
lean_dec(v_toBaseMessage_2796_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2813_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v_data_2804_);
v___x_2809_ = l_Lean_MessageData_ofFormat(v___x_2808_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 4, v___x_2809_);
v___x_2811_ = v___x_2806_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_fileName_2797_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_pos_2798_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_endPos_2799_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_caption_2803_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v___x_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2812_, sizeof(void*)*5, v_keepFullRange_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2812_, sizeof(void*)*5 + 1, v_severity_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2812_, sizeof(void*)*5 + 2, v_isSilent_2802_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2819_, uint8_t v_includeEndPos_2820_){
_start:
{
lean_object* v___y_2822_; lean_object* v___y_2826_; uint32_t v___y_2827_; lean_object* v___y_2831_; lean_object* v_str_2834_; lean_object* v_toBaseMessage_2844_; lean_object* v_kind_2845_; lean_object* v_fileName_2846_; lean_object* v_pos_2847_; lean_object* v_endPos_2848_; uint8_t v_severity_2849_; lean_object* v_caption_2850_; lean_object* v_data_2851_; lean_object* v___y_2853_; lean_object* v_str_2854_; lean_object* v___y_2862_; 
v_toBaseMessage_2844_ = lean_ctor_get(v_msg_2819_, 0);
lean_inc_ref(v_toBaseMessage_2844_);
v_kind_2845_ = lean_ctor_get(v_msg_2819_, 1);
lean_inc(v_kind_2845_);
lean_dec_ref(v_msg_2819_);
v_fileName_2846_ = lean_ctor_get(v_toBaseMessage_2844_, 0);
lean_inc_ref(v_fileName_2846_);
v_pos_2847_ = lean_ctor_get(v_toBaseMessage_2844_, 1);
lean_inc_ref(v_pos_2847_);
v_endPos_2848_ = lean_ctor_get(v_toBaseMessage_2844_, 2);
lean_inc(v_endPos_2848_);
v_severity_2849_ = lean_ctor_get_uint8(v_toBaseMessage_2844_, sizeof(void*)*5 + 1);
v_caption_2850_ = lean_ctor_get(v_toBaseMessage_2844_, 3);
lean_inc_ref(v_caption_2850_);
v_data_2851_ = lean_ctor_get(v_toBaseMessage_2844_, 4);
lean_inc(v_data_2851_);
lean_dec_ref(v_toBaseMessage_2844_);
if (v_includeEndPos_2820_ == 0)
{
lean_object* v___x_2868_; 
lean_dec(v_endPos_2848_);
v___x_2868_ = lean_box(0);
v___y_2862_ = v___x_2868_;
goto v___jp_2861_;
}
else
{
v___y_2862_ = v_endPos_2848_;
goto v___jp_2861_;
}
v___jp_2821_:
{
lean_object* v___x_2823_; lean_object* v_str_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2824_ = lean_string_append(v___y_2822_, v___x_2823_);
return v_str_2824_;
}
v___jp_2825_:
{
uint32_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = 10;
v___x_2829_ = lean_uint32_dec_eq(v___y_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
v___y_2822_ = v___y_2826_;
goto v___jp_2821_;
}
else
{
return v___y_2826_;
}
}
v___jp_2830_:
{
uint32_t v___x_2832_; 
v___x_2832_ = 65;
v___y_2826_ = v___y_2831_;
v___y_2827_ = v___x_2832_;
goto v___jp_2825_;
}
v___jp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_string_utf8_byte_size(v_str_2834_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_nat_dec_eq(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_inc_ref(v_str_2834_);
v___x_2838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2838_, 0, v_str_2834_);
lean_ctor_set(v___x_2838_, 1, v___x_2836_);
lean_ctor_set(v___x_2838_, 2, v___x_2835_);
v___x_2839_ = l_String_Slice_Pos_prev_x3f(v___x_2838_, v___x_2835_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref_known(v___x_2838_, 3);
v___y_2831_ = v_str_2834_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2841_; 
v_val_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_val_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_String_Slice_Pos_get_x3f(v___x_2838_, v_val_2840_);
lean_dec(v_val_2840_);
lean_dec_ref_known(v___x_2838_, 3);
if (lean_obj_tag(v___x_2841_) == 0)
{
v___y_2831_ = v_str_2834_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2842_; uint32_t v___x_2843_; 
v_val_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = lean_unbox_uint32(v_val_2842_);
lean_dec(v_val_2842_);
v___y_2826_ = v_str_2834_;
v___y_2827_ = v___x_2843_;
goto v___jp_2825_;
}
}
}
else
{
v___y_2822_ = v_str_2834_;
goto v___jp_2821_;
}
}
v___jp_2852_:
{
switch(v_severity_2849_)
{
case 0:
{
lean_dec(v___y_2853_);
lean_dec_ref(v_pos_2847_);
lean_dec_ref(v_fileName_2846_);
lean_dec(v_kind_2845_);
v_str_2834_ = v_str_2854_;
goto v___jp_2833_;
}
case 1:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v_str_2857_; 
v___x_2855_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2856_ = l_Lean_errorNameOfKind_x3f(v_kind_2845_);
lean_dec(v_kind_2845_);
v_str_2857_ = l_Lean_mkErrorStringWithPos(v_fileName_2846_, v_pos_2847_, v_str_2854_, v___y_2853_, v___x_2855_, v___x_2856_);
lean_dec_ref(v_str_2854_);
v_str_2834_ = v_str_2857_;
goto v___jp_2833_;
}
default: 
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_str_2860_; 
v___x_2858_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2859_ = l_Lean_errorNameOfKind_x3f(v_kind_2845_);
lean_dec(v_kind_2845_);
v_str_2860_ = l_Lean_mkErrorStringWithPos(v_fileName_2846_, v_pos_2847_, v_str_2854_, v___y_2853_, v___x_2858_, v___x_2859_);
lean_dec_ref(v_str_2854_);
v_str_2834_ = v_str_2860_;
goto v___jp_2833_;
}
}
}
v___jp_2861_:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2864_ = lean_string_dec_eq(v_caption_2850_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_str_2867_; 
v___x_2865_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2866_ = lean_string_append(v_caption_2850_, v___x_2865_);
v_str_2867_ = lean_string_append(v___x_2866_, v_data_2851_);
lean_dec(v_data_2851_);
v___y_2853_ = v___y_2862_;
v_str_2854_ = v_str_2867_;
goto v___jp_2852_;
}
else
{
lean_dec_ref(v_caption_2850_);
v___y_2853_ = v___y_2862_;
v_str_2854_ = v_data_2851_;
goto v___jp_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2869_, lean_object* v_includeEndPos_2870_){
_start:
{
uint8_t v_includeEndPos_boxed_2871_; lean_object* v_res_2872_; 
v_includeEndPos_boxed_2871_ = lean_unbox(v_includeEndPos_2870_);
v_res_2872_ = l_Lean_SerialMessage_toString(v_msg_2869_, v_includeEndPos_boxed_2871_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2873_){
_start:
{
uint8_t v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = 0;
v___x_2875_ = l_Lean_SerialMessage_toString(v_msg_2873_, v___x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2878_){
_start:
{
lean_object* v_data_2879_; lean_object* v___x_2880_; 
v_data_2879_ = lean_ctor_get(v_msg_2878_, 4);
v___x_2880_ = l_Lean_MessageData_kind(v_data_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Message_kind(v_msg_2881_);
lean_dec_ref(v_msg_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2883_){
_start:
{
lean_object* v_data_2884_; uint8_t v___x_2885_; 
v_data_2884_ = lean_ctor_get(v_msg_2883_, 4);
v___x_2885_ = l_Lean_MessageData_isTrace(v_data_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2886_){
_start:
{
uint8_t v_res_2887_; lean_object* v_r_2888_; 
v_res_2887_ = l_Lean_Message_isTrace(v_msg_2886_);
lean_dec_ref(v_msg_2886_);
v_r_2888_ = lean_box(v_res_2887_);
return v_r_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2889_){
_start:
{
lean_object* v_fileName_2891_; lean_object* v_pos_2892_; lean_object* v_endPos_2893_; uint8_t v_keepFullRange_2894_; uint8_t v_severity_2895_; uint8_t v_isSilent_2896_; lean_object* v_caption_2897_; lean_object* v_data_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2908_; 
v_fileName_2891_ = lean_ctor_get(v_msg_2889_, 0);
v_pos_2892_ = lean_ctor_get(v_msg_2889_, 1);
v_endPos_2893_ = lean_ctor_get(v_msg_2889_, 2);
v_keepFullRange_2894_ = lean_ctor_get_uint8(v_msg_2889_, sizeof(void*)*5);
v_severity_2895_ = lean_ctor_get_uint8(v_msg_2889_, sizeof(void*)*5 + 1);
v_isSilent_2896_ = lean_ctor_get_uint8(v_msg_2889_, sizeof(void*)*5 + 2);
v_caption_2897_ = lean_ctor_get(v_msg_2889_, 3);
v_data_2898_ = lean_ctor_get(v_msg_2889_, 4);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_msg_2889_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2900_ = v_msg_2889_;
v_isShared_2901_ = v_isSharedCheck_2908_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_data_2898_);
lean_inc(v_caption_2897_);
lean_inc(v_endPos_2893_);
lean_inc(v_pos_2892_);
lean_inc(v_fileName_2891_);
lean_dec(v_msg_2889_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2908_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_inc(v_data_2898_);
v___x_2902_ = l_Lean_MessageData_toString(v_data_2898_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 4, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_fileName_2891_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_pos_2892_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_endPos_2893_);
lean_ctor_set(v_reuseFailAlloc_2907_, 3, v_caption_2897_);
lean_ctor_set(v_reuseFailAlloc_2907_, 4, v___x_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2907_, sizeof(void*)*5, v_keepFullRange_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2907_, sizeof(void*)*5 + 1, v_severity_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2907_, sizeof(void*)*5 + 2, v_isSilent_2896_);
v___x_2904_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = l_Lean_MessageData_kind(v_data_2898_);
lean_dec(v_data_2898_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
return v___x_2906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Message_serialize(v_msg_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2912_, uint8_t v_includeEndPos_2913_){
_start:
{
lean_object* v_fileName_2915_; lean_object* v_pos_2916_; lean_object* v_endPos_2917_; uint8_t v_severity_2918_; lean_object* v_caption_2919_; lean_object* v_data_2920_; lean_object* v___x_2921_; lean_object* v___y_2923_; lean_object* v___y_2927_; uint32_t v___y_2928_; lean_object* v___y_2932_; lean_object* v_str_2935_; lean_object* v___x_2945_; lean_object* v___y_2947_; lean_object* v_str_2948_; lean_object* v___y_2956_; 
v_fileName_2915_ = lean_ctor_get(v_msg_2912_, 0);
lean_inc_ref(v_fileName_2915_);
v_pos_2916_ = lean_ctor_get(v_msg_2912_, 1);
lean_inc_ref(v_pos_2916_);
v_endPos_2917_ = lean_ctor_get(v_msg_2912_, 2);
lean_inc(v_endPos_2917_);
v_severity_2918_ = lean_ctor_get_uint8(v_msg_2912_, sizeof(void*)*5 + 1);
v_caption_2919_ = lean_ctor_get(v_msg_2912_, 3);
lean_inc_ref(v_caption_2919_);
v_data_2920_ = lean_ctor_get(v_msg_2912_, 4);
lean_inc_n(v_data_2920_, 2);
lean_dec_ref(v_msg_2912_);
v___x_2921_ = l_Lean_MessageData_toString(v_data_2920_);
v___x_2945_ = l_Lean_MessageData_kind(v_data_2920_);
lean_dec(v_data_2920_);
if (v_includeEndPos_2913_ == 0)
{
lean_object* v___x_2962_; 
lean_dec(v_endPos_2917_);
v___x_2962_ = lean_box(0);
v___y_2956_ = v___x_2962_;
goto v___jp_2955_;
}
else
{
v___y_2956_ = v_endPos_2917_;
goto v___jp_2955_;
}
v___jp_2922_:
{
lean_object* v___x_2924_; lean_object* v_str_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2925_ = lean_string_append(v___y_2923_, v___x_2924_);
return v_str_2925_;
}
v___jp_2926_:
{
uint32_t v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = 10;
v___x_2930_ = lean_uint32_dec_eq(v___y_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
v___y_2923_ = v___y_2927_;
goto v___jp_2922_;
}
else
{
return v___y_2927_;
}
}
v___jp_2931_:
{
uint32_t v___x_2933_; 
v___x_2933_ = 65;
v___y_2927_ = v___y_2932_;
v___y_2928_ = v___x_2933_;
goto v___jp_2926_;
}
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = lean_string_utf8_byte_size(v_str_2935_);
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = lean_nat_dec_eq(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_inc_ref(v_str_2935_);
v___x_2939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2939_, 0, v_str_2935_);
lean_ctor_set(v___x_2939_, 1, v___x_2937_);
lean_ctor_set(v___x_2939_, 2, v___x_2936_);
v___x_2940_ = l_String_Slice_Pos_prev_x3f(v___x_2939_, v___x_2936_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_dec_ref_known(v___x_2939_, 3);
v___y_2932_ = v_str_2935_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2941_; lean_object* v___x_2942_; 
v_val_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_val_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l_String_Slice_Pos_get_x3f(v___x_2939_, v_val_2941_);
lean_dec(v_val_2941_);
lean_dec_ref_known(v___x_2939_, 3);
if (lean_obj_tag(v___x_2942_) == 0)
{
v___y_2932_ = v_str_2935_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2943_; uint32_t v___x_2944_; 
v_val_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_val_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = lean_unbox_uint32(v_val_2943_);
lean_dec(v_val_2943_);
v___y_2927_ = v_str_2935_;
v___y_2928_ = v___x_2944_;
goto v___jp_2926_;
}
}
}
else
{
v___y_2923_ = v_str_2935_;
goto v___jp_2922_;
}
}
v___jp_2946_:
{
switch(v_severity_2918_)
{
case 0:
{
lean_dec(v___y_2947_);
lean_dec(v___x_2945_);
lean_dec_ref(v_pos_2916_);
lean_dec_ref(v_fileName_2915_);
v_str_2935_ = v_str_2948_;
goto v___jp_2934_;
}
case 1:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_str_2951_; 
v___x_2949_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2950_ = l_Lean_errorNameOfKind_x3f(v___x_2945_);
lean_dec(v___x_2945_);
v_str_2951_ = l_Lean_mkErrorStringWithPos(v_fileName_2915_, v_pos_2916_, v_str_2948_, v___y_2947_, v___x_2949_, v___x_2950_);
lean_dec_ref(v_str_2948_);
v_str_2935_ = v_str_2951_;
goto v___jp_2934_;
}
default: 
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_str_2954_; 
v___x_2952_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2953_ = l_Lean_errorNameOfKind_x3f(v___x_2945_);
lean_dec(v___x_2945_);
v_str_2954_ = l_Lean_mkErrorStringWithPos(v_fileName_2915_, v_pos_2916_, v_str_2948_, v___y_2947_, v___x_2952_, v___x_2953_);
lean_dec_ref(v_str_2948_);
v_str_2935_ = v_str_2954_;
goto v___jp_2934_;
}
}
}
v___jp_2955_:
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2958_ = lean_string_dec_eq(v_caption_2919_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_str_2961_; 
v___x_2959_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2960_ = lean_string_append(v_caption_2919_, v___x_2959_);
v_str_2961_ = lean_string_append(v___x_2960_, v___x_2921_);
lean_dec_ref(v___x_2921_);
v___y_2947_ = v___y_2956_;
v_str_2948_ = v_str_2961_;
goto v___jp_2946_;
}
else
{
lean_dec_ref(v_caption_2919_);
v___y_2947_ = v___y_2956_;
v_str_2948_ = v___x_2921_;
goto v___jp_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2963_, lean_object* v_includeEndPos_2964_, lean_object* v_a_2965_){
_start:
{
uint8_t v_includeEndPos_boxed_2966_; lean_object* v_res_2967_; 
v_includeEndPos_boxed_2966_ = lean_unbox(v_includeEndPos_2964_);
v_res_2967_ = l_Lean_Message_toString(v_msg_2963_, v_includeEndPos_boxed_2966_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2968_){
_start:
{
lean_object* v_fileName_2970_; lean_object* v_pos_2971_; lean_object* v_endPos_2972_; uint8_t v_keepFullRange_2973_; uint8_t v_severity_2974_; uint8_t v_isSilent_2975_; lean_object* v_caption_2976_; lean_object* v_data_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_fileName_2970_ = lean_ctor_get(v_msg_2968_, 0);
lean_inc_ref(v_fileName_2970_);
v_pos_2971_ = lean_ctor_get(v_msg_2968_, 1);
lean_inc_ref(v_pos_2971_);
v_endPos_2972_ = lean_ctor_get(v_msg_2968_, 2);
lean_inc(v_endPos_2972_);
v_keepFullRange_2973_ = lean_ctor_get_uint8(v_msg_2968_, sizeof(void*)*5);
v_severity_2974_ = lean_ctor_get_uint8(v_msg_2968_, sizeof(void*)*5 + 1);
v_isSilent_2975_ = lean_ctor_get_uint8(v_msg_2968_, sizeof(void*)*5 + 2);
v_caption_2976_ = lean_ctor_get(v_msg_2968_, 3);
lean_inc_ref(v_caption_2976_);
v_data_2977_ = lean_ctor_get(v_msg_2968_, 4);
lean_inc_n(v_data_2977_, 2);
lean_dec_ref(v_msg_2968_);
v___x_2978_ = l_Lean_MessageData_toString(v_data_2977_);
v___x_2979_ = l_Lean_MessageData_kind(v_data_2977_);
lean_dec(v_data_2977_);
v___x_2980_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_fileName_2970_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2986_ = l_Lean_instToJsonPosition_toJson(v_pos_2971_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2983_);
v___x_2989_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2990_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2972_);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v___x_2983_);
v___x_2993_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2994_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2994_, 0, v_keepFullRange_2973_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2983_);
v___x_2997_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2998_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2974_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
lean_ctor_set(v___x_3000_, 1, v___x_2983_);
v___x_3001_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3002_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3002_, 0, v_isSilent_2975_);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v___x_2983_);
v___x_3005_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_caption_2976_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_2983_);
v___x_3009_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_2978_);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v___x_2983_);
v___x_3013_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3014_ = 1;
v___x_3015_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2979_, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3013_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_2983_);
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_2983_);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3012_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3008_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3004_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3000_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_2996_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_2992_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_2988_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_2984_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3029_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3027_, v___x_3028_);
v___x_3030_ = l_Lean_Json_mkObj(v___x_3029_);
lean_dec(v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Message_toJson(v_msg_3031_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_unsigned_to_nat(32u);
v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3037_ = ((size_t)5ULL);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_unsigned_to_nat(32u);
v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
v___x_3041_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3042_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___x_3040_);
lean_ctor_set(v___x_3042_, 2, v___x_3038_);
lean_ctor_set(v___x_3042_, 3, v___x_3038_);
lean_ctor_set_usize(v___x_3042_, 4, v___x_3037_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = l_Lean_NameSet_empty;
v___x_3044_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
lean_ctor_set(v___x_3045_, 2, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_unsigned_to_nat(32u);
v___x_3049_ = lean_mk_empty_array_with_capacity(v___x_3048_);
lean_dec_ref(v___x_3049_);
v___x_3050_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3051_){
_start:
{
lean_object* v_unreported_3052_; 
v_unreported_3052_ = lean_ctor_get(v_self_3051_, 1);
lean_inc_ref(v_unreported_3052_);
return v_unreported_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_MessageLog_msgs(v_self_3053_);
lean_dec_ref(v_self_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3055_){
_start:
{
lean_object* v_reported_3056_; lean_object* v_unreported_3057_; lean_object* v___x_3058_; 
v_reported_3056_ = lean_ctor_get(v_x_3055_, 0);
lean_inc_ref(v_reported_3056_);
v_unreported_3057_ = lean_ctor_get(v_x_3055_, 1);
lean_inc_ref(v_unreported_3057_);
lean_dec_ref(v_x_3055_);
v___x_3058_ = l_Lean_PersistentArray_append___redArg(v_reported_3056_, v_unreported_3057_);
lean_dec_ref(v_unreported_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3059_){
_start:
{
lean_object* v_unreported_3060_; uint8_t v___x_3061_; 
v_unreported_3060_ = lean_ctor_get(v_log_3059_, 1);
v___x_3061_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3060_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = 1;
return v___x_3062_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = 0;
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3064_){
_start:
{
uint8_t v_res_3065_; lean_object* v_r_3066_; 
v_res_3065_ = l_Lean_MessageLog_hasUnreported(v_log_3064_);
lean_dec_ref(v_log_3064_);
v_r_3066_ = lean_box(v_res_3065_);
return v_r_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3067_, lean_object* v_log_3068_){
_start:
{
lean_object* v_reported_3069_; lean_object* v_unreported_3070_; lean_object* v_loggedKinds_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3079_; 
v_reported_3069_ = lean_ctor_get(v_log_3068_, 0);
v_unreported_3070_ = lean_ctor_get(v_log_3068_, 1);
v_loggedKinds_3071_ = lean_ctor_get(v_log_3068_, 2);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_log_3068_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3073_ = v_log_3068_;
v_isShared_3074_ = v_isSharedCheck_3079_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_loggedKinds_3071_);
lean_inc(v_unreported_3070_);
lean_inc(v_reported_3069_);
lean_dec(v_log_3068_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3079_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3075_ = l_Lean_PersistentArray_push___redArg(v_unreported_3070_, v_msg_3067_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3075_);
v___x_3077_ = v___x_3073_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_reported_3069_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_loggedKinds_3071_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3082_, lean_object* v_x_3083_){
_start:
{
if (lean_obj_tag(v_x_3083_) == 0)
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_b_u2082_3082_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; 
v___x_3085_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3086_, lean_object* v_x_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3086_, v_x_3087_);
lean_dec(v_x_3087_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3089_, lean_object* v_k_3090_, lean_object* v_t_3091_){
_start:
{
if (lean_obj_tag(v_t_3091_) == 0)
{
lean_object* v_size_3092_; lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3111_; 
v_size_3092_ = lean_ctor_get(v_t_3091_, 0);
v_k_3093_ = lean_ctor_get(v_t_3091_, 1);
v_v_3094_ = lean_ctor_get(v_t_3091_, 2);
v_l_3095_ = lean_ctor_get(v_t_3091_, 3);
v_r_3096_ = lean_ctor_get(v_t_3091_, 4);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_t_3091_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3098_ = v_t_3091_;
v_isShared_3099_ = v_isSharedCheck_3111_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_r_3096_);
lean_inc(v_l_3095_);
lean_inc(v_v_3094_);
lean_inc(v_k_3093_);
lean_inc(v_size_3092_);
lean_dec(v_t_3091_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3111_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint8_t v___x_3100_; 
v___x_3100_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3090_, v_k_3093_);
switch(v___x_3100_)
{
case 0:
{
lean_object* v_impl_3101_; lean_object* v___x_3102_; 
lean_del_object(v___x_3098_);
lean_dec(v_size_3092_);
v_impl_3101_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3089_, v_k_3090_, v_l_3095_);
v___x_3102_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3093_, v_v_3094_, v_impl_3101_, v_r_3096_);
return v___x_3102_;
}
case 1:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v_val_3105_; lean_object* v___x_3107_; 
lean_dec(v_k_3093_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_v_3094_);
v___x_3104_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3089_, v___x_3103_);
lean_dec_ref_known(v___x_3103_, 1);
v_val_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3105_);
lean_dec(v___x_3104_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 2, v_val_3105_);
lean_ctor_set(v___x_3098_, 1, v_k_3090_);
v___x_3107_ = v___x_3098_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_size_3092_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_k_3090_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_val_3105_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_l_3095_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_r_3096_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
default: 
{
lean_object* v_impl_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3098_);
lean_dec(v_size_3092_);
v_impl_3109_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3089_, v_k_3090_, v_r_3096_);
v___x_3110_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3093_, v_v_3094_, v_l_3095_, v_impl_3109_);
return v___x_3110_;
}
}
}
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_val_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3112_ = lean_box(0);
v___x_3113_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3089_, v___x_3112_);
v_val_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_val_3114_);
lean_dec(v___x_3113_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v_k_3090_);
lean_ctor_set(v___x_3116_, 2, v_val_3114_);
lean_ctor_set(v___x_3116_, 3, v_t_3091_);
lean_ctor_set(v___x_3116_, 4, v_t_3091_);
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3117_, lean_object* v_x_3118_){
_start:
{
if (lean_obj_tag(v_x_3118_) == 0)
{
lean_object* v_k_3119_; lean_object* v_v_3120_; lean_object* v_l_3121_; lean_object* v_r_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_k_3119_ = lean_ctor_get(v_x_3118_, 1);
lean_inc(v_k_3119_);
v_v_3120_ = lean_ctor_get(v_x_3118_, 2);
lean_inc(v_v_3120_);
v_l_3121_ = lean_ctor_get(v_x_3118_, 3);
lean_inc(v_l_3121_);
v_r_3122_ = lean_ctor_get(v_x_3118_, 4);
lean_inc(v_r_3122_);
lean_dec_ref_known(v_x_3118_, 5);
v___x_3123_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3117_, v_l_3121_);
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3120_, v_k_3119_, v___x_3123_);
v_init_3117_ = v___x_3124_;
v_x_3118_ = v_r_3122_;
goto _start;
}
else
{
return v_init_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3126_, lean_object* v_l_u2082_3127_){
_start:
{
lean_object* v_reported_3128_; lean_object* v_unreported_3129_; lean_object* v_loggedKinds_3130_; lean_object* v_reported_3131_; lean_object* v_unreported_3132_; lean_object* v_loggedKinds_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3143_; 
v_reported_3128_ = lean_ctor_get(v_l_u2081_3126_, 0);
lean_inc_ref(v_reported_3128_);
v_unreported_3129_ = lean_ctor_get(v_l_u2081_3126_, 1);
lean_inc_ref(v_unreported_3129_);
v_loggedKinds_3130_ = lean_ctor_get(v_l_u2081_3126_, 2);
lean_inc(v_loggedKinds_3130_);
lean_dec_ref(v_l_u2081_3126_);
v_reported_3131_ = lean_ctor_get(v_l_u2082_3127_, 0);
v_unreported_3132_ = lean_ctor_get(v_l_u2082_3127_, 1);
v_loggedKinds_3133_ = lean_ctor_get(v_l_u2082_3127_, 2);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_l_u2082_3127_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3135_ = v_l_u2082_3127_;
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_loggedKinds_3133_);
lean_inc(v_unreported_3132_);
lean_inc(v_reported_3131_);
lean_dec(v_l_u2082_3127_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3137_ = l_Lean_PersistentArray_append___redArg(v_reported_3128_, v_reported_3131_);
lean_dec_ref(v_reported_3131_);
v___x_3138_ = l_Lean_PersistentArray_append___redArg(v_unreported_3129_, v_unreported_3132_);
lean_dec_ref(v_unreported_3132_);
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3130_, v_loggedKinds_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 2, v___x_3139_);
lean_ctor_set(v___x_3135_, 1, v___x_3138_);
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3141_ = v___x_3135_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3144_, lean_object* v_k_3145_, lean_object* v_t_3146_, lean_object* v_hl_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3144_, v_k_3145_, v_t_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3149_, lean_object* v_t_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3149_, v_t_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3154_, size_t v_i_3155_, size_t v_stop_3156_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_usize_dec_eq(v_i_3155_, v_stop_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; uint8_t v_severity_3159_; 
v___x_3158_ = lean_array_uget_borrowed(v_as_3154_, v_i_3155_);
v_severity_3159_ = lean_ctor_get_uint8(v___x_3158_, sizeof(void*)*5 + 1);
if (v_severity_3159_ == 2)
{
uint8_t v___x_3160_; 
v___x_3160_ = 1;
return v___x_3160_;
}
else
{
size_t v___x_3161_; size_t v___x_3162_; 
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3155_, v___x_3161_);
v_i_3155_ = v___x_3162_;
goto _start;
}
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = 0;
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3165_, lean_object* v_i_3166_, lean_object* v_stop_3167_){
_start:
{
size_t v_i_boxed_3168_; size_t v_stop_boxed_3169_; uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_i_boxed_3168_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_stop_boxed_3169_ = lean_unbox_usize(v_stop_3167_);
lean_dec(v_stop_3167_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3165_, v_i_boxed_3168_, v_stop_boxed_3169_);
lean_dec_ref(v_as_3165_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 0)
{
lean_object* v_cs_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_cs_3173_ = lean_ctor_get(v_x_3172_, 0);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_array_get_size(v_cs_3173_);
v___x_3176_ = lean_nat_dec_lt(v___x_3174_, v___x_3175_);
if (v___x_3176_ == 0)
{
return v___x_3176_;
}
else
{
size_t v___x_3177_; size_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = lean_usize_of_nat(v___x_3175_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3173_, v___x_3177_, v___x_3178_);
return v___x_3179_;
}
}
else
{
lean_object* v_vs_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_vs_3180_ = lean_ctor_get(v_x_3172_, 0);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = lean_array_get_size(v_vs_3180_);
v___x_3183_ = lean_nat_dec_lt(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
return v___x_3183_;
}
else
{
size_t v___x_3184_; size_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = lean_usize_of_nat(v___x_3182_);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3180_, v___x_3184_, v___x_3185_);
return v___x_3186_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3187_, size_t v_i_3188_, size_t v_stop_3189_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_usize_dec_eq(v_i_3188_, v_stop_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = lean_array_uget_borrowed(v_as_3187_, v_i_3188_);
v___x_3192_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3191_);
if (v___x_3192_ == 0)
{
size_t v___x_3193_; size_t v___x_3194_; 
v___x_3193_ = ((size_t)1ULL);
v___x_3194_ = lean_usize_add(v_i_3188_, v___x_3193_);
v_i_3188_ = v___x_3194_;
goto _start;
}
else
{
return v___x_3192_;
}
}
else
{
uint8_t v___x_3196_; 
v___x_3196_ = 0;
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3197_, lean_object* v_i_3198_, lean_object* v_stop_3199_){
_start:
{
size_t v_i_boxed_3200_; size_t v_stop_boxed_3201_; uint8_t v_res_3202_; lean_object* v_r_3203_; 
v_i_boxed_3200_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_stop_boxed_3201_ = lean_unbox_usize(v_stop_3199_);
lean_dec(v_stop_3199_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3197_, v_i_boxed_3200_, v_stop_boxed_3201_);
lean_dec_ref(v_as_3197_);
v_r_3203_ = lean_box(v_res_3202_);
return v_r_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3204_);
lean_dec_ref(v_x_3204_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3207_){
_start:
{
lean_object* v_root_3208_; lean_object* v_tail_3209_; uint8_t v___x_3210_; 
v_root_3208_ = lean_ctor_get(v_t_3207_, 0);
v_tail_3209_ = lean_ctor_get(v_t_3207_, 1);
v___x_3210_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3208_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_array_get_size(v_tail_3209_);
v___x_3213_ = lean_nat_dec_lt(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
return v___x_3213_;
}
else
{
size_t v___x_3214_; size_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3214_ = ((size_t)0ULL);
v___x_3215_ = lean_usize_of_nat(v___x_3212_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3209_, v___x_3214_, v___x_3215_);
return v___x_3216_;
}
}
else
{
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3217_);
lean_dec_ref(v_t_3217_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3220_, lean_object* v_as_3221_, size_t v_i_3222_, size_t v_stop_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_eq(v_i_3222_, v_stop_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; uint8_t v_severity_3226_; uint8_t v___x_3227_; 
v___x_3225_ = lean_array_uget_borrowed(v_as_3221_, v_i_3222_);
v_severity_3226_ = lean_ctor_get_uint8(v___x_3225_, sizeof(void*)*5 + 1);
v___x_3227_ = 1;
if (v_severity_3226_ == 2)
{
return v___x_3227_;
}
else
{
if (v___x_3220_ == 0)
{
size_t v___x_3228_; size_t v___x_3229_; 
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3222_, v___x_3228_);
v_i_3222_ = v___x_3229_;
goto _start;
}
else
{
return v___x_3227_;
}
}
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = 0;
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3232_, lean_object* v_as_3233_, lean_object* v_i_3234_, lean_object* v_stop_3235_){
_start:
{
uint8_t v___x_1809__boxed_3236_; size_t v_i_boxed_3237_; size_t v_stop_boxed_3238_; uint8_t v_res_3239_; lean_object* v_r_3240_; 
v___x_1809__boxed_3236_ = lean_unbox(v___x_3232_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3234_);
lean_dec(v_i_3234_);
v_stop_boxed_3238_ = lean_unbox_usize(v_stop_3235_);
lean_dec(v_stop_3235_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3236_, v_as_3233_, v_i_boxed_3237_, v_stop_boxed_3238_);
lean_dec_ref(v_as_3233_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3241_, lean_object* v_x_3242_){
_start:
{
if (lean_obj_tag(v_x_3242_) == 0)
{
lean_object* v_cs_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
v_cs_3243_ = lean_ctor_get(v_x_3242_, 0);
v___x_3244_ = lean_unsigned_to_nat(0u);
v___x_3245_ = lean_array_get_size(v_cs_3243_);
v___x_3246_ = lean_nat_dec_lt(v___x_3244_, v___x_3245_);
if (v___x_3246_ == 0)
{
return v___x_3246_;
}
else
{
size_t v___x_3247_; size_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3247_ = ((size_t)0ULL);
v___x_3248_ = lean_usize_of_nat(v___x_3245_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3241_, v_cs_3243_, v___x_3247_, v___x_3248_);
return v___x_3249_;
}
}
else
{
lean_object* v_vs_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v_vs_3250_ = lean_ctor_get(v_x_3242_, 0);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_array_get_size(v_vs_3250_);
v___x_3253_ = lean_nat_dec_lt(v___x_3251_, v___x_3252_);
if (v___x_3253_ == 0)
{
return v___x_3253_;
}
else
{
size_t v___x_3254_; size_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = lean_usize_of_nat(v___x_3252_);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3241_, v_vs_3250_, v___x_3254_, v___x_3255_);
return v___x_3256_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3257_, lean_object* v_as_3258_, size_t v_i_3259_, size_t v_stop_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_usize_dec_eq(v_i_3259_, v_stop_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = lean_array_uget_borrowed(v_as_3258_, v_i_3259_);
v___x_3263_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3257_, v___x_3262_);
if (v___x_3263_ == 0)
{
size_t v___x_3264_; size_t v___x_3265_; 
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3259_, v___x_3264_);
v_i_3259_ = v___x_3265_;
goto _start;
}
else
{
return v___x_3263_;
}
}
else
{
uint8_t v___x_3267_; 
v___x_3267_ = 0;
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3268_, lean_object* v_as_3269_, lean_object* v_i_3270_, lean_object* v_stop_3271_){
_start:
{
uint8_t v___x_1826__boxed_3272_; size_t v_i_boxed_3273_; size_t v_stop_boxed_3274_; uint8_t v_res_3275_; lean_object* v_r_3276_; 
v___x_1826__boxed_3272_ = lean_unbox(v___x_3268_);
v_i_boxed_3273_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_stop_boxed_3274_ = lean_unbox_usize(v_stop_3271_);
lean_dec(v_stop_3271_);
v_res_3275_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3272_, v_as_3269_, v_i_boxed_3273_, v_stop_boxed_3274_);
lean_dec_ref(v_as_3269_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3277_, lean_object* v_x_3278_){
_start:
{
uint8_t v___x_1834__boxed_3279_; uint8_t v_res_3280_; lean_object* v_r_3281_; 
v___x_1834__boxed_3279_ = lean_unbox(v___x_3277_);
v_res_3280_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3279_, v_x_3278_);
lean_dec_ref(v_x_3278_);
v_r_3281_ = lean_box(v_res_3280_);
return v_r_3281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3282_, lean_object* v_t_3283_){
_start:
{
lean_object* v_root_3284_; lean_object* v_tail_3285_; uint8_t v___x_3286_; 
v_root_3284_ = lean_ctor_get(v_t_3283_, 0);
v_tail_3285_ = lean_ctor_get(v_t_3283_, 1);
v___x_3286_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3282_, v_root_3284_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_array_get_size(v_tail_3285_);
v___x_3289_ = lean_nat_dec_lt(v___x_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
return v___x_3289_;
}
else
{
size_t v___x_3290_; size_t v___x_3291_; uint8_t v___x_3292_; 
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3288_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3282_, v_tail_3285_, v___x_3290_, v___x_3291_);
return v___x_3292_;
}
}
else
{
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3293_, lean_object* v_t_3294_){
_start:
{
uint8_t v___x_1877__boxed_3295_; uint8_t v_res_3296_; lean_object* v_r_3297_; 
v___x_1877__boxed_3295_ = lean_unbox(v___x_3293_);
v_res_3296_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3295_, v_t_3294_);
lean_dec_ref(v_t_3294_);
v_r_3297_ = lean_box(v_res_3296_);
return v_r_3297_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3298_){
_start:
{
lean_object* v_reported_3299_; lean_object* v_unreported_3300_; uint8_t v___x_3301_; 
v_reported_3299_ = lean_ctor_get(v_log_3298_, 0);
v_unreported_3300_ = lean_ctor_get(v_log_3298_, 1);
v___x_3301_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3299_);
if (v___x_3301_ == 0)
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3301_, v_unreported_3300_);
return v___x_3302_;
}
else
{
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3303_){
_start:
{
uint8_t v_res_3304_; lean_object* v_r_3305_; 
v_res_3304_ = l_Lean_MessageLog_hasErrors(v_log_3303_);
lean_dec_ref(v_log_3303_);
v_r_3305_ = lean_box(v_res_3304_);
return v_r_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3306_){
_start:
{
lean_object* v_reported_3307_; lean_object* v_unreported_3308_; lean_object* v_loggedKinds_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3320_; 
v_reported_3307_ = lean_ctor_get(v_log_3306_, 0);
v_unreported_3308_ = lean_ctor_get(v_log_3306_, 1);
v_loggedKinds_3309_ = lean_ctor_get(v_log_3306_, 2);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_log_3306_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3311_ = v_log_3306_;
v_isShared_3312_ = v_isSharedCheck_3320_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_loggedKinds_3309_);
lean_inc(v_unreported_3308_);
lean_inc(v_reported_3307_);
lean_dec(v_log_3306_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3320_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3313_ = l_Lean_PersistentArray_append___redArg(v_reported_3307_, v_unreported_3308_);
lean_dec_ref(v_unreported_3308_);
v___x_3314_ = lean_unsigned_to_nat(32u);
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_3314_);
lean_dec_ref(v___x_3315_);
v___x_3316_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v___x_3316_);
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3318_ = v___x_3311_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_loggedKinds_3309_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3321_, size_t v_i_3322_, lean_object* v_bs_3323_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_usize_dec_lt(v_i_3322_, v_sz_3321_);
if (v___x_3324_ == 0)
{
return v_bs_3323_;
}
else
{
lean_object* v_v_3325_; lean_object* v_fileName_3326_; lean_object* v_pos_3327_; lean_object* v_endPos_3328_; uint8_t v_keepFullRange_3329_; uint8_t v_severity_3330_; uint8_t v_isSilent_3331_; lean_object* v_caption_3332_; lean_object* v_data_3333_; lean_object* v___x_3334_; lean_object* v_bs_x27_3335_; lean_object* v___y_3337_; 
v_v_3325_ = lean_array_uget(v_bs_3323_, v_i_3322_);
v_fileName_3326_ = lean_ctor_get(v_v_3325_, 0);
v_pos_3327_ = lean_ctor_get(v_v_3325_, 1);
v_endPos_3328_ = lean_ctor_get(v_v_3325_, 2);
v_keepFullRange_3329_ = lean_ctor_get_uint8(v_v_3325_, sizeof(void*)*5);
v_severity_3330_ = lean_ctor_get_uint8(v_v_3325_, sizeof(void*)*5 + 1);
v_isSilent_3331_ = lean_ctor_get_uint8(v_v_3325_, sizeof(void*)*5 + 2);
v_caption_3332_ = lean_ctor_get(v_v_3325_, 3);
v_data_3333_ = lean_ctor_get(v_v_3325_, 4);
v___x_3334_ = lean_unsigned_to_nat(0u);
v_bs_x27_3335_ = lean_array_uset(v_bs_3323_, v_i_3322_, v___x_3334_);
if (v_severity_3330_ == 2)
{
lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3349_; 
lean_inc(v_data_3333_);
lean_inc_ref(v_caption_3332_);
lean_inc(v_endPos_3328_);
lean_inc_ref(v_pos_3327_);
lean_inc_ref(v_fileName_3326_);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_v_3325_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; lean_object* v_unused_3351_; lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3350_ = lean_ctor_get(v_v_3325_, 4);
lean_dec(v_unused_3350_);
v_unused_3351_ = lean_ctor_get(v_v_3325_, 3);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_v_3325_, 2);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_v_3325_, 1);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_v_3325_, 0);
lean_dec(v_unused_3354_);
v___x_3343_ = v_v_3325_;
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
else
{
lean_dec(v_v_3325_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3349_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
uint8_t v___x_3345_; lean_object* v___x_3347_; 
v___x_3345_ = 1;
if (v_isShared_3344_ == 0)
{
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_fileName_3326_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_pos_3327_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_endPos_3328_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_caption_3332_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_data_3333_);
lean_ctor_set_uint8(v_reuseFailAlloc_3348_, sizeof(void*)*5, v_keepFullRange_3329_);
lean_ctor_set_uint8(v_reuseFailAlloc_3348_, sizeof(void*)*5 + 2, v_isSilent_3331_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*5 + 1, v___x_3345_);
v___y_3337_ = v___x_3347_;
goto v___jp_3336_;
}
}
}
else
{
v___y_3337_ = v_v_3325_;
goto v___jp_3336_;
}
v___jp_3336_:
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3322_, v___x_3338_);
v___x_3340_ = lean_array_uset(v_bs_x27_3335_, v_i_3322_, v___y_3337_);
v_i_3322_ = v___x_3339_;
v_bs_3323_ = v___x_3340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3355_, lean_object* v_i_3356_, lean_object* v_bs_3357_){
_start:
{
size_t v_sz_boxed_3358_; size_t v_i_boxed_3359_; lean_object* v_res_3360_; 
v_sz_boxed_3358_ = lean_unbox_usize(v_sz_3355_);
lean_dec(v_sz_3355_);
v_i_boxed_3359_ = lean_unbox_usize(v_i_3356_);
lean_dec(v_i_3356_);
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3358_, v_i_boxed_3359_, v_bs_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3361_, size_t v_i_3362_, lean_object* v_bs_3363_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_lt(v_i_3362_, v_sz_3361_);
if (v___x_3364_ == 0)
{
return v_bs_3363_;
}
else
{
lean_object* v_v_3365_; lean_object* v___x_3366_; lean_object* v_bs_x27_3367_; lean_object* v___x_3368_; size_t v___x_3369_; size_t v___x_3370_; lean_object* v___x_3371_; 
v_v_3365_ = lean_array_uget(v_bs_3363_, v_i_3362_);
v___x_3366_ = lean_unsigned_to_nat(0u);
v_bs_x27_3367_ = lean_array_uset(v_bs_3363_, v_i_3362_, v___x_3366_);
v___x_3368_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3365_);
v___x_3369_ = ((size_t)1ULL);
v___x_3370_ = lean_usize_add(v_i_3362_, v___x_3369_);
v___x_3371_ = lean_array_uset(v_bs_x27_3367_, v_i_3362_, v___x_3368_);
v_i_3362_ = v___x_3370_;
v_bs_3363_ = v___x_3371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3373_){
_start:
{
if (lean_obj_tag(v_x_3373_) == 0)
{
lean_object* v_cs_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3384_; 
v_cs_3374_ = lean_ctor_get(v_x_3373_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_x_3373_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3376_ = v_x_3373_;
v_isShared_3377_ = v_isSharedCheck_3384_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_cs_3374_);
lean_dec(v_x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3384_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
size_t v_sz_3378_; size_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v_sz_3378_ = lean_array_size(v_cs_3374_);
v___x_3379_ = ((size_t)0ULL);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3378_, v___x_3379_, v_cs_3374_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3380_);
v___x_3382_ = v___x_3376_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_vs_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3395_; 
v_vs_3385_ = lean_ctor_get(v_x_3373_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_x_3373_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3387_ = v_x_3373_;
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_vs_3385_);
lean_dec(v_x_3373_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
size_t v_sz_3389_; size_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v_sz_3389_ = lean_array_size(v_vs_3385_);
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3389_, v___x_3390_, v_vs_3385_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3391_);
v___x_3393_ = v___x_3387_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_bs_3398_){
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3399_, v_i_boxed_3400_, v_bs_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3402_){
_start:
{
lean_object* v_root_3403_; lean_object* v_tail_3404_; lean_object* v_size_3405_; size_t v_shift_3406_; lean_object* v_tailOff_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3418_; 
v_root_3403_ = lean_ctor_get(v_t_3402_, 0);
v_tail_3404_ = lean_ctor_get(v_t_3402_, 1);
v_size_3405_ = lean_ctor_get(v_t_3402_, 2);
v_shift_3406_ = lean_ctor_get_usize(v_t_3402_, 4);
v_tailOff_3407_ = lean_ctor_get(v_t_3402_, 3);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_t_3402_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3409_ = v_t_3402_;
v_isShared_3410_ = v_isSharedCheck_3418_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_tailOff_3407_);
lean_inc(v_size_3405_);
lean_inc(v_tail_3404_);
lean_inc(v_root_3403_);
lean_dec(v_t_3402_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3418_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; size_t v_sz_3412_; size_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3411_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3403_);
v_sz_3412_ = lean_array_size(v_tail_3404_);
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3412_, v___x_3413_, v_tail_3404_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 1, v___x_3414_);
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3416_ = v___x_3409_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_size_3405_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_tailOff_3407_);
lean_ctor_set_usize(v_reuseFailAlloc_3417_, 4, v_shift_3406_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3419_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v_unreported_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3432_; 
v___x_3420_ = lean_unsigned_to_nat(32u);
v___x_3421_ = lean_mk_empty_array_with_capacity(v___x_3420_);
lean_dec_ref(v___x_3421_);
v___x_3422_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3423_ = lean_ctor_get(v_log_3419_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_log_3419_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; 
v_unused_3433_ = lean_ctor_get(v_log_3419_, 2);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v_log_3419_, 0);
lean_dec(v_unused_3434_);
v___x_3425_ = v_log_3419_;
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_unreported_3423_);
lean_dec(v_log_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3427_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3423_);
v___x_3428_ = l_Lean_NameSet_empty;
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 2, v___x_3428_);
lean_ctor_set(v___x_3425_, 1, v___x_3427_);
lean_ctor_set(v___x_3425_, 0, v___x_3422_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3435_, size_t v_i_3436_, lean_object* v_bs_3437_){
_start:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_usize_dec_lt(v_i_3436_, v_sz_3435_);
if (v___x_3438_ == 0)
{
return v_bs_3437_;
}
else
{
lean_object* v_v_3439_; lean_object* v_fileName_3440_; lean_object* v_pos_3441_; lean_object* v_endPos_3442_; uint8_t v_keepFullRange_3443_; uint8_t v_severity_3444_; uint8_t v_isSilent_3445_; lean_object* v_caption_3446_; lean_object* v_data_3447_; lean_object* v___x_3448_; lean_object* v_bs_x27_3449_; lean_object* v___y_3451_; 
v_v_3439_ = lean_array_uget(v_bs_3437_, v_i_3436_);
v_fileName_3440_ = lean_ctor_get(v_v_3439_, 0);
v_pos_3441_ = lean_ctor_get(v_v_3439_, 1);
v_endPos_3442_ = lean_ctor_get(v_v_3439_, 2);
v_keepFullRange_3443_ = lean_ctor_get_uint8(v_v_3439_, sizeof(void*)*5);
v_severity_3444_ = lean_ctor_get_uint8(v_v_3439_, sizeof(void*)*5 + 1);
v_isSilent_3445_ = lean_ctor_get_uint8(v_v_3439_, sizeof(void*)*5 + 2);
v_caption_3446_ = lean_ctor_get(v_v_3439_, 3);
v_data_3447_ = lean_ctor_get(v_v_3439_, 4);
v___x_3448_ = lean_unsigned_to_nat(0u);
v_bs_x27_3449_ = lean_array_uset(v_bs_3437_, v_i_3436_, v___x_3448_);
if (v_severity_3444_ == 2)
{
lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3463_; 
lean_inc(v_data_3447_);
lean_inc_ref(v_caption_3446_);
lean_inc(v_endPos_3442_);
lean_inc_ref(v_pos_3441_);
lean_inc_ref(v_fileName_3440_);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_v_3439_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; lean_object* v_unused_3465_; lean_object* v_unused_3466_; lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3464_ = lean_ctor_get(v_v_3439_, 4);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v_v_3439_, 3);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_v_3439_, 2);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_v_3439_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_v_3439_, 0);
lean_dec(v_unused_3468_);
v___x_3457_ = v_v_3439_;
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
else
{
lean_dec(v_v_3439_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3463_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
uint8_t v___x_3459_; lean_object* v___x_3461_; 
v___x_3459_ = 0;
if (v_isShared_3458_ == 0)
{
v___x_3461_ = v___x_3457_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fileName_3440_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_pos_3441_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_endPos_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_caption_3446_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_data_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3462_, sizeof(void*)*5, v_keepFullRange_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3462_, sizeof(void*)*5 + 2, v_isSilent_3445_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*5 + 1, v___x_3459_);
v___y_3451_ = v___x_3461_;
goto v___jp_3450_;
}
}
}
else
{
v___y_3451_ = v_v_3439_;
goto v___jp_3450_;
}
v___jp_3450_:
{
size_t v___x_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = ((size_t)1ULL);
v___x_3453_ = lean_usize_add(v_i_3436_, v___x_3452_);
v___x_3454_ = lean_array_uset(v_bs_x27_3449_, v_i_3436_, v___y_3451_);
v_i_3436_ = v___x_3453_;
v_bs_3437_ = v___x_3454_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3469_, lean_object* v_i_3470_, lean_object* v_bs_3471_){
_start:
{
size_t v_sz_boxed_3472_; size_t v_i_boxed_3473_; lean_object* v_res_3474_; 
v_sz_boxed_3472_ = lean_unbox_usize(v_sz_3469_);
lean_dec(v_sz_3469_);
v_i_boxed_3473_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3472_, v_i_boxed_3473_, v_bs_3471_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3475_, size_t v_i_3476_, lean_object* v_bs_3477_){
_start:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_usize_dec_lt(v_i_3476_, v_sz_3475_);
if (v___x_3478_ == 0)
{
return v_bs_3477_;
}
else
{
lean_object* v_v_3479_; lean_object* v___x_3480_; lean_object* v_bs_x27_3481_; lean_object* v___x_3482_; size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v_v_3479_ = lean_array_uget(v_bs_3477_, v_i_3476_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v_bs_x27_3481_ = lean_array_uset(v_bs_3477_, v_i_3476_, v___x_3480_);
v___x_3482_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3479_);
v___x_3483_ = ((size_t)1ULL);
v___x_3484_ = lean_usize_add(v_i_3476_, v___x_3483_);
v___x_3485_ = lean_array_uset(v_bs_x27_3481_, v_i_3476_, v___x_3482_);
v_i_3476_ = v___x_3484_;
v_bs_3477_ = v___x_3485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 0)
{
lean_object* v_cs_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3498_; 
v_cs_3488_ = lean_ctor_get(v_x_3487_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_x_3487_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3490_ = v_x_3487_;
v_isShared_3491_ = v_isSharedCheck_3498_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_cs_3488_);
lean_dec(v_x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3498_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
size_t v_sz_3492_; size_t v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v_sz_3492_ = lean_array_size(v_cs_3488_);
v___x_3493_ = ((size_t)0ULL);
v___x_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3492_, v___x_3493_, v_cs_3488_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3494_);
v___x_3496_ = v___x_3490_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
else
{
lean_object* v_vs_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3509_; 
v_vs_3499_ = lean_ctor_get(v_x_3487_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_x_3487_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3501_ = v_x_3487_;
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_vs_3499_);
lean_dec(v_x_3487_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
size_t v_sz_3503_; size_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3507_; 
v_sz_3503_ = lean_array_size(v_vs_3499_);
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3503_, v___x_3504_, v_vs_3499_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3505_);
v___x_3507_ = v___x_3501_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_bs_3512_){
_start:
{
size_t v_sz_boxed_3513_; size_t v_i_boxed_3514_; lean_object* v_res_3515_; 
v_sz_boxed_3513_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3514_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3513_, v_i_boxed_3514_, v_bs_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3516_){
_start:
{
lean_object* v_root_3517_; lean_object* v_tail_3518_; lean_object* v_size_3519_; size_t v_shift_3520_; lean_object* v_tailOff_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3532_; 
v_root_3517_ = lean_ctor_get(v_t_3516_, 0);
v_tail_3518_ = lean_ctor_get(v_t_3516_, 1);
v_size_3519_ = lean_ctor_get(v_t_3516_, 2);
v_shift_3520_ = lean_ctor_get_usize(v_t_3516_, 4);
v_tailOff_3521_ = lean_ctor_get(v_t_3516_, 3);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_t_3516_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3523_ = v_t_3516_;
v_isShared_3524_ = v_isSharedCheck_3532_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_tailOff_3521_);
lean_inc(v_size_3519_);
lean_inc(v_tail_3518_);
lean_inc(v_root_3517_);
lean_dec(v_t_3516_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3532_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; size_t v_sz_3526_; size_t v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3525_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3517_);
v_sz_3526_ = lean_array_size(v_tail_3518_);
v___x_3527_ = ((size_t)0ULL);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3526_, v___x_3527_, v_tail_3518_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v___x_3528_);
lean_ctor_set(v___x_3523_, 0, v___x_3525_);
v___x_3530_ = v___x_3523_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_size_3519_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_tailOff_3521_);
lean_ctor_set_usize(v_reuseFailAlloc_3531_, 4, v_shift_3520_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v_unreported_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3546_; 
v___x_3534_ = lean_unsigned_to_nat(32u);
v___x_3535_ = lean_mk_empty_array_with_capacity(v___x_3534_);
lean_dec_ref(v___x_3535_);
v___x_3536_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3537_ = lean_ctor_get(v_log_3533_, 1);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_log_3533_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; 
v_unused_3547_ = lean_ctor_get(v_log_3533_, 2);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_log_3533_, 0);
lean_dec(v_unused_3548_);
v___x_3539_ = v_log_3533_;
v_isShared_3540_ = v_isSharedCheck_3546_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_unreported_3537_);
lean_dec(v_log_3533_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3546_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3541_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3537_);
v___x_3542_ = l_Lean_NameSet_empty;
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 2, v___x_3542_);
lean_ctor_set(v___x_3539_, 1, v___x_3541_);
lean_ctor_set(v___x_3539_, 0, v___x_3536_);
v___x_3544_ = v___x_3539_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3549_, size_t v_i_3550_, size_t v_stop_3551_, lean_object* v_b_3552_){
_start:
{
lean_object* v___y_3554_; uint8_t v___x_3558_; 
v___x_3558_ = lean_usize_dec_eq(v_i_3550_, v_stop_3551_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; uint8_t v_severity_3560_; 
v___x_3559_ = lean_array_uget_borrowed(v_as_3549_, v_i_3550_);
v_severity_3560_ = lean_ctor_get_uint8(v___x_3559_, sizeof(void*)*5 + 1);
if (v_severity_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_inc(v___x_3559_);
v___x_3561_ = l_Lean_PersistentArray_push___redArg(v_b_3552_, v___x_3559_);
v___y_3554_ = v___x_3561_;
goto v___jp_3553_;
}
else
{
v___y_3554_ = v_b_3552_;
goto v___jp_3553_;
}
}
else
{
return v_b_3552_;
}
v___jp_3553_:
{
size_t v___x_3555_; size_t v___x_3556_; 
v___x_3555_ = ((size_t)1ULL);
v___x_3556_ = lean_usize_add(v_i_3550_, v___x_3555_);
v_i_3550_ = v___x_3556_;
v_b_3552_ = v___y_3554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3562_, lean_object* v_i_3563_, lean_object* v_stop_3564_, lean_object* v_b_3565_){
_start:
{
size_t v_i_boxed_3566_; size_t v_stop_boxed_3567_; lean_object* v_res_3568_; 
v_i_boxed_3566_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_stop_boxed_3567_ = lean_unbox_usize(v_stop_3564_);
lean_dec(v_stop_3564_);
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3562_, v_i_boxed_3566_, v_stop_boxed_3567_, v_b_3565_);
lean_dec_ref(v_as_3562_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_object* v_cs_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_cs_3571_ = lean_ctor_get(v_x_3569_, 0);
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3573_ = lean_array_get_size(v_cs_3571_);
v___x_3574_ = lean_nat_dec_lt(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
return v_x_3570_;
}
else
{
size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = lean_usize_of_nat(v___x_3573_);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3571_, v___x_3575_, v___x_3576_, v_x_3570_);
return v___x_3577_;
}
}
else
{
lean_object* v_vs_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v_vs_3578_ = lean_ctor_get(v_x_3569_, 0);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = lean_array_get_size(v_vs_3578_);
v___x_3581_ = lean_nat_dec_lt(v___x_3579_, v___x_3580_);
if (v___x_3581_ == 0)
{
return v_x_3570_;
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3580_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3578_, v___x_3582_, v___x_3583_, v_x_3570_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3585_, size_t v_i_3586_, size_t v_stop_3587_, lean_object* v_b_3588_){
_start:
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_usize_dec_eq(v_i_3586_, v_stop_3587_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; size_t v___x_3592_; size_t v___x_3593_; 
v___x_3590_ = lean_array_uget_borrowed(v_as_3585_, v_i_3586_);
v___x_3591_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3590_, v_b_3588_);
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3586_, v___x_3592_);
v_i_3586_ = v___x_3593_;
v_b_3588_ = v___x_3591_;
goto _start;
}
else
{
return v_b_3588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3595_, lean_object* v_i_3596_, lean_object* v_stop_3597_, lean_object* v_b_3598_){
_start:
{
size_t v_i_boxed_3599_; size_t v_stop_boxed_3600_; lean_object* v_res_3601_; 
v_i_boxed_3599_ = lean_unbox_usize(v_i_3596_);
lean_dec(v_i_3596_);
v_stop_boxed_3600_ = lean_unbox_usize(v_stop_3597_);
lean_dec(v_stop_3597_);
v_res_3601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3595_, v_i_boxed_3599_, v_stop_boxed_3600_, v_b_3598_);
lean_dec_ref(v_as_3595_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3602_, v_x_3603_);
lean_dec_ref(v_x_3602_);
return v_res_3604_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3606_, size_t v_x_3607_, size_t v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
lean_object* v_cs_3610_; lean_object* v___x_3611_; size_t v___x_3612_; lean_object* v_j_3613_; lean_object* v___x_3614_; size_t v___x_3615_; size_t v___x_3616_; size_t v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_cs_3610_ = lean_ctor_get(v_x_3606_, 0);
v___x_3611_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3612_ = lean_usize_shift_right(v_x_3607_, v_x_3608_);
v_j_3613_ = lean_usize_to_nat(v___x_3612_);
v___x_3614_ = lean_array_get_borrowed(v___x_3611_, v_cs_3610_, v_j_3613_);
v___x_3615_ = ((size_t)1ULL);
v___x_3616_ = lean_usize_shift_left(v___x_3615_, v_x_3608_);
v___x_3617_ = lean_usize_sub(v___x_3616_, v___x_3615_);
v___x_3618_ = lean_usize_land(v_x_3607_, v___x_3617_);
v___x_3619_ = ((size_t)5ULL);
v___x_3620_ = lean_usize_sub(v_x_3608_, v___x_3619_);
v___x_3621_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3614_, v___x_3618_, v___x_3620_, v_x_3609_);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_add(v_j_3613_, v___x_3622_);
lean_dec(v_j_3613_);
v___x_3624_ = lean_array_get_size(v_cs_3610_);
v___x_3625_ = lean_nat_dec_lt(v___x_3623_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_dec(v___x_3623_);
return v___x_3621_;
}
else
{
size_t v___x_3626_; size_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = lean_usize_of_nat(v___x_3623_);
lean_dec(v___x_3623_);
v___x_3627_ = lean_usize_of_nat(v___x_3624_);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3610_, v___x_3626_, v___x_3627_, v___x_3621_);
return v___x_3628_;
}
}
else
{
lean_object* v_vs_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_vs_3629_ = lean_ctor_get(v_x_3606_, 0);
v___x_3630_ = lean_usize_to_nat(v_x_3607_);
v___x_3631_ = lean_array_get_size(v_vs_3629_);
v___x_3632_ = lean_nat_dec_lt(v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_dec(v___x_3630_);
return v_x_3609_;
}
else
{
size_t v___x_3633_; size_t v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_usize_of_nat(v___x_3630_);
lean_dec(v___x_3630_);
v___x_3634_ = lean_usize_of_nat(v___x_3631_);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3629_, v___x_3633_, v___x_3634_, v_x_3609_);
return v___x_3635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3636_, lean_object* v_x_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_){
_start:
{
size_t v_x_1153__boxed_3640_; size_t v_x_1154__boxed_3641_; lean_object* v_res_3642_; 
v_x_1153__boxed_3640_ = lean_unbox_usize(v_x_3637_);
lean_dec(v_x_3637_);
v_x_1154__boxed_3641_ = lean_unbox_usize(v_x_3638_);
lean_dec(v_x_3638_);
v_res_3642_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3636_, v_x_1153__boxed_3640_, v_x_1154__boxed_3641_, v_x_3639_);
lean_dec_ref(v_x_3636_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3643_, lean_object* v_init_3644_, lean_object* v_start_3645_){
_start:
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3647_ = lean_nat_dec_eq(v_start_3645_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v_root_3648_; lean_object* v_tail_3649_; size_t v_shift_3650_; lean_object* v_tailOff_3651_; uint8_t v___x_3652_; 
v_root_3648_ = lean_ctor_get(v_t_3643_, 0);
v_tail_3649_ = lean_ctor_get(v_t_3643_, 1);
v_shift_3650_ = lean_ctor_get_usize(v_t_3643_, 4);
v_tailOff_3651_ = lean_ctor_get(v_t_3643_, 3);
v___x_3652_ = lean_nat_dec_le(v_tailOff_3651_, v_start_3645_);
if (v___x_3652_ == 0)
{
size_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3653_ = lean_usize_of_nat(v_start_3645_);
v___x_3654_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3648_, v___x_3653_, v_shift_3650_, v_init_3644_);
v___x_3655_ = lean_array_get_size(v_tail_3649_);
v___x_3656_ = lean_nat_dec_lt(v___x_3646_, v___x_3655_);
if (v___x_3656_ == 0)
{
return v___x_3654_;
}
else
{
size_t v___x_3657_; size_t v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = ((size_t)0ULL);
v___x_3658_ = lean_usize_of_nat(v___x_3655_);
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3649_, v___x_3657_, v___x_3658_, v___x_3654_);
return v___x_3659_;
}
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3660_ = lean_nat_sub(v_start_3645_, v_tailOff_3651_);
v___x_3661_ = lean_array_get_size(v_tail_3649_);
v___x_3662_ = lean_nat_dec_lt(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec(v___x_3660_);
return v_init_3644_;
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_usize_of_nat(v___x_3660_);
lean_dec(v___x_3660_);
v___x_3664_ = lean_usize_of_nat(v___x_3661_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3649_, v___x_3663_, v___x_3664_, v_init_3644_);
return v___x_3665_;
}
}
}
else
{
lean_object* v_root_3666_; lean_object* v_tail_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_root_3666_ = lean_ctor_get(v_t_3643_, 0);
v_tail_3667_ = lean_ctor_get(v_t_3643_, 1);
v___x_3668_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3666_, v_init_3644_);
v___x_3669_ = lean_array_get_size(v_tail_3667_);
v___x_3670_ = lean_nat_dec_lt(v___x_3646_, v___x_3669_);
if (v___x_3670_ == 0)
{
return v___x_3668_;
}
else
{
size_t v___x_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = ((size_t)0ULL);
v___x_3672_ = lean_usize_of_nat(v___x_3669_);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3667_, v___x_3671_, v___x_3672_, v___x_3668_);
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3674_, lean_object* v_init_3675_, lean_object* v_start_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3674_, v_init_3675_, v_start_3676_);
lean_dec(v_start_3676_);
lean_dec_ref(v_t_3674_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3678_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_unreported_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3692_; 
v___x_3679_ = lean_unsigned_to_nat(32u);
v___x_3680_ = lean_mk_empty_array_with_capacity(v___x_3679_);
lean_dec_ref(v___x_3680_);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3683_ = lean_ctor_get(v_log_3678_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_log_3678_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3693_ = lean_ctor_get(v_log_3678_, 2);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_log_3678_, 0);
lean_dec(v_unused_3694_);
v___x_3685_ = v_log_3678_;
v_isShared_3686_ = v_isSharedCheck_3692_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_unreported_3683_);
lean_dec(v_log_3678_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3692_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3687_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3683_, v___x_3682_, v___x_3681_);
lean_dec_ref(v_unreported_3683_);
v___x_3688_ = l_Lean_NameSet_empty;
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 2, v___x_3688_);
lean_ctor_set(v___x_3685_, 1, v___x_3687_);
lean_ctor_set(v___x_3685_, 0, v___x_3682_);
v___x_3690_ = v___x_3685_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3695_, size_t v_i_3696_, size_t v_stop_3697_, lean_object* v_b_3698_){
_start:
{
lean_object* v___y_3700_; uint8_t v___x_3704_; 
v___x_3704_ = lean_usize_dec_eq(v_i_3696_, v_stop_3697_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; uint8_t v_severity_3706_; 
v___x_3705_ = lean_array_uget_borrowed(v_as_3695_, v_i_3696_);
v_severity_3706_ = lean_ctor_get_uint8(v___x_3705_, sizeof(void*)*5 + 1);
if (v_severity_3706_ == 1)
{
lean_object* v___x_3707_; 
lean_inc(v___x_3705_);
v___x_3707_ = l_Lean_PersistentArray_push___redArg(v_b_3698_, v___x_3705_);
v___y_3700_ = v___x_3707_;
goto v___jp_3699_;
}
else
{
v___y_3700_ = v_b_3698_;
goto v___jp_3699_;
}
}
else
{
return v_b_3698_;
}
v___jp_3699_:
{
size_t v___x_3701_; size_t v___x_3702_; 
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_add(v_i_3696_, v___x_3701_);
v_i_3696_ = v___x_3702_;
v_b_3698_ = v___y_3700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3708_, lean_object* v_i_3709_, lean_object* v_stop_3710_, lean_object* v_b_3711_){
_start:
{
size_t v_i_boxed_3712_; size_t v_stop_boxed_3713_; lean_object* v_res_3714_; 
v_i_boxed_3712_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_stop_boxed_3713_ = lean_unbox_usize(v_stop_3710_);
lean_dec(v_stop_3710_);
v_res_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3708_, v_i_boxed_3712_, v_stop_boxed_3713_, v_b_3711_);
lean_dec_ref(v_as_3708_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
lean_object* v_cs_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_cs_3717_ = lean_ctor_get(v_x_3715_, 0);
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_array_get_size(v_cs_3717_);
v___x_3720_ = lean_nat_dec_lt(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
return v_x_3716_;
}
else
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = ((size_t)0ULL);
v___x_3722_ = lean_usize_of_nat(v___x_3719_);
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3717_, v___x_3721_, v___x_3722_, v_x_3716_);
return v___x_3723_;
}
}
else
{
lean_object* v_vs_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_vs_3724_ = lean_ctor_get(v_x_3715_, 0);
v___x_3725_ = lean_unsigned_to_nat(0u);
v___x_3726_ = lean_array_get_size(v_vs_3724_);
v___x_3727_ = lean_nat_dec_lt(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
return v_x_3716_;
}
else
{
size_t v___x_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = lean_usize_of_nat(v___x_3726_);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3724_, v___x_3728_, v___x_3729_, v_x_3716_);
return v___x_3730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3731_, size_t v_i_3732_, size_t v_stop_3733_, lean_object* v_b_3734_){
_start:
{
uint8_t v___x_3735_; 
v___x_3735_ = lean_usize_dec_eq(v_i_3732_, v_stop_3733_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; lean_object* v___x_3737_; size_t v___x_3738_; size_t v___x_3739_; 
v___x_3736_ = lean_array_uget_borrowed(v_as_3731_, v_i_3732_);
v___x_3737_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3736_, v_b_3734_);
v___x_3738_ = ((size_t)1ULL);
v___x_3739_ = lean_usize_add(v_i_3732_, v___x_3738_);
v_i_3732_ = v___x_3739_;
v_b_3734_ = v___x_3737_;
goto _start;
}
else
{
return v_b_3734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3741_, lean_object* v_i_3742_, lean_object* v_stop_3743_, lean_object* v_b_3744_){
_start:
{
size_t v_i_boxed_3745_; size_t v_stop_boxed_3746_; lean_object* v_res_3747_; 
v_i_boxed_3745_ = lean_unbox_usize(v_i_3742_);
lean_dec(v_i_3742_);
v_stop_boxed_3746_ = lean_unbox_usize(v_stop_3743_);
lean_dec(v_stop_3743_);
v_res_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3741_, v_i_boxed_3745_, v_stop_boxed_3746_, v_b_3744_);
lean_dec_ref(v_as_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3748_, v_x_3749_);
lean_dec_ref(v_x_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3751_, size_t v_x_3752_, size_t v_x_3753_, lean_object* v_x_3754_){
_start:
{
if (lean_obj_tag(v_x_3751_) == 0)
{
lean_object* v_cs_3755_; lean_object* v___x_3756_; size_t v___x_3757_; lean_object* v_j_3758_; lean_object* v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; size_t v___x_3763_; size_t v___x_3764_; size_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_cs_3755_ = lean_ctor_get(v_x_3751_, 0);
v___x_3756_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3757_ = lean_usize_shift_right(v_x_3752_, v_x_3753_);
v_j_3758_ = lean_usize_to_nat(v___x_3757_);
v___x_3759_ = lean_array_get_borrowed(v___x_3756_, v_cs_3755_, v_j_3758_);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_shift_left(v___x_3760_, v_x_3753_);
v___x_3762_ = lean_usize_sub(v___x_3761_, v___x_3760_);
v___x_3763_ = lean_usize_land(v_x_3752_, v___x_3762_);
v___x_3764_ = ((size_t)5ULL);
v___x_3765_ = lean_usize_sub(v_x_3753_, v___x_3764_);
v___x_3766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3759_, v___x_3763_, v___x_3765_, v_x_3754_);
v___x_3767_ = lean_unsigned_to_nat(1u);
v___x_3768_ = lean_nat_add(v_j_3758_, v___x_3767_);
lean_dec(v_j_3758_);
v___x_3769_ = lean_array_get_size(v_cs_3755_);
v___x_3770_ = lean_nat_dec_lt(v___x_3768_, v___x_3769_);
if (v___x_3770_ == 0)
{
lean_dec(v___x_3768_);
return v___x_3766_;
}
else
{
size_t v___x_3771_; size_t v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = lean_usize_of_nat(v___x_3768_);
lean_dec(v___x_3768_);
v___x_3772_ = lean_usize_of_nat(v___x_3769_);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3755_, v___x_3771_, v___x_3772_, v___x_3766_);
return v___x_3773_;
}
}
else
{
lean_object* v_vs_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_vs_3774_ = lean_ctor_get(v_x_3751_, 0);
v___x_3775_ = lean_usize_to_nat(v_x_3752_);
v___x_3776_ = lean_array_get_size(v_vs_3774_);
v___x_3777_ = lean_nat_dec_lt(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_dec(v___x_3775_);
return v_x_3754_;
}
else
{
size_t v___x_3778_; size_t v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_usize_of_nat(v___x_3775_);
lean_dec(v___x_3775_);
v___x_3779_ = lean_usize_of_nat(v___x_3776_);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3774_, v___x_3778_, v___x_3779_, v_x_3754_);
return v___x_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_){
_start:
{
size_t v_x_1152__boxed_3785_; size_t v_x_1153__boxed_3786_; lean_object* v_res_3787_; 
v_x_1152__boxed_3785_ = lean_unbox_usize(v_x_3782_);
lean_dec(v_x_3782_);
v_x_1153__boxed_3786_ = lean_unbox_usize(v_x_3783_);
lean_dec(v_x_3783_);
v_res_3787_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3781_, v_x_1152__boxed_3785_, v_x_1153__boxed_3786_, v_x_3784_);
lean_dec_ref(v_x_3781_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3788_, lean_object* v_init_3789_, lean_object* v_start_3790_){
_start:
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = lean_nat_dec_eq(v_start_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v_root_3793_; lean_object* v_tail_3794_; size_t v_shift_3795_; lean_object* v_tailOff_3796_; uint8_t v___x_3797_; 
v_root_3793_ = lean_ctor_get(v_t_3788_, 0);
v_tail_3794_ = lean_ctor_get(v_t_3788_, 1);
v_shift_3795_ = lean_ctor_get_usize(v_t_3788_, 4);
v_tailOff_3796_ = lean_ctor_get(v_t_3788_, 3);
v___x_3797_ = lean_nat_dec_le(v_tailOff_3796_, v_start_3790_);
if (v___x_3797_ == 0)
{
size_t v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3798_ = lean_usize_of_nat(v_start_3790_);
v___x_3799_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3793_, v___x_3798_, v_shift_3795_, v_init_3789_);
v___x_3800_ = lean_array_get_size(v_tail_3794_);
v___x_3801_ = lean_nat_dec_lt(v___x_3791_, v___x_3800_);
if (v___x_3801_ == 0)
{
return v___x_3799_;
}
else
{
size_t v___x_3802_; size_t v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = ((size_t)0ULL);
v___x_3803_ = lean_usize_of_nat(v___x_3800_);
v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3794_, v___x_3802_, v___x_3803_, v___x_3799_);
return v___x_3804_;
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_nat_sub(v_start_3790_, v_tailOff_3796_);
v___x_3806_ = lean_array_get_size(v_tail_3794_);
v___x_3807_ = lean_nat_dec_lt(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_dec(v___x_3805_);
return v_init_3789_;
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_usize_of_nat(v___x_3805_);
lean_dec(v___x_3805_);
v___x_3809_ = lean_usize_of_nat(v___x_3806_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3794_, v___x_3808_, v___x_3809_, v_init_3789_);
return v___x_3810_;
}
}
}
else
{
lean_object* v_root_3811_; lean_object* v_tail_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_root_3811_ = lean_ctor_get(v_t_3788_, 0);
v_tail_3812_ = lean_ctor_get(v_t_3788_, 1);
v___x_3813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3811_, v_init_3789_);
v___x_3814_ = lean_array_get_size(v_tail_3812_);
v___x_3815_ = lean_nat_dec_lt(v___x_3791_, v___x_3814_);
if (v___x_3815_ == 0)
{
return v___x_3813_;
}
else
{
size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((size_t)0ULL);
v___x_3817_ = lean_usize_of_nat(v___x_3814_);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3812_, v___x_3816_, v___x_3817_, v___x_3813_);
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3819_, lean_object* v_init_3820_, lean_object* v_start_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3819_, v_init_3820_, v_start_3821_);
lean_dec(v_start_3821_);
lean_dec_ref(v_t_3819_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3823_){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v_unreported_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3837_; 
v___x_3824_ = lean_unsigned_to_nat(32u);
v___x_3825_ = lean_mk_empty_array_with_capacity(v___x_3824_);
lean_dec_ref(v___x_3825_);
v___x_3826_ = lean_unsigned_to_nat(0u);
v___x_3827_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3828_ = lean_ctor_get(v_log_3823_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_log_3823_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; 
v_unused_3838_ = lean_ctor_get(v_log_3823_, 2);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_log_3823_, 0);
lean_dec(v_unused_3839_);
v___x_3830_ = v_log_3823_;
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_unreported_3828_);
lean_dec(v_log_3823_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3832_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3828_, v___x_3827_, v___x_3826_);
lean_dec_ref(v_unreported_3828_);
v___x_3833_ = l_Lean_NameSet_empty;
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 2, v___x_3833_);
lean_ctor_set(v___x_3830_, 1, v___x_3832_);
lean_ctor_set(v___x_3830_, 0, v___x_3827_);
v___x_3835_ = v___x_3830_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3840_, lean_object* v_log_3841_, lean_object* v_f_3842_){
_start:
{
lean_object* v_unreported_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_unreported_3843_ = lean_ctor_get(v_log_3841_, 1);
lean_inc_ref(v_unreported_3843_);
lean_dec_ref(v_log_3841_);
v___x_3844_ = lean_unsigned_to_nat(0u);
v___x_3845_ = l_Lean_PersistentArray_forM___redArg(v_inst_3840_, v_unreported_3843_, v_f_3842_, v___x_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3846_, lean_object* v_inst_3847_, lean_object* v_log_3848_, lean_object* v_f_3849_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_MessageLog_forM___redArg(v_inst_3847_, v_log_3848_, v_f_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3851_){
_start:
{
lean_object* v_unreported_3852_; lean_object* v___x_3853_; 
v_unreported_3852_ = lean_ctor_get(v_log_3851_, 1);
v___x_3853_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_MessageLog_toList(v_log_3854_);
lean_dec_ref(v_log_3854_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3856_){
_start:
{
lean_object* v_unreported_3857_; lean_object* v___x_3858_; 
v_unreported_3857_ = lean_ctor_get(v_log_3856_, 1);
v___x_3858_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_MessageLog_toArray(v_log_3859_);
lean_dec_ref(v_log_3859_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3861_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_unsigned_to_nat(2u);
v___x_3863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v_msg_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
lean_ctor_set(v___x_3866_, 1, v_msg_3864_);
v___x_3867_ = l_Lean_MessageData_nestD(v___x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3868_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = l_Lean_MessageData_ofExpr(v_e_3868_);
v___x_3870_ = l_Lean_indentD(v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3871_, lean_object* v_msg_3872_){
_start:
{
lean_object* v_env_3874_; lean_object* v_mctx_3875_; lean_object* v_lctx_3876_; lean_object* v_opts_3877_; lean_object* v_currNamespace_3878_; lean_object* v_openDecls_3879_; lean_object* v___x_3880_; lean_object* v_msg_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_env_3874_ = lean_ctor_get(v_ctx_3871_, 0);
v_mctx_3875_ = lean_ctor_get(v_ctx_3871_, 1);
v_lctx_3876_ = lean_ctor_get(v_ctx_3871_, 2);
v_opts_3877_ = lean_ctor_get(v_ctx_3871_, 3);
v_currNamespace_3878_ = lean_ctor_get(v_ctx_3871_, 4);
v_openDecls_3879_ = lean_ctor_get(v_ctx_3871_, 5);
lean_inc(v_openDecls_3879_);
lean_inc(v_currNamespace_3878_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_currNamespace_3878_);
lean_ctor_set(v___x_3880_, 1, v_openDecls_3879_);
v_msg_3881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3881_, 0, v___x_3880_);
lean_ctor_set(v_msg_3881_, 1, v_msg_3872_);
lean_inc_ref(v_opts_3877_);
lean_inc_ref(v_lctx_3876_);
lean_inc_ref(v_mctx_3875_);
lean_inc_ref(v_env_3874_);
v___x_3882_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3882_, 0, v_env_3874_);
lean_ctor_set(v___x_3882_, 1, v_mctx_3875_);
lean_ctor_set(v___x_3882_, 2, v_lctx_3876_);
lean_ctor_set(v___x_3882_, 3, v_opts_3877_);
v___x_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
v___x_3884_ = l_Lean_MessageData_format(v_msg_3881_, v___x_3883_);
v___x_3885_ = l_Std_Format_defWidth;
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = l_Std_Format_pretty(v___x_3884_, v___x_3885_, v___x_3886_, v___x_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3888_, lean_object* v_msg_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3888_, v_msg_3889_);
lean_dec_ref(v_ctx_3888_);
return v_res_3891_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_3892_, lean_object* v_a_3893_, uint8_t v_b_3894_){
_start:
{
lean_object* v_str_3895_; lean_object* v_startInclusive_3896_; lean_object* v_endExclusive_3897_; lean_object* v___x_3898_; uint8_t v_decide_3899_; 
v_str_3895_ = lean_ctor_get(v_s_3892_, 0);
v_startInclusive_3896_ = lean_ctor_get(v_s_3892_, 1);
v_endExclusive_3897_ = lean_ctor_get(v_s_3892_, 2);
v___x_3898_ = lean_nat_sub(v_endExclusive_3897_, v_startInclusive_3896_);
v_decide_3899_ = lean_nat_dec_eq(v_a_3893_, v___x_3898_);
lean_dec(v___x_3898_);
if (v_decide_3899_ == 0)
{
lean_object* v___x_3900_; uint32_t v___x_3901_; uint32_t v___x_3902_; uint8_t v___x_3903_; 
v___x_3900_ = lean_nat_add(v_startInclusive_3896_, v_a_3893_);
lean_dec(v_a_3893_);
v___x_3901_ = lean_string_utf8_get_fast(v_str_3895_, v___x_3900_);
v___x_3902_ = 10;
v___x_3903_ = lean_uint32_dec_eq(v___x_3901_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_string_utf8_next_fast(v_str_3895_, v___x_3900_);
lean_dec(v___x_3900_);
v___x_3905_ = lean_nat_sub(v___x_3904_, v_startInclusive_3896_);
v_a_3893_ = v___x_3905_;
v_b_3894_ = v___x_3903_;
goto _start;
}
else
{
lean_dec(v___x_3900_);
return v___x_3903_;
}
}
else
{
lean_dec(v_a_3893_);
return v_b_3894_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_3907_, lean_object* v_a_3908_, lean_object* v_b_3909_){
_start:
{
uint8_t v_b_boxed_3910_; uint8_t v_res_3911_; lean_object* v_r_3912_; 
v_b_boxed_3910_ = lean_unbox(v_b_3909_);
v_res_3911_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3907_, v_a_3908_, v_b_boxed_3910_);
lean_dec_ref(v_s_3907_);
v_r_3912_ = lean_box(v_res_3911_);
return v_r_3912_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_3913_){
_start:
{
lean_object* v_searcher_3914_; uint8_t v___x_3915_; uint8_t v___x_3916_; 
v_searcher_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = 0;
v___x_3916_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3913_, v_searcher_3914_, v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_3917_){
_start:
{
uint8_t v_res_3918_; lean_object* v_r_3919_; 
v_res_3918_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_3917_);
lean_dec_ref(v_s_3917_);
v_r_3919_ = lean_box(v_res_3918_);
return v_r_3919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_3920_, lean_object* v_val_3921_, lean_object* v_a_3922_, lean_object* v_b_3923_){
_start:
{
uint8_t v_decide_3924_; 
v_decide_3924_ = lean_nat_dec_eq(v_a_3922_, v___x_3920_);
if (v_decide_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_string_utf8_next_fast(v_val_3921_, v_a_3922_);
lean_dec(v_a_3922_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_add(v_b_3923_, v___x_3926_);
lean_dec(v_b_3923_);
v_a_3922_ = v___x_3925_;
v_b_3923_ = v___x_3927_;
goto _start;
}
else
{
lean_dec(v_a_3922_);
return v_b_3923_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_3929_, lean_object* v_val_3930_, lean_object* v_a_3931_, lean_object* v_b_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3929_, v_val_3930_, v_a_3931_, v_b_3932_);
lean_dec_ref(v_val_3930_);
lean_dec(v___x_3929_);
return v_res_3933_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3935_ = l_Lean_MessageData_ofFormat(v___x_3934_);
return v___x_3935_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_3940_ = l_Lean_MessageData_ofFormat(v___x_3939_);
return v___x_3940_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_3945_ = l_Lean_MessageData_ofFormat(v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3946_, lean_object* v_maxInlineLength_3947_, lean_object* v_ctx_3948_){
_start:
{
lean_object* v_msg_3950_; lean_object* v___x_3951_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_msg_3950_ = l_Lean_MessageData_ofExpr(v_e_3946_);
lean_inc_ref(v_msg_3950_);
v___x_3951_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3948_, v_msg_3950_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = lean_string_utf8_byte_size(v___x_3951_);
lean_inc_ref(v___x_3951_);
v___x_3958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3951_);
lean_ctor_set(v___x_3958_, 1, v___x_3956_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
v___x_3959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3957_, v___x_3951_, v___x_3956_, v___x_3956_);
lean_dec_ref(v___x_3951_);
v___x_3960_ = lean_nat_dec_lt(v_maxInlineLength_3947_, v___x_3959_);
lean_dec(v___x_3959_);
if (v___x_3960_ == 0)
{
uint8_t v___x_3961_; 
v___x_3961_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_3958_);
lean_dec_ref_known(v___x_3958_, 3);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3962_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_3963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v_msg_3950_);
v___x_3964_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
return v___x_3965_;
}
else
{
goto v___jp_3952_;
}
}
else
{
lean_dec_ref_known(v___x_3958_, 3);
goto v___jp_3952_;
}
v___jp_3952_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = l_Lean_indentD(v_msg_3950_);
v___x_3954_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3966_, lean_object* v_maxInlineLength_3967_, lean_object* v_ctx_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_inlineExpr___lam__0(v_e_3966_, v_maxInlineLength_3967_, v_ctx_3968_);
lean_dec_ref(v_ctx_3968_);
lean_dec(v_maxInlineLength_3967_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3971_, lean_object* v_x_3972_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3974_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_3975_ = l_Lean_MessageData_ofExpr(v_e_3971_);
v___x_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v___x_3977_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3979_, lean_object* v_x_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_inlineExpr___lam__2(v_e_3979_, v_x_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3983_, lean_object* v_maxInlineLength_3984_){
_start:
{
lean_object* v___f_3985_; lean_object* v___f_3986_; lean_object* v___f_3987_; lean_object* v___x_3988_; 
lean_inc_ref_n(v_e_3983_, 2);
v___f_3985_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3985_, 0, v_e_3983_);
lean_closure_set(v___f_3985_, 1, v_maxInlineLength_3984_);
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3986_, 0, v_e_3983_);
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3987_, 0, v_e_3983_);
v___x_3988_ = l_Lean_MessageData_lazy(v___f_3985_, v___f_3986_, v___f_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_3989_, lean_object* v___x_3990_, lean_object* v_val_3991_, lean_object* v_inst_3992_, lean_object* v_R_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v_c_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3989_, v_val_3991_, v_a_3994_, v_b_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v_val_4000_, lean_object* v_inst_4001_, lean_object* v_R_4002_, lean_object* v_a_4003_, lean_object* v_b_4004_, lean_object* v_c_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_3998_, v___x_3999_, v_val_4000_, v_inst_4001_, v_R_4002_, v_a_4003_, v_b_4004_, v_c_4005_);
lean_dec_ref(v_val_4000_);
lean_dec_ref(v___x_3999_);
lean_dec(v___x_3998_);
return v_res_4006_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4007_, lean_object* v_inst_4008_, lean_object* v_R_4009_, lean_object* v_a_4010_, uint8_t v_b_4011_, lean_object* v_c_4012_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4007_, v_a_4010_, v_b_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4014_, lean_object* v_inst_4015_, lean_object* v_R_4016_, lean_object* v_a_4017_, lean_object* v_b_4018_, lean_object* v_c_4019_){
_start:
{
uint8_t v_b_boxed_4020_; uint8_t v_res_4021_; lean_object* v_r_4022_; 
v_b_boxed_4020_ = lean_unbox(v_b_4018_);
v_res_4021_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4014_, v_inst_4015_, v_R_4016_, v_a_4017_, v_b_boxed_4020_, v_c_4019_);
lean_dec_ref(v_s_4014_);
v_r_4022_ = lean_box(v_res_4021_);
return v_r_4022_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4027_ = l_Lean_MessageData_ofFormat(v___x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4028_, lean_object* v_maxInlineLength_4029_, lean_object* v_ctx_4030_){
_start:
{
lean_object* v_msg_4032_; lean_object* v___x_4033_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v_msg_4032_ = l_Lean_MessageData_ofExpr(v_e_4028_);
lean_inc_ref(v_msg_4032_);
v___x_4033_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4030_, v_msg_4032_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = lean_string_utf8_byte_size(v___x_4033_);
lean_inc_ref(v___x_4033_);
v___x_4038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4033_);
lean_ctor_set(v___x_4038_, 1, v___x_4036_);
lean_ctor_set(v___x_4038_, 2, v___x_4037_);
v___x_4039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4037_, v___x_4033_, v___x_4036_, v___x_4036_);
lean_dec_ref(v___x_4033_);
v___x_4040_ = lean_nat_dec_lt(v_maxInlineLength_4029_, v___x_4039_);
lean_dec(v___x_4039_);
if (v___x_4040_ == 0)
{
uint8_t v___x_4041_; 
v___x_4041_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4038_);
lean_dec_ref_known(v___x_4038_, 3);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4042_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v_msg_4032_);
v___x_4044_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
return v___x_4045_;
}
else
{
goto v___jp_4034_;
}
}
else
{
lean_dec_ref_known(v___x_4038_, 3);
goto v___jp_4034_;
}
v___jp_4034_:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_indentD(v_msg_4032_);
return v___x_4035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4046_, lean_object* v_maxInlineLength_4047_, lean_object* v_ctx_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_inlineExprTrailing___lam__0(v_e_4046_, v_maxInlineLength_4047_, v_ctx_4048_);
lean_dec_ref(v_ctx_4048_);
lean_dec(v_maxInlineLength_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4051_, lean_object* v_x_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4054_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4055_ = l_Lean_MessageData_ofExpr(v_e_4051_);
v___x_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4054_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4059_, lean_object* v_x_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_inlineExprTrailing___lam__2(v_e_4059_, v_x_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4063_, lean_object* v_maxInlineLength_4064_){
_start:
{
lean_object* v___f_4065_; lean_object* v___f_4066_; lean_object* v___f_4067_; lean_object* v___x_4068_; 
lean_inc_ref_n(v_e_4063_, 2);
v___f_4065_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4065_, 0, v_e_4063_);
lean_closure_set(v___f_4065_, 1, v_maxInlineLength_4064_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4066_, 0, v_e_4063_);
v___f_4067_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4067_, 0, v_e_4063_);
v___x_4068_ = l_Lean_MessageData_lazy(v___f_4065_, v___f_4066_, v___f_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4073_ = l_Lean_MessageData_ofFormat(v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4078_ = l_Lean_MessageData_ofFormat(v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4079_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4080_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v_msg_4079_);
v___x_4082_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4084_, lean_object* v_inst_4085_, lean_object* v_msg_4086_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_apply_1(v_inst_4084_, v_msg_4086_);
v___x_4088_ = lean_apply_2(v_inst_4085_, lean_box(0), v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4089_, lean_object* v_inst_4090_){
_start:
{
lean_object* v___f_4091_; 
v___f_4091_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4091_, 0, v_inst_4090_);
lean_closure_set(v___f_4091_, 1, v_inst_4089_);
return v___f_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4092_, lean_object* v_n_4093_, lean_object* v_inst_4094_, lean_object* v_inst_4095_){
_start:
{
lean_object* v___f_4096_; 
v___f_4096_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4096_, 0, v_inst_4095_);
lean_closure_set(v___f_4096_, 1, v_inst_4094_);
return v___f_4096_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_unsigned_to_nat(32u);
v___x_4098_ = lean_mk_empty_array_with_capacity(v___x_4097_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4100_ = ((size_t)5ULL);
v___x_4101_ = lean_unsigned_to_nat(0u);
v___x_4102_ = lean_unsigned_to_nat(32u);
v___x_4103_ = lean_mk_empty_array_with_capacity(v___x_4102_);
v___x_4104_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4105_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v___x_4103_);
lean_ctor_set(v___x_4105_, 2, v___x_4101_);
lean_ctor_set(v___x_4105_, 3, v___x_4101_);
lean_ctor_set_usize(v___x_4105_, 4, v___x_4100_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4106_ = lean_box(1);
v___x_4107_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4108_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v___x_4107_);
lean_ctor_set(v___x_4109_, 2, v___x_4106_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4110_, lean_object* v_msgData_4111_, lean_object* v_toPure_4112_, lean_object* v_opts_4113_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4114_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4115_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4116_, 0, v_env_4110_);
lean_ctor_set(v___x_4116_, 1, v___x_4114_);
lean_ctor_set(v___x_4116_, 2, v___x_4115_);
lean_ctor_set(v___x_4116_, 3, v_opts_4113_);
v___x_4117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
lean_ctor_set(v___x_4117_, 1, v_msgData_4111_);
v___x_4118_ = lean_apply_2(v_toPure_4112_, lean_box(0), v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_inst_4119_, lean_object* v_msgData_4120_, lean_object* v_toPure_4121_, lean_object* v_toBind_4122_, lean_object* v_____do__lift_4123_){
_start:
{
lean_object* v_getOptionsUnrestricted_4124_; uint8_t v___x_4125_; lean_object* v_env_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; 
v_getOptionsUnrestricted_4124_ = lean_ctor_get(v_inst_4119_, 1);
lean_inc(v_getOptionsUnrestricted_4124_);
lean_dec_ref(v_inst_4119_);
v___x_4125_ = 0;
v_env_4126_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4123_, v___x_4125_);
v___f_4127_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4127_, 0, v_env_4126_);
lean_closure_set(v___f_4127_, 1, v_msgData_4120_);
lean_closure_set(v___f_4127_, 2, v_toPure_4121_);
v___x_4128_ = lean_apply_4(v_toBind_4122_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4124_, v___f_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_msgData_4132_){
_start:
{
lean_object* v_toApplicative_4133_; lean_object* v_toBind_4134_; lean_object* v_getEnv_4135_; lean_object* v_toPure_4136_; lean_object* v___f_4137_; lean_object* v___x_4138_; 
v_toApplicative_4133_ = lean_ctor_get(v_inst_4129_, 0);
lean_inc_ref(v_toApplicative_4133_);
v_toBind_4134_ = lean_ctor_get(v_inst_4129_, 1);
lean_inc_n(v_toBind_4134_, 2);
lean_dec_ref(v_inst_4129_);
v_getEnv_4135_ = lean_ctor_get(v_inst_4130_, 0);
lean_inc(v_getEnv_4135_);
lean_dec_ref(v_inst_4130_);
v_toPure_4136_ = lean_ctor_get(v_toApplicative_4133_, 1);
lean_inc(v_toPure_4136_);
lean_dec_ref(v_toApplicative_4133_);
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4137_, 0, v_inst_4131_);
lean_closure_set(v___f_4137_, 1, v_msgData_4132_);
lean_closure_set(v___f_4137_, 2, v_toPure_4136_);
lean_closure_set(v___f_4137_, 3, v_toBind_4134_);
v___x_4138_ = lean_apply_4(v_toBind_4134_, lean_box(0), lean_box(0), v_getEnv_4135_, v___f_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4139_, lean_object* v_inst_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_msgData_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_addMessageContextPartial___redArg(v_inst_4140_, v_inst_4141_, v_inst_4142_, v_msgData_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4145_, lean_object* v_mctx_4146_, lean_object* v_lctx_4147_, lean_object* v_msgData_4148_, lean_object* v_toPure_4149_, lean_object* v_opts_4150_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4151_, 0, v_env_4145_);
lean_ctor_set(v___x_4151_, 1, v_mctx_4146_);
lean_ctor_set(v___x_4151_, 2, v_lctx_4147_);
lean_ctor_set(v___x_4151_, 3, v_opts_4150_);
v___x_4152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
lean_ctor_set(v___x_4152_, 1, v_msgData_4148_);
v___x_4153_ = lean_apply_2(v_toPure_4149_, lean_box(0), v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_inst_4154_, lean_object* v_env_4155_, lean_object* v_mctx_4156_, lean_object* v_msgData_4157_, lean_object* v_toPure_4158_, lean_object* v_toBind_4159_, lean_object* v_lctx_4160_){
_start:
{
lean_object* v_getOptionsUnrestricted_4161_; lean_object* v___f_4162_; lean_object* v___x_4163_; 
v_getOptionsUnrestricted_4161_ = lean_ctor_get(v_inst_4154_, 1);
lean_inc(v_getOptionsUnrestricted_4161_);
lean_dec_ref(v_inst_4154_);
v___f_4162_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4162_, 0, v_env_4155_);
lean_closure_set(v___f_4162_, 1, v_mctx_4156_);
lean_closure_set(v___f_4162_, 2, v_lctx_4160_);
lean_closure_set(v___f_4162_, 3, v_msgData_4157_);
lean_closure_set(v___f_4162_, 4, v_toPure_4158_);
v___x_4163_ = lean_apply_4(v_toBind_4159_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4161_, v___f_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_inst_4164_, lean_object* v_env_4165_, lean_object* v_msgData_4166_, lean_object* v_toPure_4167_, lean_object* v_toBind_4168_, lean_object* v_inst_4169_, lean_object* v_mctx_4170_){
_start:
{
lean_object* v___f_4171_; lean_object* v___x_4172_; 
lean_inc(v_toBind_4168_);
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4171_, 0, v_inst_4164_);
lean_closure_set(v___f_4171_, 1, v_env_4165_);
lean_closure_set(v___f_4171_, 2, v_mctx_4170_);
lean_closure_set(v___f_4171_, 3, v_msgData_4166_);
lean_closure_set(v___f_4171_, 4, v_toPure_4167_);
lean_closure_set(v___f_4171_, 5, v_toBind_4168_);
v___x_4172_ = lean_apply_4(v_toBind_4168_, lean_box(0), lean_box(0), v_inst_4169_, v___f_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4173_, lean_object* v_inst_4174_, lean_object* v_msgData_4175_, lean_object* v_toPure_4176_, lean_object* v_toBind_4177_, lean_object* v_inst_4178_, lean_object* v_____do__lift_4179_){
_start:
{
lean_object* v_getMCtx_4180_; uint8_t v___x_4181_; lean_object* v_env_4182_; lean_object* v___f_4183_; lean_object* v___x_4184_; 
v_getMCtx_4180_ = lean_ctor_get(v_inst_4173_, 0);
lean_inc(v_getMCtx_4180_);
lean_dec_ref(v_inst_4173_);
v___x_4181_ = 0;
v_env_4182_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4179_, v___x_4181_);
lean_inc(v_toBind_4177_);
v___f_4183_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4183_, 0, v_inst_4174_);
lean_closure_set(v___f_4183_, 1, v_env_4182_);
lean_closure_set(v___f_4183_, 2, v_msgData_4175_);
lean_closure_set(v___f_4183_, 3, v_toPure_4176_);
lean_closure_set(v___f_4183_, 4, v_toBind_4177_);
lean_closure_set(v___f_4183_, 5, v_inst_4178_);
v___x_4184_ = lean_apply_4(v_toBind_4177_, lean_box(0), lean_box(0), v_getMCtx_4180_, v___f_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4185_, lean_object* v_inst_4186_, lean_object* v_inst_4187_, lean_object* v_inst_4188_, lean_object* v_inst_4189_, lean_object* v_msgData_4190_){
_start:
{
lean_object* v_toApplicative_4191_; lean_object* v_toBind_4192_; lean_object* v_getEnv_4193_; lean_object* v_toPure_4194_; lean_object* v___f_4195_; lean_object* v___x_4196_; 
v_toApplicative_4191_ = lean_ctor_get(v_inst_4185_, 0);
lean_inc_ref(v_toApplicative_4191_);
v_toBind_4192_ = lean_ctor_get(v_inst_4185_, 1);
lean_inc_n(v_toBind_4192_, 2);
lean_dec_ref(v_inst_4185_);
v_getEnv_4193_ = lean_ctor_get(v_inst_4186_, 0);
lean_inc(v_getEnv_4193_);
lean_dec_ref(v_inst_4186_);
v_toPure_4194_ = lean_ctor_get(v_toApplicative_4191_, 1);
lean_inc(v_toPure_4194_);
lean_dec_ref(v_toApplicative_4191_);
v___f_4195_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4195_, 0, v_inst_4187_);
lean_closure_set(v___f_4195_, 1, v_inst_4189_);
lean_closure_set(v___f_4195_, 2, v_msgData_4190_);
lean_closure_set(v___f_4195_, 3, v_toPure_4194_);
lean_closure_set(v___f_4195_, 4, v_toBind_4192_);
lean_closure_set(v___f_4195_, 5, v_inst_4188_);
v___x_4196_ = lean_apply_4(v_toBind_4192_, lean_box(0), lean_box(0), v_getEnv_4193_, v___f_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_inst_4201_, lean_object* v_inst_4202_, lean_object* v_msgData_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_addMessageContextFull___redArg(v_inst_4198_, v_inst_4199_, v_inst_4200_, v_inst_4201_, v_inst_4202_, v_msgData_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg(){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0));
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object* v___dummy_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v_res_4210_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4214_);
lean_dec_ref(v_s_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4216_, lean_object* v___x_4217_, lean_object* v___x_4218_, lean_object* v_a_4219_, lean_object* v_b_4220_){
_start:
{
lean_object* v_it_4222_; lean_object* v_startInclusive_4223_; lean_object* v_endExclusive_4224_; 
if (lean_obj_tag(v_a_4219_) == 0)
{
lean_object* v_currPos_4230_; lean_object* v_searcher_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4254_; 
v_currPos_4230_ = lean_ctor_get(v_a_4219_, 0);
v_searcher_4231_ = lean_ctor_get(v_a_4219_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_a_4219_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4233_ = v_a_4219_;
v_isShared_4234_ = v_isSharedCheck_4254_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_searcher_4231_);
lean_inc(v_currPos_4230_);
lean_dec(v_a_4219_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4254_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
uint8_t v_decide_4235_; 
v_decide_4235_ = lean_nat_dec_eq(v_searcher_4231_, v___x_4218_);
if (v_decide_4235_ == 0)
{
uint32_t v___x_4236_; uint32_t v___x_4237_; uint8_t v___x_4238_; 
v___x_4236_ = 10;
v___x_4237_ = lean_string_utf8_get_fast(v_str_4216_, v_searcher_4231_);
v___x_4238_ = lean_uint32_dec_eq(v___x_4237_, v___x_4236_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4239_ = lean_string_utf8_next_fast(v_str_4216_, v_searcher_4231_);
lean_dec(v_searcher_4231_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v___x_4239_);
v___x_4241_ = v___x_4233_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_currPos_4230_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
v_a_4219_ = v___x_4241_;
goto _start;
}
}
else
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v_slice_4247_; lean_object* v_nextIt_4249_; 
v___x_4244_ = lean_string_utf8_next_fast(v_str_4216_, v_searcher_4231_);
v___x_4245_ = lean_nat_sub(v___x_4244_, v_searcher_4231_);
v___x_4246_ = lean_nat_add(v_searcher_4231_, v___x_4245_);
lean_dec(v___x_4245_);
v_slice_4247_ = l_String_Slice_subslice_x21(v___x_4217_, v_currPos_4230_, v_searcher_4231_);
lean_inc(v___x_4246_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v___x_4246_);
lean_ctor_set(v___x_4233_, 0, v___x_4246_);
v_nextIt_4249_ = v___x_4233_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v___x_4246_);
v_nextIt_4249_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v_startInclusive_4250_; lean_object* v_endExclusive_4251_; 
v_startInclusive_4250_ = lean_ctor_get(v_slice_4247_, 0);
lean_inc(v_startInclusive_4250_);
v_endExclusive_4251_ = lean_ctor_get(v_slice_4247_, 1);
lean_inc(v_endExclusive_4251_);
lean_dec_ref(v_slice_4247_);
v_it_4222_ = v_nextIt_4249_;
v_startInclusive_4223_ = v_startInclusive_4250_;
v_endExclusive_4224_ = v_endExclusive_4251_;
goto v___jp_4221_;
}
}
}
else
{
lean_object* v___x_4253_; 
lean_del_object(v___x_4233_);
lean_dec(v_searcher_4231_);
v___x_4253_ = lean_box(1);
lean_inc(v___x_4218_);
v_it_4222_ = v___x_4253_;
v_startInclusive_4223_ = v_currPos_4230_;
v_endExclusive_4224_ = v___x_4218_;
goto v___jp_4221_;
}
}
}
else
{
lean_dec(v___x_4218_);
return v_b_4220_;
}
v___jp_4221_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = lean_string_utf8_extract_fast(v_str_4216_, v_startInclusive_4223_, v_endExclusive_4224_);
lean_dec(v_endExclusive_4224_);
lean_dec(v_startInclusive_4223_);
v___x_4226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
v___x_4227_ = l_Lean_MessageData_ofFormat(v___x_4226_);
v___x_4228_ = lean_array_push(v_b_4220_, v___x_4227_);
v_a_4219_ = v_it_4222_;
v_b_4220_ = v___x_4228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4255_, lean_object* v___x_4256_, lean_object* v___x_4257_, lean_object* v_a_4258_, lean_object* v_b_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4255_, v___x_4256_, v___x_4257_, v_a_4258_, v_b_4259_);
lean_dec_ref(v___x_4256_);
lean_dec_ref(v_str_4255_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4263_){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v_lines_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = lean_string_utf8_byte_size(v_str_4263_);
lean_inc_ref(v_str_4263_);
v___x_4266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4266_, 0, v_str_4263_);
lean_ctor_set(v___x_4266_, 1, v___x_4264_);
lean_ctor_set(v___x_4266_, 2, v___x_4265_);
v_lines_4267_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
v___x_4268_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4263_, v___x_4266_, v___x_4265_, v_lines_4267_, v___x_4268_);
lean_dec_ref_known(v___x_4266_, 3);
lean_dec_ref(v_str_4263_);
v___x_4270_ = lean_array_to_list(v___x_4269_);
v___x_4271_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4272_ = l_Lean_MessageData_joinSep(v___x_4270_, v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4273_, lean_object* v___x_4274_, lean_object* v___x_4275_, lean_object* v_inst_4276_, lean_object* v_R_4277_, lean_object* v_a_4278_, lean_object* v_b_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4273_, v___x_4274_, v___x_4275_, v_a_4278_, v_b_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v_inst_4284_, lean_object* v_R_4285_, lean_object* v_a_4286_, lean_object* v_b_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4281_, v___x_4282_, v___x_4283_, v_inst_4284_, v_R_4285_, v_a_4286_, v_b_4287_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_str_4281_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4289_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4291_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4291_, 0, lean_box(0));
lean_closure_set(v___x_4291_, 1, lean_box(0));
lean_closure_set(v___x_4291_, 2, lean_box(0));
lean_closure_set(v___x_4291_, 3, v___x_4290_);
lean_closure_set(v___x_4291_, 4, v_inst_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4292_, lean_object* v_inst_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg(){
_start:
{
lean_object* v___f_4302_; 
v___f_4302_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object* v___dummy_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_instToMessageDataTSyntax___redArg();
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4305_){
_start:
{
lean_object* v___f_4306_; 
v___f_4306_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Lean_instToMessageDataTSyntax(v_k_4307_);
lean_dec(v_k_4307_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4313_, lean_object* v_as_4314_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = lean_box(0);
v___x_4316_ = l_List_mapTR_loop___redArg(v_inst_4313_, v_as_4314_, v___x_4315_);
v___x_4317_ = l_Lean_MessageData_ofList(v___x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4318_){
_start:
{
lean_object* v___f_4319_; 
v___f_4319_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4319_, 0, v_inst_4318_);
return v___f_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4320_, lean_object* v_inst_4321_){
_start:
{
lean_object* v___f_4322_; 
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4322_, 0, v_inst_4321_);
return v___f_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4323_, lean_object* v_as_4324_){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4325_ = lean_array_to_list(v_as_4324_);
v___x_4326_ = lean_box(0);
v___x_4327_ = l_List_mapTR_loop___redArg(v_inst_4323_, v___x_4325_, v___x_4326_);
v___x_4328_ = l_Lean_MessageData_ofList(v___x_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4329_){
_start:
{
lean_object* v___f_4330_; 
v___f_4330_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4330_, 0, v_inst_4329_);
return v___f_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4331_, lean_object* v_inst_4332_){
_start:
{
lean_object* v___f_4333_; 
v___f_4333_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4333_, 0, v_inst_4332_);
return v___f_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4334_, lean_object* v_acc_4335_, lean_object* v_recur_4336_){
_start:
{
lean_object* v_array_4337_; lean_object* v_start_4338_; lean_object* v_stop_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4352_; 
v_array_4337_ = lean_ctor_get(v_it_4334_, 0);
v_start_4338_ = lean_ctor_get(v_it_4334_, 1);
v_stop_4339_ = lean_ctor_get(v_it_4334_, 2);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_it_4334_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4341_ = v_it_4334_;
v_isShared_4342_ = v_isSharedCheck_4352_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_stop_4339_);
lean_inc(v_start_4338_);
lean_inc(v_array_4337_);
lean_dec(v_it_4334_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4352_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_nat_dec_lt(v_start_4338_, v_stop_4339_);
if (v___x_4343_ == 0)
{
lean_del_object(v___x_4341_);
lean_dec(v_stop_4339_);
lean_dec(v_start_4338_);
lean_dec_ref(v_array_4337_);
lean_dec_ref(v_recur_4336_);
return v_acc_4335_;
}
else
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4344_ = lean_unsigned_to_nat(1u);
v___x_4345_ = lean_nat_add(v_start_4338_, v___x_4344_);
lean_inc_ref(v_array_4337_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 1, v___x_4345_);
v___x_4347_ = v___x_4341_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_array_4337_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v_stop_4339_);
v___x_4347_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_array_fget(v_array_4337_, v_start_4338_);
lean_dec(v_start_4338_);
lean_dec_ref(v_array_4337_);
v___x_4349_ = lean_array_push(v_acc_4335_, v___x_4348_);
v___x_4350_ = lean_apply_3(v_recur_4336_, v___x_4347_, v___x_4349_, lean_box(0));
return v___x_4350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4355_, lean_object* v_inst_4356_, lean_object* v_as_4357_){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4358_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4359_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4355_, v_as_4357_, v___x_4358_);
v___x_4360_ = lean_array_to_list(v___x_4359_);
v___x_4361_ = lean_box(0);
v___x_4362_ = l_List_mapTR_loop___redArg(v_inst_4356_, v___x_4360_, v___x_4361_);
v___x_4363_ = l_Lean_MessageData_ofList(v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4365_){
_start:
{
lean_object* v___f_4366_; lean_object* v___f_4367_; 
v___f_4366_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4367_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4367_, 0, v___f_4366_);
lean_closure_set(v___f_4367_, 1, v_inst_4365_);
return v___f_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4368_, lean_object* v_inst_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4369_);
return v___x_4370_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4375_ = l_Lean_MessageData_ofFormat(v___x_4374_);
return v___x_4375_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4379_ = l_Lean_MessageData_ofFormat(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4380_, lean_object* v_x_4381_){
_start:
{
if (lean_obj_tag(v_x_4381_) == 0)
{
lean_object* v___x_4382_; 
lean_dec_ref(v_inst_4380_);
v___x_4382_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4382_;
}
else
{
lean_object* v_val_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_val_4383_ = lean_ctor_get(v_x_4381_, 0);
lean_inc(v_val_4383_);
lean_dec_ref_known(v_x_4381_, 1);
v___x_4384_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4385_ = lean_apply_1(v_inst_4380_, v_val_4383_);
v___x_4386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4384_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
v___x_4387_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4389_){
_start:
{
lean_object* v___f_4390_; 
v___f_4390_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4390_, 0, v_inst_4389_);
return v___f_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4391_, lean_object* v_inst_4392_){
_start:
{
lean_object* v___f_4393_; 
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4393_, 0, v_inst_4392_);
return v___f_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4394_, lean_object* v_inst_4395_, lean_object* v_x_4396_){
_start:
{
lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4412_; 
v_fst_4397_ = lean_ctor_get(v_x_4396_, 0);
v_snd_4398_ = lean_ctor_get(v_x_4396_, 1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_x_4396_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4400_ = v_x_4396_;
v_isShared_4401_ = v_isSharedCheck_4412_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_x_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4412_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4402_ = lean_apply_1(v_inst_4394_, v_fst_4397_);
v___x_4403_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 7);
lean_ctor_set(v___x_4400_, 1, v___x_4403_);
lean_ctor_set(v___x_4400_, 0, v___x_4402_);
v___x_4405_ = v___x_4400_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4406_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4405_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
v___x_4408_ = lean_apply_1(v_inst_4395_, v_snd_4398_);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l_Lean_MessageData_paren(v___x_4409_);
return v___x_4410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4413_, lean_object* v_inst_4414_){
_start:
{
lean_object* v___f_4415_; 
v___f_4415_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4415_, 0, v_inst_4413_);
lean_closure_set(v___f_4415_, 1, v_inst_4414_);
return v___f_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4416_, lean_object* v_00_u03b2_4417_, lean_object* v_inst_4418_, lean_object* v_inst_4419_){
_start:
{
lean_object* v___f_4420_; 
v___f_4420_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4420_, 0, v_inst_4418_);
lean_closure_set(v___f_4420_, 1, v_inst_4419_);
return v___f_4420_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4425_ = l_Lean_MessageData_ofFormat(v___x_4424_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4426_){
_start:
{
if (lean_obj_tag(v_x_4426_) == 0)
{
lean_object* v___x_4427_; 
v___x_4427_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4427_;
}
else
{
lean_object* v_val_4428_; lean_object* v___x_4429_; 
v_val_4428_ = lean_ctor_get(v_x_4426_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v_x_4426_, 1);
v___x_4429_ = l_Lean_MessageData_ofExpr(v_val_4428_);
return v___x_4429_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4464_ = l_String_toRawSubstring_x27(v___x_4463_);
return v___x_4464_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4480_ = l_String_toRawSubstring_x27(v___x_4479_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v___x_4497_; uint8_t v___x_4498_; 
v___x_4497_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4494_);
v___x_4498_ = l_Lean_Syntax_isOfKind(v_x_4494_, v___x_4497_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
lean_dec(v_x_4494_);
v___x_4499_ = lean_box(1);
v___x_4500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
lean_ctor_set(v___x_4500_, 1, v_a_4496_);
return v___x_4500_;
}
else
{
lean_object* v_quotContext_4501_; lean_object* v_currMacroScope_4502_; lean_object* v_ref_4503_; lean_object* v___x_4504_; lean_object* v_interpStr_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_quotContext_4501_ = lean_ctor_get(v_a_4495_, 1);
v_currMacroScope_4502_ = lean_ctor_get(v_a_4495_, 2);
v_ref_4503_ = lean_ctor_get(v_a_4495_, 5);
v___x_4504_ = lean_unsigned_to_nat(1u);
v_interpStr_4505_ = l_Lean_Syntax_getArg(v_x_4494_, v___x_4504_);
lean_dec(v_x_4494_);
v___x_4506_ = 0;
v___x_4507_ = l_Lean_SourceInfo_fromRef(v_ref_4503_, v___x_4506_);
v___x_4508_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4509_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4502_, 2);
lean_inc_n(v_quotContext_4501_, 2);
v___x_4510_ = l_Lean_addMacroScope(v_quotContext_4501_, v___x_4509_, v_currMacroScope_4502_);
v___x_4511_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4507_);
v___x_4512_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4507_);
lean_ctor_set(v___x_4512_, 1, v___x_4508_);
lean_ctor_set(v___x_4512_, 2, v___x_4510_);
lean_ctor_set(v___x_4512_, 3, v___x_4511_);
v___x_4513_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4514_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4515_ = l_Lean_addMacroScope(v_quotContext_4501_, v___x_4514_, v_currMacroScope_4502_);
v___x_4516_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4517_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4507_);
lean_ctor_set(v___x_4517_, 1, v___x_4513_);
lean_ctor_set(v___x_4517_, 2, v___x_4515_);
lean_ctor_set(v___x_4517_, 3, v___x_4516_);
lean_inc_ref(v___x_4517_);
v___x_4518_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4505_, v___x_4512_, v___x_4517_, v___x_4517_, v_a_4495_, v_a_4496_);
lean_dec(v_interpStr_4505_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_a_4520_ = lean_ctor_get(v___x_4518_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4518_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4519_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
v_a_4528_ = lean_ctor_get(v___x_4518_, 0);
v_a_4529_ = lean_ctor_get(v___x_4518_, 1);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4518_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_inc(v_a_4528_);
lean_dec(v___x_4518_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4528_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4537_, v_a_4538_, v_a_4539_);
lean_dec_ref(v_a_4538_);
return v_res_4540_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4543_ = l_Lean_stringToMessageData(v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4544_){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4545_ = lean_array_to_list(v_msgs_4544_);
v___x_4546_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4547_ = l_Lean_MessageData_joinSep(v___x_4545_, v___x_4546_);
v___x_4548_ = l_Lean_indentD(v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4549_, lean_object* v_lctx_4550_, lean_object* v_opts_4551_, lean_object* v_msg_4552_){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4553_ = l_Lean_Environment_ofKernelEnv(v_env_4549_);
v___x_4554_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
lean_ctor_set(v___x_4555_, 2, v_lctx_4550_);
lean_ctor_set(v___x_4555_, 3, v_opts_4551_);
v___x_4556_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v_msg_4552_);
return v___x_4556_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4559_ = l_Lean_stringToMessageData(v___x_4558_);
return v___x_4559_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4562_ = l_Lean_stringToMessageData(v___x_4561_);
return v___x_4562_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4565_ = l_Lean_stringToMessageData(v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4566_, lean_object* v_n_4567_, lean_object* v_expectedType_4568_){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4569_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4570_ = l_Lean_MessageData_ofName(v_n_4567_);
v___x_4571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_indentExpr(v_givenType_4566_);
v___x_4575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4573_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4575_);
lean_ctor_set(v___x_4577_, 1, v___x_4576_);
v___x_4578_ = l_Lean_indentExpr(v_expectedType_4568_);
v___x_4579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4577_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
return v___x_4579_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4580_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
return v___x_4581_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = lean_box(1);
v___x_4583_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4584_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
lean_ctor_set(v___x_4585_, 2, v___x_4582_);
return v___x_4585_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__2));
v___x_4588_ = l_Lean_stringToMessageData(v___x_4587_);
return v___x_4588_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4590_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__4));
v___x_4591_ = l_Lean_stringToMessageData(v___x_4590_);
return v___x_4591_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__6));
v___x_4594_ = l_Lean_stringToMessageData(v___x_4593_);
return v___x_4594_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__9));
v___x_4599_ = l_Lean_MessageData_ofFormat(v___x_4598_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__12(void){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__11));
v___x_4602_ = l_Lean_stringToMessageData(v___x_4601_);
return v___x_4602_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__14(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__13));
v___x_4605_ = l_Lean_stringToMessageData(v___x_4604_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__16(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__15));
v___x_4608_ = l_Lean_stringToMessageData(v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__18(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__17));
v___x_4611_ = l_Lean_stringToMessageData(v___x_4610_);
return v___x_4611_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__20(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__19));
v___x_4614_ = l_Lean_stringToMessageData(v___x_4613_);
return v___x_4614_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__22(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__21));
v___x_4617_ = l_Lean_stringToMessageData(v___x_4616_);
return v___x_4617_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__24(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__23));
v___x_4620_ = l_Lean_stringToMessageData(v___x_4619_);
return v___x_4620_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__26(void){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__25));
v___x_4623_ = l_Lean_stringToMessageData(v___x_4622_);
return v___x_4623_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__28(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__27));
v___x_4626_ = l_Lean_stringToMessageData(v___x_4625_);
return v___x_4626_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__30(void){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__29));
v___x_4629_ = l_Lean_stringToMessageData(v___x_4628_);
return v___x_4629_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__32(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__31));
v___x_4632_ = l_Lean_stringToMessageData(v___x_4631_);
return v___x_4632_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__34(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4634_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__33));
v___x_4635_ = l_Lean_stringToMessageData(v___x_4634_);
return v___x_4635_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__36(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__35));
v___x_4638_ = l_Lean_stringToMessageData(v___x_4637_);
return v___x_4638_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__38(void){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__37));
v___x_4641_ = l_Lean_stringToMessageData(v___x_4640_);
return v___x_4641_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__41(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__40));
v___x_4646_ = l_Lean_MessageData_ofFormat(v___x_4645_);
return v___x_4646_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__44(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__43));
v___x_4651_ = l_Lean_MessageData_ofFormat(v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__47(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__46));
v___x_4656_ = l_Lean_MessageData_ofFormat(v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__50(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__49));
v___x_4661_ = l_Lean_MessageData_ofFormat(v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4662_, lean_object* v_opts_4663_){
_start:
{
switch(lean_obj_tag(v_e_4662_))
{
case 0:
{
lean_object* v_env_4664_; lean_object* v_name_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4678_; 
v_env_4664_ = lean_ctor_get(v_e_4662_, 0);
v_name_4665_ = lean_ctor_get(v_e_4662_, 1);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_e_4662_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4667_ = v_e_4662_;
v_isShared_4668_ = v_isSharedCheck_4678_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_name_4665_);
lean_inc(v_env_4664_);
lean_dec(v_e_4662_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4678_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4673_; 
v___x_4669_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4670_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__3, &l_Lean_Kernel_Exception_toMessageData___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__3);
v___x_4671_ = l_Lean_MessageData_ofName(v_name_4665_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 7);
lean_ctor_set(v___x_4667_, 1, v___x_4671_);
lean_ctor_set(v___x_4667_, 0, v___x_4670_);
v___x_4673_ = v___x_4667_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4664_, v___x_4669_, v_opts_4663_, v___x_4675_);
return v___x_4676_;
}
}
}
case 1:
{
lean_object* v_env_4679_; lean_object* v_name_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4694_; 
v_env_4679_ = lean_ctor_get(v_e_4662_, 0);
v_name_4680_ = lean_ctor_get(v_e_4662_, 1);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_e_4662_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4682_ = v_e_4662_;
v_isShared_4683_ = v_isSharedCheck_4694_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_name_4680_);
lean_inc(v_env_4679_);
lean_dec(v_e_4662_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4694_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v___x_4684_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4685_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__7, &l_Lean_Kernel_Exception_toMessageData___closed__7_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__7);
v___x_4686_ = 1;
v___x_4687_ = l_Lean_MessageData_ofConstName(v_name_4680_, v___x_4686_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set_tag(v___x_4682_, 7);
lean_ctor_set(v___x_4682_, 1, v___x_4687_);
lean_ctor_set(v___x_4682_, 0, v___x_4685_);
v___x_4689_ = v___x_4682_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4690_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4689_);
lean_ctor_set(v___x_4691_, 1, v___x_4690_);
v___x_4692_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4679_, v___x_4684_, v_opts_4663_, v___x_4691_);
return v___x_4692_;
}
}
}
case 2:
{
lean_object* v_env_4695_; lean_object* v_decl_4696_; lean_object* v_givenType_4697_; lean_object* v___x_4698_; 
v_env_4695_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4695_);
v_decl_4696_ = lean_ctor_get(v_e_4662_, 1);
lean_inc(v_decl_4696_);
v_givenType_4697_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_givenType_4697_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4698_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
switch(lean_obj_tag(v_decl_4696_))
{
case 1:
{
lean_object* v_val_4699_; lean_object* v_toConstantVal_4700_; lean_object* v_name_4701_; lean_object* v_type_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v_val_4699_ = lean_ctor_get(v_decl_4696_, 0);
lean_inc_ref(v_val_4699_);
lean_dec_ref_known(v_decl_4696_, 1);
v_toConstantVal_4700_ = lean_ctor_get(v_val_4699_, 0);
lean_inc_ref(v_toConstantVal_4700_);
lean_dec_ref(v_val_4699_);
v_name_4701_ = lean_ctor_get(v_toConstantVal_4700_, 0);
lean_inc(v_name_4701_);
v_type_4702_ = lean_ctor_get(v_toConstantVal_4700_, 2);
lean_inc_ref(v_type_4702_);
lean_dec_ref(v_toConstantVal_4700_);
v___x_4703_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4697_, v_name_4701_, v_type_4702_);
v___x_4704_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4695_, v___x_4698_, v_opts_4663_, v___x_4703_);
return v___x_4704_;
}
case 2:
{
lean_object* v_val_4705_; lean_object* v_toConstantVal_4706_; lean_object* v_name_4707_; lean_object* v_type_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v_val_4705_ = lean_ctor_get(v_decl_4696_, 0);
lean_inc_ref(v_val_4705_);
lean_dec_ref_known(v_decl_4696_, 1);
v_toConstantVal_4706_ = lean_ctor_get(v_val_4705_, 0);
lean_inc_ref(v_toConstantVal_4706_);
lean_dec_ref(v_val_4705_);
v_name_4707_ = lean_ctor_get(v_toConstantVal_4706_, 0);
lean_inc(v_name_4707_);
v_type_4708_ = lean_ctor_get(v_toConstantVal_4706_, 2);
lean_inc_ref(v_type_4708_);
lean_dec_ref(v_toConstantVal_4706_);
v___x_4709_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4697_, v_name_4707_, v_type_4708_);
v___x_4710_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4695_, v___x_4698_, v_opts_4663_, v___x_4709_);
return v___x_4710_;
}
default: 
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
lean_dec_ref(v_givenType_4697_);
lean_dec(v_decl_4696_);
v___x_4711_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__10, &l_Lean_Kernel_Exception_toMessageData___closed__10_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__10);
v___x_4712_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4695_, v___x_4698_, v_opts_4663_, v___x_4711_);
return v___x_4712_;
}
}
}
case 3:
{
lean_object* v_env_4713_; lean_object* v_name_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v_env_4713_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4713_);
v_name_4714_ = lean_ctor_get(v_e_4662_, 1);
lean_inc(v_name_4714_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4715_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4716_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__12, &l_Lean_Kernel_Exception_toMessageData___closed__12_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__12);
v___x_4717_ = 1;
v___x_4718_ = l_Lean_MessageData_ofConstName(v_name_4714_, v___x_4717_);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4716_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4719_);
lean_ctor_set(v___x_4721_, 1, v___x_4720_);
v___x_4722_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4713_, v___x_4715_, v_opts_4663_, v___x_4721_);
return v___x_4722_;
}
case 4:
{
lean_object* v_env_4723_; lean_object* v_name_4724_; lean_object* v_expr_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_env_4723_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4723_);
v_name_4724_ = lean_ctor_get(v_e_4662_, 1);
lean_inc(v_name_4724_);
v_expr_4725_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_expr_4725_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4726_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4727_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__14, &l_Lean_Kernel_Exception_toMessageData___closed__14_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__14);
v___x_4728_ = 1;
v___x_4729_ = l_Lean_MessageData_ofConstName(v_name_4724_, v___x_4728_);
v___x_4730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4727_);
lean_ctor_set(v___x_4730_, 1, v___x_4729_);
v___x_4731_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__16, &l_Lean_Kernel_Exception_toMessageData___closed__16_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__16);
v___x_4732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4730_);
lean_ctor_set(v___x_4732_, 1, v___x_4731_);
v___x_4733_ = l_Lean_indentExpr(v_expr_4725_);
v___x_4734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4723_, v___x_4726_, v_opts_4663_, v___x_4734_);
return v___x_4735_;
}
case 5:
{
lean_object* v_env_4736_; lean_object* v_lctx_4737_; lean_object* v_expr_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v_env_4736_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4736_);
v_lctx_4737_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4737_);
v_expr_4738_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_expr_4738_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4739_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__18, &l_Lean_Kernel_Exception_toMessageData___closed__18_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__18);
v___x_4740_ = l_Lean_indentExpr(v_expr_4738_);
v___x_4741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4739_);
lean_ctor_set(v___x_4741_, 1, v___x_4740_);
v___x_4742_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4736_, v_lctx_4737_, v_opts_4663_, v___x_4741_);
return v___x_4742_;
}
case 6:
{
lean_object* v_env_4743_; lean_object* v_lctx_4744_; lean_object* v_expr_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v_env_4743_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4743_);
v_lctx_4744_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4744_);
v_expr_4745_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_expr_4745_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4746_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__20, &l_Lean_Kernel_Exception_toMessageData___closed__20_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__20);
v___x_4747_ = l_Lean_indentExpr(v_expr_4745_);
v___x_4748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4743_, v_lctx_4744_, v_opts_4663_, v___x_4748_);
return v___x_4749_;
}
case 7:
{
lean_object* v_env_4750_; lean_object* v_lctx_4751_; lean_object* v_name_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_env_4750_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4750_);
v_lctx_4751_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4751_);
v_name_4752_ = lean_ctor_get(v_e_4662_, 2);
lean_inc(v_name_4752_);
lean_dec_ref_known(v_e_4662_, 5);
v___x_4753_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__22, &l_Lean_Kernel_Exception_toMessageData___closed__22_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__22);
v___x_4754_ = l_Lean_MessageData_ofName(v_name_4752_);
v___x_4755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4753_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4750_, v_lctx_4751_, v_opts_4663_, v___x_4757_);
return v___x_4758_;
}
case 8:
{
lean_object* v_env_4759_; lean_object* v_lctx_4760_; lean_object* v_expr_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v_env_4759_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4759_);
v_lctx_4760_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4760_);
v_expr_4761_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_expr_4761_);
lean_dec_ref_known(v_e_4662_, 4);
v___x_4762_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__24, &l_Lean_Kernel_Exception_toMessageData___closed__24_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__24);
v___x_4763_ = l_Lean_indentExpr(v_expr_4761_);
v___x_4764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4762_);
lean_ctor_set(v___x_4764_, 1, v___x_4763_);
v___x_4765_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4759_, v_lctx_4760_, v_opts_4663_, v___x_4764_);
return v___x_4765_;
}
case 9:
{
lean_object* v_env_4766_; lean_object* v_lctx_4767_; lean_object* v_app_4768_; lean_object* v_funType_4769_; lean_object* v_argType_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v_env_4766_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4766_);
v_lctx_4767_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4767_);
v_app_4768_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_app_4768_);
v_funType_4769_ = lean_ctor_get(v_e_4662_, 3);
lean_inc_ref(v_funType_4769_);
v_argType_4770_ = lean_ctor_get(v_e_4662_, 4);
lean_inc_ref(v_argType_4770_);
lean_dec_ref_known(v_e_4662_, 5);
v___x_4771_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__26, &l_Lean_Kernel_Exception_toMessageData___closed__26_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__26);
v___x_4772_ = l_Lean_indentExpr(v_app_4768_);
v___x_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__28, &l_Lean_Kernel_Exception_toMessageData___closed__28_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__28);
v___x_4775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4773_);
lean_ctor_set(v___x_4775_, 1, v___x_4774_);
v___x_4776_ = l_Lean_indentExpr(v_argType_4770_);
v___x_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v___x_4778_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__30, &l_Lean_Kernel_Exception_toMessageData___closed__30_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__30);
v___x_4779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4777_);
lean_ctor_set(v___x_4779_, 1, v___x_4778_);
v___x_4780_ = l_Lean_indentExpr(v_funType_4769_);
v___x_4781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
v___x_4782_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4766_, v_lctx_4767_, v_opts_4663_, v___x_4781_);
return v___x_4782_;
}
case 10:
{
lean_object* v_env_4783_; lean_object* v_lctx_4784_; lean_object* v_proj_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_env_4783_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4783_);
v_lctx_4784_ = lean_ctor_get(v_e_4662_, 1);
lean_inc_ref(v_lctx_4784_);
v_proj_4785_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_proj_4785_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4786_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__32, &l_Lean_Kernel_Exception_toMessageData___closed__32_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__32);
v___x_4787_ = l_Lean_indentExpr(v_proj_4785_);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4783_, v_lctx_4784_, v_opts_4663_, v___x_4788_);
return v___x_4789_;
}
case 11:
{
lean_object* v_env_4790_; lean_object* v_name_4791_; lean_object* v_type_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v_env_4790_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_env_4790_);
v_name_4791_ = lean_ctor_get(v_e_4662_, 1);
lean_inc(v_name_4791_);
v_type_4792_ = lean_ctor_get(v_e_4662_, 2);
lean_inc_ref(v_type_4792_);
lean_dec_ref_known(v_e_4662_, 3);
v___x_4793_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4794_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__34, &l_Lean_Kernel_Exception_toMessageData___closed__34_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__34);
v___x_4795_ = 1;
v___x_4796_ = l_Lean_MessageData_ofConstName(v_name_4791_, v___x_4795_);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4794_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__36, &l_Lean_Kernel_Exception_toMessageData___closed__36_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__36);
v___x_4799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4797_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = l_Lean_indentExpr(v_type_4792_);
v___x_4801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4799_);
lean_ctor_set(v___x_4801_, 1, v___x_4800_);
v___x_4802_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4790_, v___x_4793_, v_opts_4663_, v___x_4801_);
return v___x_4802_;
}
case 12:
{
lean_object* v_msg_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_dec_ref(v_opts_4663_);
v_msg_4803_ = lean_ctor_get(v_e_4662_, 0);
lean_inc_ref(v_msg_4803_);
lean_dec_ref_known(v_e_4662_, 1);
v___x_4804_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__38, &l_Lean_Kernel_Exception_toMessageData___closed__38_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__38);
v___x_4805_ = l_Lean_stringToMessageData(v_msg_4803_);
v___x_4806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4804_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
return v___x_4806_;
}
case 13:
{
lean_object* v___x_4807_; 
lean_dec_ref(v_opts_4663_);
v___x_4807_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__41, &l_Lean_Kernel_Exception_toMessageData___closed__41_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__41);
return v___x_4807_;
}
case 14:
{
lean_object* v___x_4808_; 
lean_dec_ref(v_opts_4663_);
v___x_4808_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__44, &l_Lean_Kernel_Exception_toMessageData___closed__44_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__44);
return v___x_4808_;
}
case 15:
{
lean_object* v___x_4809_; 
lean_dec_ref(v_opts_4663_);
v___x_4809_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__47, &l_Lean_Kernel_Exception_toMessageData___closed__47_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__47);
return v___x_4809_;
}
default: 
{
lean_object* v___x_4810_; 
lean_dec_ref(v_opts_4663_);
v___x_4810_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__50, &l_Lean_Kernel_Exception_toMessageData___closed__50_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__50);
return v___x_4810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4811_, lean_object* v_e_4812_, lean_object* v_cls_4813_){
_start:
{
lean_object* v___x_4814_; double v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4814_ = lean_box(0);
v___x_4815_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__7, &l_Lean_MessageData_formatAux___closed__7_once, _init_l_Lean_MessageData_formatAux___closed__7);
v___x_4816_ = 1;
v___x_4817_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4818_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4818_, 0, v_cls_4813_);
lean_ctor_set(v___x_4818_, 1, v___x_4814_);
lean_ctor_set(v___x_4818_, 2, v___x_4817_);
lean_ctor_set_float(v___x_4818_, sizeof(void*)*3, v___x_4815_);
lean_ctor_set_float(v___x_4818_, sizeof(void*)*3 + 8, v___x_4815_);
lean_ctor_set_uint8(v___x_4818_, sizeof(void*)*3 + 16, v___x_4816_);
v___x_4819_ = lean_apply_1(v_inst_4811_, v_e_4812_);
v___x_4820_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4821_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4818_);
lean_ctor_set(v___x_4821_, 1, v___x_4819_);
lean_ctor_set(v___x_4821_, 2, v___x_4820_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4822_, lean_object* v_inst_4823_, lean_object* v_e_4824_, lean_object* v_cls_4825_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Lean_toTraceElem___redArg(v_inst_4823_, v_e_4824_, v_cls_4825_);
return v___x_4826_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PPExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedMessageSeverity_default = _init_l_Lean_instInhabitedMessageSeverity_default();
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instInhabitedTraceResult_default = _init_l_Lean_instInhabitedTraceResult_default();
l_Lean_instInhabitedTraceResult = _init_l_Lean_instInhabitedTraceResult();
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
res = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_MessageData_maxTraceChildren = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_MessageData_maxTraceChildren);
lean_dec_ref(res);
l_Lean_instInhabitedMessageLog_default = _init_l_Lean_instInhabitedMessageLog_default();
lean_mark_persistent(l_Lean_instInhabitedMessageLog_default);
l_Lean_instInhabitedMessageLog = _init_l_Lean_instInhabitedMessageLog();
lean_mark_persistent(l_Lean_instInhabitedMessageLog);
l_Lean_MessageLog_empty = _init_l_Lean_MessageLog_empty();
lean_mark_persistent(l_Lean_MessageLog_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Message(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Message(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Message(builtin);
}
#ifdef __cplusplus
}
#endif
