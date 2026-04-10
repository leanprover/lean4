// Lean compiler output
// Module: Lean.Message
// Imports: public import Init.Data.Slice.Array public import Lean.Util.PPExt public import Lean.Util.Sorry import Init.Data.String.Search import Init.Data.Format.Macro import Init.Data.Iterators.Consumers.Collect
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_instToJsonPosition_toJson(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_ppConstNameWithInfos(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TraceResult_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_instInhabitedMessageData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedMessageData_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData_default = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "maxTraceChildren"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 113, 99, 32, 64, 25, 169, 239)}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Maximum number of trace node children to display"};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(175, 61, 140, 215, 80, 247, 40, 222)}};
static const lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_string_object l_Lean_MessageData_formatAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_MessageData_formatAux___closed__7 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__7_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__7_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__8 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__8_value;
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_MessageData_formatAux___closed__9;
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
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_closure_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11_value)} };
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SerialMessage"};
static const lean_object* l_Lean_instFromJsonSerialMessage_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonSerialMessage_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__2;
static const lean_string_object l_Lean_inlineExpr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__3 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_inlineExpr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_inlineExpr___lam__0___closed__3_value)}};
static const lean_object* l_Lean_inlineExpr___lam__0___closed__4 = (const lean_object*)&l_Lean_inlineExpr___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__5;
static lean_once_cell_t l_Lean_inlineExpr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inlineExpr___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_value;
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
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_127__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__2;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) unknown constant '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__3 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__3_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__4;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__5 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__5_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__6;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "(kernel) constant has already been declared '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__7 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__7_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__8;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) declaration type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__9 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__10 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__10_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__11;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) declaration has metavariables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__12 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__12_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__13;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "(kernel) declaration has free variables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__14 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__14_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__15;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', expression: "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__16 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__16_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__17;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) function expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__18 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__18_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__19;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "(kernel) type expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__20 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__20_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__21;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) let-declaration type mismatch '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__22 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__22_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__23;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "(kernel) type mismatch at"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__24 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__24_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__25;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) application type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__26 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__26_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__27;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nargument has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__28 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__28_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__29;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nbut function has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__30 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__30_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__31;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) invalid projection"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__32 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__32_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__33;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) type of theorem '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__34 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__34_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__35;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "' is not a proposition"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__36 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__36_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__37;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "(kernel) "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__38 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__38_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__39;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "(kernel) deterministic timeout"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__40 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__41 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__41_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__42;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "(kernel) excessive memory consumption detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__43 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__44 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__44_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__45;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "(kernel) deep recursion detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__46 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__47 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__47_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__48;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "(kernel) interrupted"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__49 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__50 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__50_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__51;
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos(lean_object* v_fileName_7_, lean_object* v_pos_8_, lean_object* v_msg_9_, lean_object* v_endPos_10_, lean_object* v_kind_11_, lean_object* v_name_12_){
_start:
{
lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_32_; lean_object* v___y_33_; lean_object* v___y_34_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___y_53_; lean_object* v___y_70_; 
if (lean_obj_tag(v_endPos_10_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_70_ = v___x_72_;
goto v___jp_69_;
}
else
{
lean_object* v_val_73_; lean_object* v_line_74_; lean_object* v_column_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_val_73_ = lean_ctor_get(v_endPos_10_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v_endPos_10_);
v_line_74_ = lean_ctor_get(v_val_73_, 0);
lean_inc(v_line_74_);
v_column_75_ = lean_ctor_get(v_val_73_, 1);
lean_inc(v_column_75_);
lean_dec(v_val_73_);
v___x_76_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__5));
v___x_77_ = l_Nat_reprFast(v_line_74_);
v___x_78_ = lean_string_append(v___x_76_, v___x_77_);
lean_dec_ref(v___x_77_);
v___x_79_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
v___x_81_ = l_Nat_reprFast(v_column_75_);
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
lean_dec_ref(v___x_81_);
v___y_70_ = v___x_82_;
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
v___x_35_ = lean_string_append(v___y_32_, v___y_34_);
lean_dec_ref(v___y_34_);
v___x_36_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__0));
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
v___y_14_ = v___y_33_;
v___y_15_ = v___x_37_;
goto v___jp_13_;
}
v___jp_38_:
{
lean_object* v___x_43_; 
lean_inc_ref(v___y_40_);
v___x_43_ = lean_string_append(v___y_40_, v___y_42_);
if (lean_obj_tag(v___y_39_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___x_43_;
v___y_33_ = v___y_41_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_39_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v___y_39_);
v___y_32_ = v___x_43_;
v___y_33_ = v___y_41_;
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
v___y_39_ = v___y_48_;
v___y_40_ = v___x_49_;
v___y_41_ = v___y_47_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___y_48_;
v___y_40_ = v___x_49_;
v___y_41_ = v___y_47_;
v___y_42_ = v_val_51_;
goto v___jp_38_;
}
}
v___jp_52_:
{
if (lean_obj_tag(v_name_12_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_box(0);
v___y_47_ = v___y_53_;
v___y_48_ = v___x_54_;
goto v___jp_46_;
}
else
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_68_; 
v_val_55_ = lean_ctor_get(v_name_12_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_name_12_);
if (v_isSharedCheck_68_ == 0)
{
v___x_57_ = v_name_12_;
v_isShared_58_ = v_isSharedCheck_68_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v_name_12_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_68_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_59_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_60_ = 1;
v___x_61_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_55_, v___x_60_);
v___x_62_ = lean_string_append(v___x_59_, v___x_61_);
lean_dec_ref(v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_64_ = lean_string_append(v___x_62_, v___x_63_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_64_);
v___x_66_ = v___x_57_;
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
v___y_53_ = v___y_70_;
goto v___jp_52_;
}
}
else
{
v___y_53_ = v___y_70_;
goto v___jp_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkErrorStringWithPos___boxed(lean_object* v_fileName_83_, lean_object* v_pos_84_, lean_object* v_msg_85_, lean_object* v_endPos_86_, lean_object* v_kind_87_, lean_object* v_name_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_mkErrorStringWithPos(v_fileName_83_, v_pos_84_, v_msg_85_, v_endPos_86_, v_kind_87_, v_name_88_);
lean_dec(v_kind_87_);
lean_dec_ref(v_msg_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t v_x_90_){
_start:
{
switch(v_x_90_)
{
case 0:
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(0u);
return v___x_91_;
}
case 1:
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(1u);
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(2u);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object* v_x_94_){
_start:
{
uint8_t v_x_boxed_95_; lean_object* v_res_96_; 
v_x_boxed_95_ = lean_unbox(v_x_94_);
v_res_96_ = l_Lean_MessageSeverity_ctorIdx(v_x_boxed_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx(uint8_t v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_MessageSeverity_ctorIdx(v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toCtorIdx___boxed(lean_object* v_x_99_){
_start:
{
uint8_t v_x_4__boxed_100_; lean_object* v_res_101_; 
v_x_4__boxed_100_ = lean_unbox(v_x_99_);
v_res_101_ = l_Lean_MessageSeverity_toCtorIdx(v_x_4__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* v_k_102_){
_start:
{
lean_inc(v_k_102_);
return v_k_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* v_k_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_MessageSeverity_ctorElim___redArg(v_k_103_);
lean_dec(v_k_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_105_, lean_object* v_ctorIdx_106_, uint8_t v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_inc(v_k_109_);
return v_k_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_110_, lean_object* v_ctorIdx_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_k_114_){
_start:
{
uint8_t v_t_boxed_115_; lean_object* v_res_116_; 
v_t_boxed_115_ = lean_unbox(v_t_112_);
v_res_116_ = l_Lean_MessageSeverity_ctorElim(v_motive_110_, v_ctorIdx_111_, v_t_boxed_115_, v_h_113_, v_k_114_);
lean_dec(v_k_114_);
lean_dec(v_ctorIdx_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_117_){
_start:
{
lean_inc(v_information_117_);
return v_information_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_118_);
lean_dec(v_information_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_120_, uint8_t v_t_121_, lean_object* v_h_122_, lean_object* v_information_123_){
_start:
{
lean_inc(v_information_123_);
return v_information_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_information_127_){
_start:
{
uint8_t v_t_boxed_128_; lean_object* v_res_129_; 
v_t_boxed_128_ = lean_unbox(v_t_125_);
v_res_129_ = l_Lean_MessageSeverity_information_elim(v_motive_124_, v_t_boxed_128_, v_h_126_, v_information_127_);
lean_dec(v_information_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_130_){
_start:
{
lean_inc(v_warning_130_);
return v_warning_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_131_);
lean_dec(v_warning_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_133_, uint8_t v_t_134_, lean_object* v_h_135_, lean_object* v_warning_136_){
_start:
{
lean_inc(v_warning_136_);
return v_warning_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_warning_140_){
_start:
{
uint8_t v_t_boxed_141_; lean_object* v_res_142_; 
v_t_boxed_141_ = lean_unbox(v_t_138_);
v_res_142_ = l_Lean_MessageSeverity_warning_elim(v_motive_137_, v_t_boxed_141_, v_h_139_, v_warning_140_);
lean_dec(v_warning_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* v_error_143_){
_start:
{
lean_inc(v_error_143_);
return v_error_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* v_error_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_MessageSeverity_error_elim___redArg(v_error_144_);
lean_dec(v_error_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_error_149_){
_start:
{
lean_inc(v_error_149_);
return v_error_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_error_153_){
_start:
{
uint8_t v_t_boxed_154_; lean_object* v_res_155_; 
v_t_boxed_154_ = lean_unbox(v_t_151_);
v_res_155_ = l_Lean_MessageSeverity_error_elim(v_motive_150_, v_t_boxed_154_, v_h_152_, v_error_153_);
lean_dec(v_error_153_);
return v_res_155_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_158_, uint8_t v_y_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_MessageSeverity_ctorIdx(v_x_158_);
v___x_161_ = l_Lean_MessageSeverity_ctorIdx(v_y_159_);
v___x_162_ = lean_nat_dec_eq(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
lean_dec(v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_163_, lean_object* v_y_164_){
_start:
{
uint8_t v_x_17__boxed_165_; uint8_t v_y_18__boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_x_17__boxed_165_ = lean_unbox(v_x_163_);
v_y_18__boxed_166_ = lean_unbox(v_y_164_);
v_res_167_ = l_Lean_instBEqMessageSeverity_beq(v_x_17__boxed_165_, v_y_18__boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_180_){
_start:
{
switch(v_x_180_)
{
case 0:
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_181_;
}
case 1:
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_182_;
}
default: 
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_184_){
_start:
{
uint8_t v_x_67__boxed_185_; lean_object* v_res_186_; 
v_x_67__boxed_185_ = lean_unbox(v_x_184_);
v_res_186_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Json_getTag_x3f(v_json_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref(v___x_205_);
v___x_208_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_209_ = lean_string_dec_eq(v_val_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_211_ = lean_string_dec_eq(v_val_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_213_ = lean_string_dec_eq(v_val_207_, v___x_212_);
lean_dec(v_val_207_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_214_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_215_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_val_207_);
v___x_216_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_val_207_);
v___x_217_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_220_){
_start:
{
switch(v_x_220_)
{
case 0:
{
lean_object* v___x_221_; 
v___x_221_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_221_;
}
case 1:
{
lean_object* v___x_222_; 
v___x_222_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_222_;
}
default: 
{
lean_object* v___x_223_; 
v___x_223_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_224_){
_start:
{
uint8_t v_x_28__boxed_225_; lean_object* v_res_226_; 
v_x_28__boxed_225_ = lean_unbox(v_x_224_);
v_res_226_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx(uint8_t v_x_229_){
_start:
{
switch(v_x_229_)
{
case 0:
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(0u);
return v___x_230_;
}
case 1:
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(1u);
return v___x_231_;
}
default: 
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(2u);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___boxed(lean_object* v_x_233_){
_start:
{
uint8_t v_x_boxed_234_; lean_object* v_res_235_; 
v_x_boxed_234_ = lean_unbox(v_x_233_);
v_res_235_ = l_Lean_TraceResult_ctorIdx(v_x_boxed_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toCtorIdx(uint8_t v_x_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_TraceResult_ctorIdx(v_x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toCtorIdx___boxed(lean_object* v_x_238_){
_start:
{
uint8_t v_x_4__boxed_239_; lean_object* v_res_240_; 
v_x_4__boxed_239_ = lean_unbox(v_x_238_);
v_res_240_ = l_Lean_TraceResult_toCtorIdx(v_x_4__boxed_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg(lean_object* v_k_241_){
_start:
{
lean_inc(v_k_241_);
return v_k_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg___boxed(lean_object* v_k_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_TraceResult_ctorElim___redArg(v_k_242_);
lean_dec(v_k_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim(lean_object* v_motive_244_, lean_object* v_ctorIdx_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_k_248_){
_start:
{
lean_inc(v_k_248_);
return v_k_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___boxed(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_TraceResult_ctorElim(v_motive_249_, v_ctorIdx_250_, v_t_boxed_254_, v_h_252_, v_k_253_);
lean_dec(v_k_253_);
lean_dec(v_ctorIdx_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg(lean_object* v_success_256_){
_start:
{
lean_inc(v_success_256_);
return v_success_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg___boxed(lean_object* v_success_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_TraceResult_success_elim___redArg(v_success_257_);
lean_dec(v_success_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_success_262_){
_start:
{
lean_inc(v_success_262_);
return v_success_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_success_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Lean_TraceResult_success_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_success_266_);
lean_dec(v_success_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg(lean_object* v_failure_269_){
_start:
{
lean_inc(v_failure_269_);
return v_failure_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg___boxed(lean_object* v_failure_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_TraceResult_failure_elim___redArg(v_failure_270_);
lean_dec(v_failure_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim(lean_object* v_motive_272_, uint8_t v_t_273_, lean_object* v_h_274_, lean_object* v_failure_275_){
_start:
{
lean_inc(v_failure_275_);
return v_failure_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___boxed(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_failure_279_){
_start:
{
uint8_t v_t_boxed_280_; lean_object* v_res_281_; 
v_t_boxed_280_ = lean_unbox(v_t_277_);
v_res_281_ = l_Lean_TraceResult_failure_elim(v_motive_276_, v_t_boxed_280_, v_h_278_, v_failure_279_);
lean_dec(v_failure_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg(lean_object* v_error_282_){
_start:
{
lean_inc(v_error_282_);
return v_error_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg___boxed(lean_object* v_error_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_TraceResult_error_elim___redArg(v_error_283_);
lean_dec(v_error_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim(lean_object* v_motive_285_, uint8_t v_t_286_, lean_object* v_h_287_, lean_object* v_error_288_){
_start:
{
lean_inc(v_error_288_);
return v_error_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___boxed(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_error_292_){
_start:
{
uint8_t v_t_boxed_293_; lean_object* v_res_294_; 
v_t_boxed_293_ = lean_unbox(v_t_290_);
v_res_294_ = l_Lean_TraceResult_error_elim(v_motive_289_, v_t_boxed_293_, v_h_291_, v_error_292_);
lean_dec(v_error_292_);
return v_res_294_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult_default(void){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult(void){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTraceResult_beq(uint8_t v_x_297_, uint8_t v_y_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Lean_TraceResult_ctorIdx(v_x_297_);
v___x_300_ = l_Lean_TraceResult_ctorIdx(v_y_298_);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
lean_dec(v___x_300_);
lean_dec(v___x_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_302_, lean_object* v_y_303_){
_start:
{
uint8_t v_x_17__boxed_304_; uint8_t v_y_18__boxed_305_; uint8_t v_res_306_; lean_object* v_r_307_; 
v_x_17__boxed_304_ = lean_unbox(v_x_302_);
v_y_18__boxed_305_ = lean_unbox(v_y_303_);
v_res_306_ = l_Lean_instBEqTraceResult_beq(v_x_17__boxed_304_, v_y_18__boxed_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_323_, lean_object* v_prec_324_){
_start:
{
lean_object* v___y_326_; lean_object* v___y_333_; lean_object* v___y_340_; 
switch(v_x_323_)
{
case 0:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1024u);
v___x_347_ = lean_nat_dec_le(v___x_346_, v_prec_324_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_326_ = v___x_348_;
goto v___jp_325_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_326_ = v___x_349_;
goto v___jp_325_;
}
}
case 1:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1024u);
v___x_351_ = lean_nat_dec_le(v___x_350_, v_prec_324_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_333_ = v___x_352_;
goto v___jp_332_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_333_ = v___x_353_;
goto v___jp_332_;
}
}
default: 
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1024u);
v___x_355_ = lean_nat_dec_le(v___x_354_, v_prec_324_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_340_ = v___x_356_;
goto v___jp_339_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_340_ = v___x_357_;
goto v___jp_339_;
}
}
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_326_);
v___x_328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = 0;
v___x_330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*1, v___x_329_);
v___x_331_ = l_Repr_addAppParen(v___x_330_, v_prec_324_);
return v___x_331_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_334_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_333_);
v___x_335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_335_, 0, v___y_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = 0;
v___x_337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_336_);
v___x_338_ = l_Repr_addAppParen(v___x_337_, v_prec_324_);
return v___x_338_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_341_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_340_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___y_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = 0;
v___x_344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
v___x_345_ = l_Repr_addAppParen(v___x_344_, v_prec_324_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_358_, lean_object* v_prec_359_){
_start:
{
uint8_t v_x_177__boxed_360_; lean_object* v_res_361_; 
v_x_177__boxed_360_ = lean_unbox(v_x_358_);
v_res_361_ = l_Lean_instReprTraceResult_repr(v_x_177__boxed_360_, v_prec_359_);
lean_dec(v_prec_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object* v_x_364_){
_start:
{
switch(lean_obj_tag(v_x_364_))
{
case 0:
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(0u);
return v___x_365_;
}
case 1:
{
lean_object* v___x_366_; 
v___x_366_ = lean_unsigned_to_nat(1u);
return v___x_366_;
}
case 2:
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(2u);
return v___x_367_;
}
case 3:
{
lean_object* v___x_368_; 
v___x_368_ = lean_unsigned_to_nat(3u);
return v___x_368_;
}
case 4:
{
lean_object* v___x_369_; 
v___x_369_ = lean_unsigned_to_nat(4u);
return v___x_369_;
}
case 5:
{
lean_object* v___x_370_; 
v___x_370_ = lean_unsigned_to_nat(5u);
return v___x_370_;
}
case 6:
{
lean_object* v___x_371_; 
v___x_371_ = lean_unsigned_to_nat(6u);
return v___x_371_;
}
case 7:
{
lean_object* v___x_372_; 
v___x_372_ = lean_unsigned_to_nat(7u);
return v___x_372_;
}
case 8:
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(8u);
return v___x_373_;
}
case 9:
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(9u);
return v___x_374_;
}
default: 
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(10u);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_MessageData_ctorIdx(v_x_376_);
lean_dec_ref(v_x_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_378_, lean_object* v_k_379_){
_start:
{
switch(lean_obj_tag(v_t_378_))
{
case 0:
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v_t_378_, 0);
lean_inc_ref(v_a_380_);
lean_dec_ref(v_t_378_);
v___x_381_ = lean_apply_1(v_k_379_, v_a_380_);
return v___x_381_;
}
case 1:
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v_t_378_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v_t_378_);
v___x_383_ = lean_apply_1(v_k_379_, v_a_382_);
return v___x_383_;
}
case 5:
{
lean_object* v_a_384_; lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_384_ = lean_ctor_get(v_t_378_, 0);
lean_inc(v_a_384_);
v_a_385_ = lean_ctor_get(v_t_378_, 1);
lean_inc_ref(v_a_385_);
lean_dec_ref(v_t_378_);
v___x_386_ = lean_apply_2(v_k_379_, v_a_384_, v_a_385_);
return v___x_386_;
}
case 6:
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v_t_378_, 0);
lean_inc_ref(v_a_387_);
lean_dec_ref(v_t_378_);
v___x_388_ = lean_apply_1(v_k_379_, v_a_387_);
return v___x_388_;
}
case 8:
{
lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_389_ = lean_ctor_get(v_t_378_, 0);
lean_inc(v_a_389_);
v_a_390_ = lean_ctor_get(v_t_378_, 1);
lean_inc_ref(v_a_390_);
lean_dec_ref(v_t_378_);
v___x_391_ = lean_apply_2(v_k_379_, v_a_389_, v_a_390_);
return v___x_391_;
}
case 9:
{
lean_object* v_data_392_; lean_object* v_msg_393_; lean_object* v_children_394_; lean_object* v___x_395_; 
v_data_392_ = lean_ctor_get(v_t_378_, 0);
lean_inc_ref(v_data_392_);
v_msg_393_ = lean_ctor_get(v_t_378_, 1);
lean_inc_ref(v_msg_393_);
v_children_394_ = lean_ctor_get(v_t_378_, 2);
lean_inc_ref(v_children_394_);
lean_dec_ref(v_t_378_);
v___x_395_ = lean_apply_3(v_k_379_, v_data_392_, v_msg_393_, v_children_394_);
return v___x_395_;
}
default: 
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v_t_378_, 0);
lean_inc_ref(v_a_396_);
v_a_397_ = lean_ctor_get(v_t_378_, 1);
lean_inc_ref(v_a_397_);
lean_dec_ref(v_t_378_);
v___x_398_ = lean_apply_2(v_k_379_, v_a_396_, v_a_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_399_, lean_object* v_ctorIdx_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_k_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_MessageData_ctorElim___redArg(v_t_401_, v_k_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_405_, lean_object* v_ctorIdx_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_k_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_MessageData_ctorElim(v_motive__1_405_, v_ctorIdx_406_, v_t_407_, v_h_408_, v_k_409_);
lean_dec(v_ctorIdx_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_411_, lean_object* v_ofFormatWithInfos_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_MessageData_ctorElim___redArg(v_t_411_, v_ofFormatWithInfos_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_ofFormatWithInfos_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MessageData_ctorElim___redArg(v_t_415_, v_ofFormatWithInfos_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_419_, lean_object* v_ofGoal_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_MessageData_ctorElim___redArg(v_t_419_, v_ofGoal_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_ofGoal_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_MessageData_ctorElim___redArg(v_t_423_, v_ofGoal_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_427_, lean_object* v_ofWidget_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_MessageData_ctorElim___redArg(v_t_427_, v_ofWidget_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_ofWidget_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MessageData_ctorElim___redArg(v_t_431_, v_ofWidget_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_435_, lean_object* v_withContext_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_MessageData_ctorElim___redArg(v_t_435_, v_withContext_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_withContext_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_MessageData_ctorElim___redArg(v_t_439_, v_withContext_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_443_, lean_object* v_withNamingContext_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_MessageData_ctorElim___redArg(v_t_443_, v_withNamingContext_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_withNamingContext_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_MessageData_ctorElim___redArg(v_t_447_, v_withNamingContext_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_451_, lean_object* v_nest_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_MessageData_ctorElim___redArg(v_t_451_, v_nest_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_nest_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MessageData_ctorElim___redArg(v_t_455_, v_nest_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_459_, lean_object* v_group_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_MessageData_ctorElim___redArg(v_t_459_, v_group_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_462_, lean_object* v_t_463_, lean_object* v_h_464_, lean_object* v_group_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_MessageData_ctorElim___redArg(v_t_463_, v_group_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_467_, lean_object* v_compose_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_MessageData_ctorElim___redArg(v_t_467_, v_compose_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_compose_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_MessageData_ctorElim___redArg(v_t_471_, v_compose_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_475_, lean_object* v_tagged_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_MessageData_ctorElim___redArg(v_t_475_, v_tagged_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_tagged_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MessageData_ctorElim___redArg(v_t_479_, v_tagged_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_483_, lean_object* v_trace_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_MessageData_ctorElim___redArg(v_t_483_, v_trace_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_trace_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_MessageData_ctorElim___redArg(v_t_487_, v_trace_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_491_, lean_object* v_ofLazy_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_MessageData_ctorElim___redArg(v_t_491_, v_ofLazy_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_ofLazy_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_MessageData_ctorElim___redArg(v_t_495_, v_ofLazy_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_box(1);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_fmt_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_514_, lean_object* v_onMissingContext_515_, lean_object* v_f_516_, lean_object* v_ctx_x3f_517_){
_start:
{
lean_object* v_msg_520_; 
if (lean_obj_tag(v_ctx_x3f_517_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_f_516_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_2(v_onMissingContext_515_, v___x_522_, lean_box(0));
v_msg_520_ = v___x_523_;
goto v___jp_519_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_525_; 
lean_dec_ref(v_onMissingContext_515_);
v_val_524_ = lean_ctor_get(v_ctx_x3f_517_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v_ctx_x3f_517_);
v___x_525_ = lean_apply_2(v_f_516_, v_val_524_, lean_box(0));
v_msg_520_ = v___x_525_;
goto v___jp_519_;
}
v___jp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_514_);
lean_ctor_set(v___x_521_, 1, v_msg_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_526_, lean_object* v_onMissingContext_527_, lean_object* v_f_528_, lean_object* v_ctx_x3f_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MessageData_lazy___lam__0(v___x_526_, v_onMissingContext_527_, v_f_528_, v_ctx_x3f_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_532_, lean_object* v_hasSyntheticSorry_533_, lean_object* v_onMissingContext_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___f_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___f_536_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_536_, 0, v___x_535_);
lean_closure_set(v___f_536_, 1, v_onMissingContext_534_);
lean_closure_set(v___f_536_, 2, v_f_532_);
v___x_537_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_537_, 0, v___f_536_);
lean_ctor_set(v___x_537_, 1, v_hasSyntheticSorry_533_);
return v___x_537_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_538_, lean_object* v_x_539_){
_start:
{
switch(lean_obj_tag(v_x_539_))
{
case 3:
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_540_);
lean_dec_ref(v_x_539_);
v_x_539_ = v_a_540_;
goto _start;
}
case 4:
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_542_);
lean_dec_ref(v_x_539_);
v_x_539_ = v_a_542_;
goto _start;
}
case 5:
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_544_);
lean_dec_ref(v_x_539_);
v_x_539_ = v_a_544_;
goto _start;
}
case 6:
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v_x_539_, 0);
lean_inc_ref(v_a_546_);
lean_dec_ref(v_x_539_);
v_x_539_ = v_a_546_;
goto _start;
}
case 7:
{
lean_object* v_a_548_; lean_object* v_a_549_; uint8_t v___x_550_; 
v_a_548_ = lean_ctor_get(v_x_539_, 0);
lean_inc_ref(v_a_548_);
v_a_549_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_549_);
lean_dec_ref(v_x_539_);
lean_inc_ref(v_p_538_);
v___x_550_ = l_Lean_MessageData_hasTag(v_p_538_, v_a_548_);
if (v___x_550_ == 0)
{
v_x_539_ = v_a_549_;
goto _start;
}
else
{
lean_dec_ref(v_a_549_);
lean_dec_ref(v_p_538_);
return v___x_550_;
}
}
case 8:
{
lean_object* v_a_552_; lean_object* v_a_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_a_552_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_552_);
v_a_553_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_553_);
lean_dec_ref(v_x_539_);
lean_inc_ref(v_p_538_);
v___x_554_ = lean_apply_1(v_p_538_, v_a_552_);
v___x_555_ = lean_unbox(v___x_554_);
if (v___x_555_ == 0)
{
v_x_539_ = v_a_553_;
goto _start;
}
else
{
uint8_t v___x_557_; 
lean_dec_ref(v_a_553_);
lean_dec_ref(v_p_538_);
v___x_557_ = lean_unbox(v___x_554_);
return v___x_557_;
}
}
case 9:
{
lean_object* v_data_558_; lean_object* v_msg_559_; lean_object* v_children_560_; lean_object* v_cls_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_data_558_ = lean_ctor_get(v_x_539_, 0);
lean_inc_ref(v_data_558_);
v_msg_559_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_msg_559_);
v_children_560_ = lean_ctor_get(v_x_539_, 2);
lean_inc_ref(v_children_560_);
lean_dec_ref(v_x_539_);
v_cls_561_ = lean_ctor_get(v_data_558_, 0);
lean_inc(v_cls_561_);
lean_dec_ref(v_data_558_);
lean_inc_ref(v_p_538_);
v___x_562_ = lean_apply_1(v_p_538_, v_cls_561_);
v___x_563_ = lean_unbox(v___x_562_);
if (v___x_563_ == 0)
{
uint8_t v___x_564_; 
lean_inc_ref(v_p_538_);
v___x_564_ = l_Lean_MessageData_hasTag(v_p_538_, v_msg_559_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_array_get_size(v_children_560_);
v___x_567_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec_ref(v_children_560_);
lean_dec_ref(v_p_538_);
return v___x_564_;
}
else
{
if (v___x_567_ == 0)
{
lean_dec_ref(v_children_560_);
lean_dec_ref(v_p_538_);
return v___x_564_;
}
else
{
size_t v___x_568_; size_t v___x_569_; uint8_t v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_566_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_538_, v_children_560_, v___x_568_, v___x_569_);
lean_dec_ref(v_children_560_);
return v___x_570_;
}
}
}
else
{
lean_dec_ref(v_children_560_);
lean_dec_ref(v_p_538_);
return v___x_564_;
}
}
else
{
uint8_t v___x_571_; 
lean_dec_ref(v_children_560_);
lean_dec_ref(v_msg_559_);
lean_dec_ref(v_p_538_);
v___x_571_ = lean_unbox(v___x_562_);
return v___x_571_;
}
}
default: 
{
uint8_t v___x_572_; 
lean_dec_ref(v_x_539_);
lean_dec_ref(v_p_538_);
v___x_572_ = 0;
return v___x_572_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
lean_inc(v___x_578_);
lean_inc_ref(v_p_573_);
v___x_579_ = l_Lean_MessageData_hasTag(v_p_573_, v___x_578_);
if (v___x_579_ == 0)
{
size_t v___x_580_; size_t v___x_581_; 
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_575_, v___x_580_);
v_i_575_ = v___x_581_;
goto _start;
}
else
{
lean_dec_ref(v_p_573_);
return v___x_579_;
}
}
else
{
uint8_t v___x_583_; 
lean_dec_ref(v_p_573_);
v___x_583_ = 0;
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_584_, lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_stop_587_){
_start:
{
size_t v_i_boxed_588_; size_t v_stop_boxed_589_; uint8_t v_res_590_; lean_object* v_r_591_; 
v_i_boxed_588_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_stop_boxed_589_ = lean_unbox_usize(v_stop_587_);
lean_dec(v_stop_587_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_584_, v_as_585_, v_i_boxed_588_, v_stop_boxed_589_);
lean_dec_ref(v_as_585_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_592_, lean_object* v_x_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Lean_MessageData_hasTag(v_p_592_, v_x_593_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_596_){
_start:
{
switch(lean_obj_tag(v_x_596_))
{
case 3:
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v_x_596_, 1);
v_x_596_ = v_a_597_;
goto _start;
}
case 4:
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v_x_596_, 1);
v_x_596_ = v_a_599_;
goto _start;
}
case 8:
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_a_601_);
return v_a_601_;
}
default: 
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(0);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_MessageData_kind(v_x_603_);
lean_dec_ref(v_x_603_);
return v_res_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_605_){
_start:
{
switch(lean_obj_tag(v_x_605_))
{
case 3:
{
lean_object* v_a_606_; 
v_a_606_ = lean_ctor_get(v_x_605_, 1);
v_x_605_ = v_a_606_;
goto _start;
}
case 4:
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v_x_605_, 1);
v_x_605_ = v_a_608_;
goto _start;
}
case 8:
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v_x_605_, 1);
v_x_605_ = v_a_610_;
goto _start;
}
case 9:
{
uint8_t v___x_612_; 
v___x_612_ = 1;
return v___x_612_;
}
default: 
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Lean_MessageData_isTrace(v_x_614_);
lean_dec_ref(v_x_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
switch(lean_obj_tag(v_x_617_))
{
case 3:
{
lean_object* v_a_619_; lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
v_a_619_ = lean_ctor_get(v_x_617_, 0);
v_a_620_ = lean_ctor_get(v_x_617_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v_x_617_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_inc(v_a_619_);
lean_dec(v_x_617_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = l_Lean_MessageData_composePreservingKind(v_a_620_, v_x_618_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_619_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
case 4:
{
lean_object* v_a_629_; lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_a_629_ = lean_ctor_get(v_x_617_, 0);
v_a_630_ = lean_ctor_get(v_x_617_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v_x_617_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_inc(v_a_629_);
lean_dec(v_x_617_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = l_Lean_MessageData_composePreservingKind(v_a_630_, v_x_618_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
case 8:
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_a_639_ = lean_ctor_get(v_x_617_, 0);
v_a_640_ = lean_ctor_get(v_x_617_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_x_617_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v_x_617_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 7);
lean_ctor_set(v___x_642_, 1, v_x_618_);
lean_ctor_set(v___x_642_, 0, v_a_640_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_640_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_x_618_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_646_, 0, v_a_639_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v_x_617_);
lean_ctor_set(v___x_649_, 1, v_x_618_);
return v___x_649_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = l_Lean_MessageData_ofFormat(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_653_, lean_object* v_ctx_654_){
_start:
{
lean_object* v_env_655_; lean_object* v_mctx_656_; lean_object* v_lctx_657_; lean_object* v_opts_658_; lean_object* v_currNamespace_659_; lean_object* v_openDecls_660_; lean_object* v___x_661_; 
v_env_655_ = lean_ctor_get(v_ctx_654_, 0);
v_mctx_656_ = lean_ctor_get(v_ctx_654_, 1);
v_lctx_657_ = lean_ctor_get(v_ctx_654_, 2);
v_opts_658_ = lean_ctor_get(v_ctx_654_, 3);
v_currNamespace_659_ = lean_ctor_get(v_nCtx_653_, 0);
v_openDecls_660_ = lean_ctor_get(v_nCtx_653_, 1);
lean_inc(v_openDecls_660_);
lean_inc(v_currNamespace_659_);
lean_inc_ref(v_opts_658_);
lean_inc_ref(v_lctx_657_);
lean_inc_ref(v_mctx_656_);
lean_inc_ref(v_env_655_);
v___x_661_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_661_, 0, v_env_655_);
lean_ctor_set(v___x_661_, 1, v_mctx_656_);
lean_ctor_set(v___x_661_, 2, v_lctx_657_);
lean_ctor_set(v___x_661_, 3, v_opts_658_);
lean_ctor_set(v___x_661_, 4, v_currNamespace_659_);
lean_ctor_set(v___x_661_, 5, v_openDecls_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_662_, lean_object* v_ctx_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_MessageData_mkPPContext(v_nCtx_662_, v_ctx_663_);
lean_dec_ref(v_ctx_663_);
lean_dec_ref(v_nCtx_662_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_667_);
lean_dec_ref(v_x_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_670_, lean_object* v_stx_671_, lean_object* v_ctx_x3f_672_){
_start:
{
lean_object* v_val_675_; 
if (lean_obj_tag(v_ctx_x3f_672_) == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(0);
v___x_679_ = 0;
v___x_680_ = l_Lean_Syntax_formatStx(v_stx_671_, v___x_678_, v___x_679_);
v_val_675_ = v___x_680_;
goto v___jp_674_;
}
else
{
lean_object* v_val_681_; lean_object* v___x_682_; 
v_val_681_ = lean_ctor_get(v_ctx_x3f_672_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v_ctx_x3f_672_);
v___x_682_ = l_Lean_ppTerm(v_val_681_, v_stx_671_);
v_val_675_ = v___x_682_;
goto v___jp_674_;
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Lean_MessageData_ofFormat(v_val_675_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_670_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_683_, lean_object* v_stx_684_, lean_object* v_ctx_x3f_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_683_, v_stx_684_, v_ctx_x3f_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_stx_693_; lean_object* v___f_694_; lean_object* v___x_695_; 
v___f_690_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_691_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___x_692_ = lean_box(0);
v_stx_693_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_689_, v___x_692_);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_694_, 0, v___x_691_);
lean_closure_set(v___f_694_, 1, v_stx_693_);
v___x_695_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_695_, 0, v___f_694_);
lean_ctor_set(v___x_695_, 1, v___f_690_);
return v___x_695_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_696_, lean_object* v_mctx_697_){
_start:
{
lean_object* v___x_698_; lean_object* v_fst_699_; uint8_t v___x_700_; 
v___x_698_ = l_Lean_instantiateMVarsCore(v_mctx_697_, v_e_696_);
v_fst_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_fst_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = l_Lean_Expr_hasSyntheticSorry(v_fst_699_);
lean_dec(v_fst_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_701_, lean_object* v_mctx_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean_MessageData_ofExpr___lam__0(v_e_701_, v_mctx_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_705_, lean_object* v_e_706_, lean_object* v_ctx_x3f_707_){
_start:
{
lean_object* v_val_710_; 
if (lean_obj_tag(v_ctx_x3f_707_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = lean_expr_dbg_to_string(v_e_706_);
lean_dec_ref(v_e_706_);
v___x_714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___x_715_ = lean_box(1);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v_val_710_ = v___x_716_;
goto v___jp_709_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_718_; 
v_val_717_ = lean_ctor_get(v_ctx_x3f_707_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v_ctx_x3f_707_);
v___x_718_ = l_Lean_ppExprWithInfos(v_val_717_, v_e_706_);
v_val_710_ = v___x_718_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_val_710_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_705_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_719_, lean_object* v_e_720_, lean_object* v_ctx_x3f_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_MessageData_ofExpr___lam__1(v___x_719_, v_e_720_, v_ctx_x3f_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_724_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; 
lean_inc_ref(v_e_724_);
v___f_725_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_725_, 0, v_e_724_);
v___x_726_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___f_727_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_727_, 0, v___x_726_);
lean_closure_set(v___f_727_, 1, v_e_724_);
v___x_728_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_728_, 0, v___f_727_);
lean_ctor_set(v___x_728_, 1, v___f_725_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_MessageData_ofLevel___lam__0(v_x_731_);
lean_dec(v_x_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_733_, lean_object* v_l_734_, lean_object* v___f_735_, lean_object* v_ctx_x3f_736_){
_start:
{
lean_object* v_val_739_; 
if (lean_obj_tag(v_ctx_x3f_736_) == 0)
{
uint8_t v___x_742_; lean_object* v___x_743_; 
v___x_742_ = 1;
v___x_743_ = l_Lean_Level_format(v_l_734_, v___x_742_, v___f_735_);
v_val_739_ = v___x_743_;
goto v___jp_738_;
}
else
{
lean_object* v_val_744_; lean_object* v___x_745_; 
lean_dec_ref(v___f_735_);
v_val_744_ = lean_ctor_get(v_ctx_x3f_736_, 0);
lean_inc(v_val_744_);
lean_dec_ref(v_ctx_x3f_736_);
v___x_745_ = l_Lean_ppLevel(v_val_744_, v_l_734_);
v_val_739_ = v___x_745_;
goto v___jp_738_;
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_MessageData_ofFormat(v_val_739_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_733_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_746_, lean_object* v_l_747_, lean_object* v___f_748_, lean_object* v_ctx_x3f_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_MessageData_ofLevel___lam__2(v___x_746_, v_l_747_, v___f_748_, v_ctx_x3f_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_753_){
_start:
{
lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v___f_754_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_755_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_756_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___f_757_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_757_, 0, v___x_756_);
lean_closure_set(v___f_757_, 1, v_l_753_);
lean_closure_set(v___f_757_, 2, v___f_754_);
v___x_758_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_758_, 0, v___f_757_);
lean_ctor_set(v___x_758_, 1, v___f_755_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_759_){
_start:
{
uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = 1;
v___x_761_ = l_Lean_Name_toString(v_n_759_, v___x_760_);
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = l_Lean_MessageData_ofFormat(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_767_, lean_object* v_k_768_, uint8_t v_v_769_){
_start:
{
lean_object* v_map_770_; uint8_t v_hasTrace_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_785_; 
v_map_770_ = lean_ctor_get(v_o_767_, 0);
v_hasTrace_771_ = lean_ctor_get_uint8(v_o_767_, sizeof(void*)*1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_o_767_);
if (v_isSharedCheck_785_ == 0)
{
v___x_773_ = v_o_767_;
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_map_770_);
lean_dec(v_o_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_775_, 0, v_v_769_);
lean_inc(v_k_768_);
v___x_776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_768_, v___x_775_, v_map_770_);
if (v_hasTrace_771_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_780_; 
v___x_777_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_778_ = l_Lean_Name_isPrefixOf(v___x_777_, v_k_768_);
lean_dec(v_k_768_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_776_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_776_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*1, v___x_778_);
return v___x_780_;
}
}
else
{
lean_object* v___x_783_; 
lean_dec(v_k_768_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_776_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*1, v_hasTrace_771_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_786_, lean_object* v_k_787_, lean_object* v_v_788_){
_start:
{
uint8_t v_v_boxed_789_; lean_object* v_res_790_; 
v_v_boxed_789_ = lean_unbox(v_v_788_);
v_res_790_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_786_, v_k_787_, v_v_boxed_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_796_, lean_object* v_constName_797_, uint8_t v_fullNames_798_, lean_object* v_ctx_x3f_799_){
_start:
{
lean_object* v_val_802_; lean_object* v___y_806_; 
if (lean_obj_tag(v_ctx_x3f_799_) == 0)
{
uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_807_ = 1;
v___x_808_ = l_Lean_Name_toString(v_constName_797_, v___x_807_);
v___x_809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = lean_box(1);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v_val_802_ = v___x_811_;
goto v___jp_801_;
}
else
{
if (v_fullNames_798_ == 0)
{
lean_object* v_val_812_; lean_object* v___x_813_; 
v_val_812_ = lean_ctor_get(v_ctx_x3f_799_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v_ctx_x3f_799_);
v___x_813_ = l_Lean_ppConstNameWithInfos(v_val_812_, v_constName_797_);
v___y_806_ = v___x_813_;
goto v___jp_805_;
}
else
{
lean_object* v_val_814_; lean_object* v_env_815_; lean_object* v_mctx_816_; lean_object* v_lctx_817_; lean_object* v_opts_818_; lean_object* v_currNamespace_819_; lean_object* v_openDecls_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
v_val_814_ = lean_ctor_get(v_ctx_x3f_799_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v_ctx_x3f_799_);
v_env_815_ = lean_ctor_get(v_val_814_, 0);
v_mctx_816_ = lean_ctor_get(v_val_814_, 1);
v_lctx_817_ = lean_ctor_get(v_val_814_, 2);
v_opts_818_ = lean_ctor_get(v_val_814_, 3);
v_currNamespace_819_ = lean_ctor_get(v_val_814_, 4);
v_openDecls_820_ = lean_ctor_get(v_val_814_, 5);
v_isSharedCheck_830_ = !lean_is_exclusive(v_val_814_);
if (v_isSharedCheck_830_ == 0)
{
v___x_822_ = v_val_814_;
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_openDecls_820_);
lean_inc(v_currNamespace_819_);
lean_inc(v_opts_818_);
lean_inc(v_lctx_817_);
lean_inc(v_mctx_816_);
lean_inc(v_env_815_);
lean_dec(v_val_814_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_825_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_818_, v___x_824_, v_fullNames_798_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 3, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_env_815_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_mctx_816_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_lctx_817_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_currNamespace_819_);
lean_ctor_set(v_reuseFailAlloc_829_, 5, v_openDecls_820_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_ppConstNameWithInfos(v___x_827_, v_constName_797_);
v___y_806_ = v___x_828_;
goto v___jp_805_;
}
}
}
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_val_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_796_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
v___jp_805_:
{
v_val_802_ = v___y_806_;
goto v___jp_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_831_, lean_object* v_constName_832_, lean_object* v_fullNames_833_, lean_object* v_ctx_x3f_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_fullNames_boxed_836_; lean_object* v_res_837_; 
v_fullNames_boxed_836_ = lean_unbox(v_fullNames_833_);
v_res_837_ = l_Lean_MessageData_ofConstName___lam__1(v___x_831_, v_constName_832_, v_fullNames_boxed_836_, v_ctx_x3f_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_838_, uint8_t v_fullNames_839_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; 
v___f_840_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_841_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___x_842_ = lean_box(v_fullNames_839_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_843_, 0, v___x_841_);
lean_closure_set(v___f_843_, 1, v_constName_838_);
lean_closure_set(v___f_843_, 2, v___x_842_);
v___x_844_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_844_, 0, v___f_843_);
lean_ctor_set(v___x_844_, 1, v___f_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_845_, lean_object* v_fullNames_846_){
_start:
{
uint8_t v_fullNames_boxed_847_; lean_object* v_res_848_; 
v_fullNames_boxed_847_ = lean_unbox(v_fullNames_846_);
v_res_848_ = l_Lean_MessageData_ofConstName(v_constName_845_, v_fullNames_boxed_847_);
return v_res_848_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_ctor_set(v___x_854_, 3, v___x_853_);
lean_ctor_set(v___x_854_, 4, v___x_852_);
lean_ctor_set(v___x_854_, 5, v___x_852_);
lean_ctor_set(v___x_854_, 6, v___x_852_);
lean_ctor_set(v___x_854_, 7, v___x_852_);
lean_ctor_set(v___x_854_, 8, v___x_852_);
lean_ctor_set(v___x_854_, 9, v___x_852_);
return v___x_854_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_855_, lean_object* v_a_856_){
_start:
{
switch(lean_obj_tag(v_a_856_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_855_) == 0)
{
lean_object* v_hasSyntheticSorry_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_hasSyntheticSorry_857_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_hasSyntheticSorry_857_);
lean_dec_ref(v_a_856_);
v___x_858_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_859_ = lean_apply_1(v_hasSyntheticSorry_857_, v___x_858_);
v___x_860_ = lean_unbox(v___x_859_);
return v___x_860_;
}
else
{
lean_object* v_hasSyntheticSorry_861_; lean_object* v_val_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_hasSyntheticSorry_861_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_hasSyntheticSorry_861_);
lean_dec_ref(v_a_856_);
v_val_862_ = lean_ctor_get(v_mctx_x3f_855_, 0);
lean_inc(v_val_862_);
lean_dec_ref(v_mctx_x3f_855_);
v___x_863_ = lean_apply_1(v_hasSyntheticSorry_861_, v_val_862_);
v___x_864_ = lean_unbox(v___x_863_);
return v___x_864_;
}
}
case 3:
{
lean_object* v_a_865_; lean_object* v_a_866_; lean_object* v_mctx_867_; lean_object* v___x_868_; 
lean_dec(v_mctx_x3f_855_);
v_a_865_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_a_865_);
v_a_866_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_a_866_);
lean_dec_ref(v_a_856_);
v_mctx_867_ = lean_ctor_get(v_a_865_, 1);
lean_inc_ref(v_mctx_867_);
lean_dec_ref(v_a_865_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_mctx_867_);
v_mctx_x3f_855_ = v___x_868_;
v_a_856_ = v_a_866_;
goto _start;
}
case 4:
{
lean_object* v_a_870_; 
v_a_870_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_a_870_);
lean_dec_ref(v_a_856_);
v_a_856_ = v_a_870_;
goto _start;
}
case 5:
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_a_872_);
lean_dec_ref(v_a_856_);
v_a_856_ = v_a_872_;
goto _start;
}
case 6:
{
lean_object* v_a_874_; 
v_a_874_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_a_874_);
lean_dec_ref(v_a_856_);
v_a_856_ = v_a_874_;
goto _start;
}
case 7:
{
lean_object* v_a_876_; lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_876_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_a_876_);
v_a_877_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_a_877_);
lean_dec_ref(v_a_856_);
lean_inc(v_mctx_x3f_855_);
v___x_878_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_855_, v_a_876_);
if (v___x_878_ == 0)
{
v_a_856_ = v_a_877_;
goto _start;
}
else
{
lean_dec_ref(v_a_877_);
lean_dec(v_mctx_x3f_855_);
return v___x_878_;
}
}
case 8:
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_a_880_);
lean_dec_ref(v_a_856_);
v_a_856_ = v_a_880_;
goto _start;
}
case 9:
{
lean_object* v_msg_882_; lean_object* v_children_883_; uint8_t v___x_884_; 
v_msg_882_ = lean_ctor_get(v_a_856_, 1);
lean_inc_ref(v_msg_882_);
v_children_883_ = lean_ctor_get(v_a_856_, 2);
lean_inc_ref(v_children_883_);
lean_dec_ref(v_a_856_);
lean_inc(v_mctx_x3f_855_);
v___x_884_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_855_, v_msg_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_array_get_size(v_children_883_);
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec_ref(v_children_883_);
lean_dec(v_mctx_x3f_855_);
return v___x_884_;
}
else
{
if (v___x_887_ == 0)
{
lean_dec_ref(v_children_883_);
lean_dec(v_mctx_x3f_855_);
return v___x_884_;
}
else
{
size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v___x_888_ = ((size_t)0ULL);
v___x_889_ = lean_usize_of_nat(v___x_886_);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_855_, v_children_883_, v___x_888_, v___x_889_);
lean_dec_ref(v_children_883_);
return v___x_890_;
}
}
}
else
{
lean_dec_ref(v_children_883_);
lean_dec(v_mctx_x3f_855_);
return v___x_884_;
}
}
default: 
{
uint8_t v___x_891_; 
lean_dec_ref(v_a_856_);
lean_dec(v_mctx_x3f_855_);
v___x_891_ = 0;
return v___x_891_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_892_, lean_object* v_as_893_, size_t v_i_894_, size_t v_stop_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_eq(v_i_894_, v_stop_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_array_uget_borrowed(v_as_893_, v_i_894_);
lean_inc(v___x_897_);
lean_inc(v_mctx_x3f_892_);
v___x_898_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_892_, v___x_897_);
if (v___x_898_ == 0)
{
size_t v___x_899_; size_t v___x_900_; 
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_894_, v___x_899_);
v_i_894_ = v___x_900_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_892_);
return v___x_898_;
}
}
else
{
uint8_t v___x_902_; 
lean_dec(v_mctx_x3f_892_);
v___x_902_ = 0;
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_903_, lean_object* v_as_904_, lean_object* v_i_905_, lean_object* v_stop_906_){
_start:
{
size_t v_i_boxed_907_; size_t v_stop_boxed_908_; uint8_t v_res_909_; lean_object* v_r_910_; 
v_i_boxed_907_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_stop_boxed_908_ = lean_unbox_usize(v_stop_906_);
lean_dec(v_stop_906_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_903_, v_as_904_, v_i_boxed_907_, v_stop_boxed_908_);
lean_dec_ref(v_as_904_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_911_, v_a_912_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_box(0);
v___x_917_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_916_, v_msg_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_918_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_921_, lean_object* v_decl_922_, lean_object* v_ref_923_){
_start:
{
lean_object* v_defValue_925_; lean_object* v_descr_926_; lean_object* v_deprecation_x3f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_defValue_925_ = lean_ctor_get(v_decl_922_, 0);
v_descr_926_ = lean_ctor_get(v_decl_922_, 1);
v_deprecation_x3f_927_ = lean_ctor_get(v_decl_922_, 2);
lean_inc(v_defValue_925_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v_defValue_925_);
lean_inc(v_deprecation_x3f_927_);
lean_inc_ref(v_descr_926_);
lean_inc_n(v_name_921_, 2);
v___x_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_929_, 0, v_name_921_);
lean_ctor_set(v___x_929_, 1, v_ref_923_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v_descr_926_);
lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_927_);
v___x_930_ = lean_register_option(v_name_921_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_939_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v_defValue_925_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_name_921_);
lean_ctor_set(v___x_934_, 1, v_defValue_925_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
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
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_name_921_);
v_a_940_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_948_, lean_object* v_decl_949_, lean_object* v_ref_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
lean_dec_ref(v_decl_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_967_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_968_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_969_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_966_, v___x_967_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_nat_to_int(v_a_972_);
return v___x_973_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
v___x_975_ = l_instMonadBaseIO;
v___x_976_ = l_instInhabitedOfMonad___redArg(v___x_975_, v___x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_2068__overap_980_; lean_object* v___x_981_; 
v___x_979_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2068__overap_980_ = lean_panic_fn_borrowed(v___x_979_, v_msg_977_);
v___x_981_ = lean_apply_1(v___x_2068__overap_980_, lean_box(0));
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_dec(v_x_985_);
return v_x_986_;
}
else
{
lean_object* v_head_988_; lean_object* v_tail_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v_head_988_ = lean_ctor_get(v_x_987_, 0);
v_tail_989_ = lean_ctor_get(v_x_987_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_987_);
if (v_isSharedCheck_998_ == 0)
{
v___x_991_ = v_x_987_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_tail_989_);
lean_inc(v_head_988_);
lean_dec(v_x_987_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
lean_inc(v_x_985_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 5);
lean_ctor_set(v___x_991_, 1, v_x_985_);
lean_ctor_set(v___x_991_, 0, v_x_986_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_x_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_x_985_);
v___x_994_ = v_reuseFailAlloc_997_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_head_988_);
v_x_986_ = v___x_995_;
v_x_987_ = v_tail_989_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_x_1000_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
else
{
lean_object* v_tail_1002_; 
v_tail_1002_ = lean_ctor_get(v_x_999_, 1);
if (lean_obj_tag(v_tail_1002_) == 0)
{
lean_object* v_head_1003_; 
lean_dec(v_x_1000_);
v_head_1003_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_head_1003_);
lean_dec_ref(v_x_999_);
return v_head_1003_;
}
else
{
lean_object* v_head_1004_; lean_object* v___x_1005_; 
lean_inc(v_tail_1002_);
v_head_1004_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_head_1004_);
lean_dec_ref(v_x_999_);
v___x_1005_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1000_, v_head_1004_, v_tail_1002_);
return v___x_1005_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1020_; double v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_float_of_nat(v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
switch(lean_obj_tag(v_x_1027_))
{
case 0:
{
lean_object* v_a_1029_; lean_object* v_fmt_1030_; 
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1025_);
v_a_1029_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_a_1029_);
lean_dec_ref(v_x_1027_);
v_fmt_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_fmt_1030_);
lean_dec_ref(v_a_1029_);
return v_fmt_1030_;
}
case 1:
{
if (lean_obj_tag(v_x_1026_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_x_1025_);
v_a_1031_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v_x_1027_);
v___x_1032_ = l_Lean_formatRawGoal(v_a_1031_);
return v___x_1032_;
}
else
{
lean_object* v_a_1033_; lean_object* v_val_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1033_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v_x_1027_);
v_val_1034_ = lean_ctor_get(v_x_1026_, 0);
lean_inc(v_val_1034_);
lean_dec_ref(v_x_1026_);
v___x_1035_ = l_Lean_MessageData_mkPPContext(v_x_1025_, v_val_1034_);
lean_dec(v_val_1034_);
lean_dec_ref(v_x_1025_);
v___x_1036_ = l_Lean_ppGoal(v___x_1035_, v_a_1033_);
return v___x_1036_;
}
}
case 3:
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_x_1026_);
v_a_1037_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_x_1027_, 1);
lean_inc_ref(v_a_1038_);
lean_dec_ref(v_x_1027_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1037_);
v_x_1026_ = v___x_1039_;
v_x_1027_ = v_a_1038_;
goto _start;
}
case 4:
{
lean_object* v_a_1041_; lean_object* v_a_1042_; 
lean_dec_ref(v_x_1025_);
v_a_1041_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_a_1041_);
v_a_1042_ = lean_ctor_get(v_x_1027_, 1);
lean_inc_ref(v_a_1042_);
lean_dec_ref(v_x_1027_);
v_x_1025_ = v_a_1041_;
v_x_1027_ = v_a_1042_;
goto _start;
}
case 5:
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1054_; 
v_a_1044_ = lean_ctor_get(v_x_1027_, 0);
v_a_1045_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1047_ = v_x_1027_;
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_inc(v_a_1044_);
lean_dec(v_x_1027_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = l_Lean_MessageData_formatAux(v_x_1025_, v_x_1026_, v_a_1045_);
v___x_1050_ = lean_nat_to_int(v_a_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 4);
lean_ctor_set(v___x_1047_, 1, v___x_1049_);
lean_ctor_set(v___x_1047_, 0, v___x_1050_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1049_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
case 6:
{
lean_object* v_a_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; 
v_a_1055_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_a_1055_);
lean_dec_ref(v_x_1027_);
v___x_1056_ = l_Lean_MessageData_formatAux(v_x_1025_, v_x_1026_, v_a_1055_);
v___x_1057_ = 0;
v___x_1058_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*1, v___x_1057_);
return v___x_1058_;
}
case 7:
{
lean_object* v_a_1059_; lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1069_; 
v_a_1059_ = lean_ctor_get(v_x_1027_, 0);
v_a_1060_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1062_ = v_x_1027_;
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_inc(v_a_1059_);
lean_dec(v_x_1027_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_inc(v_x_1026_);
lean_inc_ref(v_x_1025_);
v___x_1064_ = l_Lean_MessageData_formatAux(v_x_1025_, v_x_1026_, v_a_1059_);
v___x_1065_ = l_Lean_MessageData_formatAux(v_x_1025_, v_x_1026_, v_a_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 5);
lean_ctor_set(v___x_1062_, 1, v___x_1065_);
lean_ctor_set(v___x_1062_, 0, v___x_1064_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
case 9:
{
lean_object* v_data_1070_; lean_object* v_msg_1071_; lean_object* v_children_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v_msg_1077_; lean_object* v_cls_1089_; double v_startTime_1090_; double v_stopTime_1091_; uint8_t v___x_1092_; 
v_data_1070_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_data_1070_);
v_msg_1071_ = lean_ctor_get(v_x_1027_, 1);
lean_inc_ref(v_msg_1071_);
v_children_1072_ = lean_ctor_get(v_x_1027_, 2);
lean_inc_ref(v_children_1072_);
lean_dec_ref(v_x_1027_);
v_sz_1073_ = lean_array_size(v_children_1072_);
v___x_1074_ = ((size_t)0ULL);
lean_inc(v_x_1026_);
lean_inc_ref(v_x_1025_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1025_, v_x_1026_, v_sz_1073_, v___x_1074_, v_children_1072_);
v_cls_1089_ = lean_ctor_get(v_data_1070_, 0);
lean_inc(v_cls_1089_);
v_startTime_1090_ = lean_ctor_get_float(v_data_1070_, sizeof(void*)*3);
v_stopTime_1091_ = lean_ctor_get_float(v_data_1070_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1070_);
v___x_1092_ = l_Lean_Name_isAnonymous(v_cls_1089_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; double v___x_1108_; uint8_t v___x_1109_; 
v___x_1093_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1094_ = 1;
v___x_1095_ = l_Lean_Name_toString(v_cls_1089_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1093_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1108_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1109_ = lean_float_beq(v_startTime_1090_, v___x_1108_);
if (v___x_1109_ == 0)
{
goto v___jp_1100_;
}
else
{
if (v___x_1092_ == 0)
{
v_msg_1077_ = v___x_1099_;
goto v___jp_1076_;
}
else
{
goto v___jp_1100_;
}
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; double v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1101_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_float_sub(v_stopTime_1091_, v_startTime_1090_);
v___x_1104_ = lean_float_to_string(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1102_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1098_);
v_msg_1077_ = v___x_1107_;
goto v___jp_1076_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_cls_1089_);
lean_dec_ref(v_msg_1071_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1025_);
v___x_1110_ = lean_array_to_list(v___x_1075_);
v___x_1111_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1112_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1110_, v___x_1111_);
return v___x_1112_;
}
v___jp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1078_ = l_Lean_MessageData_formatAux(v_x_1025_, v_x_1026_, v_msg_1071_);
v___x_1079_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_msg_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1078_);
v___x_1083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1080_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_array_to_list(v___x_1075_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1087_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1085_, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1081_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
return v___x_1088_;
}
}
case 10:
{
lean_object* v_f_1113_; lean_object* v___x_1114_; lean_object* v___y_1116_; 
v_f_1113_ = lean_ctor_get(v_x_1027_, 0);
lean_inc_ref(v_f_1113_);
lean_dec_ref(v_x_1027_);
v___x_1114_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
if (lean_obj_tag(v_x_1026_) == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_box(0);
v___y_1116_ = v___x_1132_;
goto v___jp_1115_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_val_1133_ = lean_ctor_get(v_x_1026_, 0);
v___x_1134_ = l_Lean_MessageData_mkPPContext(v_x_1025_, v_val_1133_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___y_1116_ = v___x_1135_;
goto v___jp_1115_;
}
v___jp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_apply_2(v_f_1113_, v___y_1116_, lean_box(0));
v___x_1118_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1117_, v___x_1114_);
if (lean_obj_tag(v___x_1118_) == 1)
{
lean_object* v_val_1119_; 
lean_dec(v___x_1117_);
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1119_);
lean_dec_ref(v___x_1118_);
v_x_1027_ = v_val_1119_;
goto _start;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___x_1118_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1025_);
v___x_1121_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1122_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1123_ = lean_unsigned_to_nat(330u);
v___x_1124_ = lean_unsigned_to_nat(8u);
v___x_1125_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1126_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1117_);
lean_dec(v___x_1117_);
v___x_1127_ = 1;
v___x_1128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_string_append(v___x_1125_, v___x_1128_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_mkPanicMessageWithDecl(v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1130_);
return v___x_1131_;
}
}
}
default: 
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v_x_1027_, 1);
lean_inc_ref(v_a_1136_);
lean_dec_ref(v_x_1027_);
v_x_1027_ = v_a_1136_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1138_, lean_object* v_x_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_bs_1142_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
if (v___x_1144_ == 0)
{
lean_dec(v_x_1139_);
lean_dec_ref(v_x_1138_);
return v_bs_1142_;
}
else
{
lean_object* v_v_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_bs_x27_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v_v_1145_ = lean_array_uget_borrowed(v_bs_1142_, v_i_1141_);
lean_inc(v_v_1145_);
lean_inc(v_x_1139_);
lean_inc_ref(v_x_1138_);
v___x_1146_ = l_Lean_MessageData_formatAux(v_x_1138_, v_x_1139_, v_v_1145_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v_bs_x27_1148_ = lean_array_uset(v_bs_1142_, v_i_1141_, v___x_1147_);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1141_, v___x_1149_);
v___x_1151_ = lean_array_uset(v_bs_x27_1148_, v_i_1141_, v___x_1146_);
v_i_1141_ = v___x_1150_;
v_bs_1142_ = v___x_1151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_bs_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1153_, v_x_1154_, v_sz_boxed_1159_, v_i_boxed_1160_, v_bs_1157_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_MessageData_formatAux(v_x_1162_, v_x_1163_, v_x_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1170_, lean_object* v_ctx_x3f_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1174_ = l_Lean_MessageData_formatAux(v___x_1173_, v_ctx_x3f_1171_, v_msgData_1170_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1175_, lean_object* v_ctx_x3f_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_MessageData_format(v_msgData_1175_, v_ctx_x3f_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_MessageData_format(v_msgData_1179_, v___x_1181_);
v___x_1183_ = l_Std_Format_defWidth;
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = l_Std_Format_pretty(v___x_1182_, v___x_1183_, v___x_1184_, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_MessageData_toString(v_msgData_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1189_);
lean_ctor_set(v___x_1191_, 1, v_a_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_s_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1219_ = l_Lean_MessageData_ofFormat(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1220_){
_start:
{
if (lean_obj_tag(v_o_1220_) == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1221_;
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1223_; 
v_val_1222_ = lean_ctor_get(v_o_1220_, 0);
lean_inc(v_val_1222_);
lean_dec_ref(v_o_1220_);
v___x_1223_ = l_Lean_MessageData_ofExpr(v_val_1222_);
return v___x_1223_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1227_ = l_Lean_MessageData_ofFormat(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1232_ = l_Lean_MessageData_ofFormat(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1233_, lean_object* v_i_1234_, lean_object* v_acc_1235_){
_start:
{
lean_object* v___y_1237_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v_es_1233_);
v___x_1242_ = lean_nat_dec_lt(v_i_1234_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_i_1234_);
v___x_1243_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_acc_1235_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_e_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_e_1245_ = lean_array_fget_borrowed(v_es_1233_, v_i_1234_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_nat_dec_eq(v_i_1234_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_acc_1235_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_inc(v_e_1245_);
v___x_1250_ = l_Lean_MessageData_ofExpr(v_e_1245_);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___y_1237_ = v___x_1251_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_inc(v_e_1245_);
v___x_1252_ = l_Lean_MessageData_ofExpr(v_e_1245_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_acc_1235_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___y_1237_ = v___x_1253_;
goto v___jp_1236_;
}
}
v___jp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_i_1234_, v___x_1238_);
lean_dec(v_i_1234_);
v_i_1234_ = v___x_1239_;
v_acc_1235_ = v___y_1237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1254_, lean_object* v_i_1255_, lean_object* v_acc_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1254_, v_i_1255_, v_acc_1256_);
lean_dec_ref(v_es_1254_);
return v_res_1257_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1262_ = l_Lean_MessageData_ofFormat(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1266_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1263_, v___x_1264_, v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1267_);
lean_dec_ref(v_es_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1271_, lean_object* v_f_1272_, lean_object* v_r_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1274_ = lean_string_length(v_l_1271_);
v___x_1275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_l_1271_);
v___x_1276_ = l_Lean_MessageData_ofFormat(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_f_1272_);
v___x_1278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_r_1273_);
v___x_1279_ = l_Lean_MessageData_ofFormat(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1277_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1274_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1285_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1286_ = l_Lean_MessageData_bracket(v___x_1284_, v_f_1283_, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1289_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1290_ = l_Lean_MessageData_bracket(v___x_1288_, v_f_1287_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref(v_x_1292_);
v___x_1293_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1293_;
}
else
{
lean_object* v_tail_1294_; 
v_tail_1294_ = lean_ctor_get(v_x_1291_, 1);
if (lean_obj_tag(v_tail_1294_) == 0)
{
lean_object* v_head_1295_; 
lean_dec_ref(v_x_1292_);
v_head_1295_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_head_1295_);
lean_dec_ref(v_x_1291_);
return v_head_1295_;
}
else
{
lean_object* v_head_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1305_; 
lean_inc(v_tail_1294_);
v_head_1296_ = lean_ctor_get(v_x_1291_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_x_1291_, 1);
lean_dec(v_unused_1306_);
v___x_1298_ = v_x_1291_;
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_head_1296_);
lean_dec(v_x_1291_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
lean_inc_ref(v_x_1292_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 7);
lean_ctor_set(v___x_1298_, 1, v_x_1292_);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_head_1296_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_x_1292_);
v___x_1301_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = l_Lean_MessageData_joinSep(v_tail_1294_, v_x_1292_);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
return v___x_1303_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1311_ = l_Lean_MessageData_ofFormat(v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1316_ = l_Lean_MessageData_ofFormat(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(1);
v___x_1318_ = l_Lean_MessageData_ofFormat(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1320_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1325_ = l_Lean_MessageData_joinSep(v_x_1322_, v___x_1324_);
v___x_1326_ = l_Lean_MessageData_sbracket(v___x_1325_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_array_to_list(v_msgs_1327_);
v___x_1329_ = l_Lean_MessageData_ofList(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1334_ = l_Lean_MessageData_ofFormat(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1339_ = l_Lean_MessageData_ofFormat(v___x_1338_);
return v___x_1339_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1344_ = l_Lean_MessageData_ofFormat(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1345_){
_start:
{
if (lean_obj_tag(v_xs_1345_) == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1346_;
}
else
{
lean_object* v_tail_1347_; 
v_tail_1347_ = lean_ctor_get(v_xs_1345_, 1);
lean_inc(v_tail_1347_);
if (lean_obj_tag(v_tail_1347_) == 0)
{
lean_object* v_head_1348_; 
v_head_1348_ = lean_ctor_get(v_xs_1345_, 0);
lean_inc(v_head_1348_);
lean_dec_ref(v_xs_1345_);
return v_head_1348_;
}
else
{
lean_object* v_tail_1349_; 
v_tail_1349_ = lean_ctor_get(v_tail_1347_, 1);
if (lean_obj_tag(v_tail_1349_) == 0)
{
lean_object* v_head_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1367_; 
v_head_1350_ = lean_ctor_get(v_xs_1345_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_xs_1345_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v_xs_1345_, 1);
lean_dec(v_unused_1368_);
v___x_1352_ = v_xs_1345_;
v_isShared_1353_ = v_isSharedCheck_1367_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_head_1350_);
lean_dec(v_xs_1345_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1367_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_head_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1365_; 
v_head_1354_ = lean_ctor_get(v_tail_1347_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_tail_1347_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_tail_1347_, 1);
lean_dec(v_unused_1366_);
v___x_1356_ = v_tail_1347_;
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_head_1354_);
lean_dec(v_tail_1347_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 7);
lean_ctor_set(v___x_1356_, 1, v___x_1358_);
lean_ctor_set(v___x_1356_, 0, v_head_1350_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_head_1350_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 7);
lean_ctor_set(v___x_1352_, 1, v_head_1354_);
lean_ctor_set(v___x_1352_, 0, v___x_1360_);
v___x_1362_ = v___x_1352_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_head_1354_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
else
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v_tail_1347_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1393_ = lean_ctor_get(v_tail_1347_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_tail_1347_, 0);
lean_dec(v_unused_1394_);
v___x_1370_ = v_tail_1347_;
v_isShared_1371_ = v_isSharedCheck_1392_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_tail_1347_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1392_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1372_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1345_);
v___x_1373_ = lean_array_mk(v_xs_1345_);
v___x_1374_ = lean_array_pop(v___x_1373_);
v___x_1375_ = lean_array_to_list(v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1377_ = l_Lean_MessageData_joinSep(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 7);
lean_ctor_set(v___x_1370_, 1, v___x_1378_);
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1380_ = v___x_1370_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v___x_1381_ = l_List_getLast_x21___redArg(v___x_1372_, v_xs_1345_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_xs_1345_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1389_ = lean_ctor_get(v_xs_1345_, 1);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_xs_1345_, 0);
lean_dec(v_unused_1390_);
v___x_1383_ = v_xs_1345_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_xs_1345_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 7);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
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
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1399_ = l_Lean_MessageData_ofFormat(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1404_ = l_Lean_MessageData_ofFormat(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1405_){
_start:
{
if (lean_obj_tag(v_xs_1405_) == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1406_;
}
else
{
lean_object* v_tail_1407_; 
v_tail_1407_ = lean_ctor_get(v_xs_1405_, 1);
lean_inc(v_tail_1407_);
if (lean_obj_tag(v_tail_1407_) == 0)
{
lean_object* v_head_1408_; 
v_head_1408_ = lean_ctor_get(v_xs_1405_, 0);
lean_inc(v_head_1408_);
lean_dec_ref(v_xs_1405_);
return v_head_1408_;
}
else
{
lean_object* v_tail_1409_; 
v_tail_1409_ = lean_ctor_get(v_tail_1407_, 1);
if (lean_obj_tag(v_tail_1409_) == 0)
{
lean_object* v_head_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1427_; 
v_head_1410_ = lean_ctor_get(v_xs_1405_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_xs_1405_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_xs_1405_, 1);
lean_dec(v_unused_1428_);
v___x_1412_ = v_xs_1405_;
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_head_1410_);
lean_dec(v_xs_1405_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_head_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1425_; 
v_head_1414_ = lean_ctor_get(v_tail_1407_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_tail_1407_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v_tail_1407_, 1);
lean_dec(v_unused_1426_);
v___x_1416_ = v_tail_1407_;
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_head_1414_);
lean_dec(v_tail_1407_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1418_);
lean_ctor_set(v___x_1416_, 0, v_head_1410_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_head_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 7);
lean_ctor_set(v___x_1412_, 1, v_head_1414_);
lean_ctor_set(v___x_1412_, 0, v___x_1420_);
v___x_1422_ = v___x_1412_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_head_1414_);
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
}
else
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1452_; 
v_isSharedCheck_1452_ = !lean_is_exclusive(v_tail_1407_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1453_ = lean_ctor_get(v_tail_1407_, 1);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_tail_1407_, 0);
lean_dec(v_unused_1454_);
v___x_1430_ = v_tail_1407_;
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_tail_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1432_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1405_);
v___x_1433_ = lean_array_mk(v_xs_1405_);
v___x_1434_ = lean_array_pop(v___x_1433_);
v___x_1435_ = lean_array_to_list(v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1437_ = l_Lean_MessageData_joinSep(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 7);
lean_ctor_set(v___x_1430_, 1, v___x_1438_);
lean_ctor_set(v___x_1430_, 0, v___x_1437_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v___x_1441_ = l_List_getLast_x21___redArg(v___x_1432_, v_xs_1405_);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_xs_1405_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_xs_1405_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_xs_1405_, 0);
lean_dec(v_unused_1450_);
v___x_1443_ = v_xs_1405_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_xs_1405_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 7);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 0, v___x_1440_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
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
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_1461_ = l_Lean_MessageData_ofFormat(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_1463_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_note_1465_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_1472_ = l_Lean_MessageData_ofFormat(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_1474_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v_hint_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1482_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_1483_ = lean_box(0);
v___x_1484_ = l_List_mapTR_loop___redArg(v___x_1482_, v_es_1481_, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofList(v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_1490_ = l_Lean_instInhabitedPosition_default;
v___x_1491_ = lean_box(0);
v___x_1492_ = 0;
v___x_1493_ = 2;
v___x_1494_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1494_, 0, v___x_1489_);
lean_ctor_set(v___x_1494_, 1, v___x_1490_);
lean_ctor_set(v___x_1494_, 2, v___x_1491_);
lean_ctor_set(v___x_1494_, 3, v___x_1489_);
lean_ctor_set(v___x_1494_, 4, v_inst_1488_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*5, v___x_1492_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*5 + 1, v___x_1493_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*5 + 2, v___x_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_1500_, lean_object* v_inst_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v_fileName_1517_; lean_object* v_pos_1518_; lean_object* v_endPos_1519_; uint8_t v_keepFullRange_1520_; uint8_t v_severity_1521_; uint8_t v_isSilent_1522_; lean_object* v_caption_1523_; lean_object* v_data_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_fileName_1517_ = lean_ctor_get(v_x_1516_, 0);
lean_inc_ref(v_fileName_1517_);
v_pos_1518_ = lean_ctor_get(v_x_1516_, 1);
lean_inc_ref(v_pos_1518_);
v_endPos_1519_ = lean_ctor_get(v_x_1516_, 2);
lean_inc(v_endPos_1519_);
v_keepFullRange_1520_ = lean_ctor_get_uint8(v_x_1516_, sizeof(void*)*5);
v_severity_1521_ = lean_ctor_get_uint8(v_x_1516_, sizeof(void*)*5 + 1);
v_isSilent_1522_ = lean_ctor_get_uint8(v_x_1516_, sizeof(void*)*5 + 2);
v_caption_1523_ = lean_ctor_get(v_x_1516_, 3);
lean_inc_ref(v_caption_1523_);
v_data_1524_ = lean_ctor_get(v_x_1516_, 4);
lean_inc(v_data_1524_);
lean_dec_ref(v_x_1516_);
v___x_1525_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_1526_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_fileName_1517_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1532_ = l_Lean_instToJsonPosition_toJson(v_pos_1518_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1529_);
v___x_1535_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1536_ = l_Option_toJson___redArg(v___x_1525_, v_endPos_1519_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1529_);
v___x_1539_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1540_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1540_, 0, v_keepFullRange_1520_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1529_);
v___x_1543_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1544_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1521_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1529_);
v___x_1547_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1548_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1548_, 0, v_isSilent_1522_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1529_);
v___x_1551_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_caption_1523_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1529_);
v___x_1555_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1556_ = lean_apply_1(v_inst_1515_, v_data_1524_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1529_);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1529_);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1554_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1550_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1546_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1542_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1538_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1534_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1530_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_1568_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1569_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_1567_, v___x_1566_, v___x_1568_);
v___x_1570_ = l_Lean_Json_mkObj(v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_1571_, lean_object* v_inst_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_1572_, v_x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1576_, 0, lean_box(0));
lean_closure_set(v___x_1576_, 1, v_inst_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_1577_, lean_object* v_inst_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1579_, 0, lean_box(0));
lean_closure_set(v___x_1579_, 1, v_inst_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = 1;
v___x_1586_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_1587_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1586_, v___x_1585_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_1590_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = 1;
v___x_1595_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_1596_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_1598_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1599_ = lean_string_append(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1602_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_1603_ = lean_string_append(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = 1;
v___x_1610_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_1611_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_1613_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1614_ = lean_string_append(v___x_1613_, v___x_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1616_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_1617_ = lean_string_append(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = 1;
v___x_1621_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_1622_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1621_, v___x_1620_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_1624_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1625_ = lean_string_append(v___x_1624_, v___x_1623_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1627_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_1628_ = lean_string_append(v___x_1627_, v___x_1626_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 1;
v___x_1633_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_1634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_1636_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1637_ = lean_string_append(v___x_1636_, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1639_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_1640_ = lean_string_append(v___x_1639_, v___x_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = 1;
v___x_1644_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_1645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_1647_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1648_ = lean_string_append(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1650_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_1651_ = lean_string_append(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = 1;
v___x_1655_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_1656_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_1658_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1659_ = lean_string_append(v___x_1658_, v___x_1657_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1661_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_1662_ = lean_string_append(v___x_1661_, v___x_1660_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = 1;
v___x_1666_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_1667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_1669_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1670_ = lean_string_append(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1672_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_1673_ = lean_string_append(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = 1;
v___x_1677_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_1678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_1680_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1681_ = lean_string_append(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1683_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_1684_ = lean_string_append(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_1685_, lean_object* v_json_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_1688_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_1686_);
v___x_1689_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1687_, v___x_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1694_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_1695_ = lean_string_append(v___x_1694_, v_a_1690_);
lean_dec(v_a_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1695_);
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1700_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1689_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1689_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 0);
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1708_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1689_);
v___x_1709_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_1710_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_1711_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_1686_);
v___x_1712_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1709_, v___x_1711_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_1718_ = lean_string_append(v___x_1717_, v_a_1713_);
lean_dec(v_a_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1723_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1712_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1712_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 0);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_a_1731_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1712_);
v___x_1732_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_1686_);
v___x_1733_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1710_, v___x_1732_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_1739_ = lean_string_append(v___x_1738_, v_a_1734_);
lean_dec(v_a_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1739_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1744_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1733_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1733_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 0);
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_a_1752_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1733_);
v___x_1753_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_1754_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_1686_);
v___x_1755_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1753_, v___x_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_1761_ = lean_string_append(v___x_1760_, v_a_1756_);
lean_dec(v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1766_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1755_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1755_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 0);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_a_1774_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1755_);
v___x_1775_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_1776_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_1686_);
v___x_1777_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1775_, v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_1783_ = lean_string_append(v___x_1782_, v_a_1778_);
lean_dec(v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1788_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1777_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1777_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set_tag(v___x_1790_, 0);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_a_1796_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1777_);
v___x_1797_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_1686_);
v___x_1798_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1753_, v___x_1797_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_1804_ = lean_string_append(v___x_1803_, v_a_1799_);
lean_dec(v_a_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1809_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1798_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1798_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 0);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1817_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1798_);
v___x_1818_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_1686_);
v___x_1819_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v___x_1687_, v___x_1818_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1817_);
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1829_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1829_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1824_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_1825_ = lean_string_append(v___x_1824_, v_a_1820_);
lean_dec(v_a_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1817_);
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
lean_dec(v_json_1686_);
lean_dec_ref(v_inst_1685_);
v_a_1830_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1819_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1819_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 0);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_a_1838_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1819_);
v___x_1839_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1840_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1686_, v_inst_1685_, v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1838_);
lean_dec(v_a_1817_);
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_1846_ = lean_string_append(v___x_1845_, v_a_1841_);
lean_dec(v_a_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1838_);
lean_dec(v_a_1817_);
lean_dec(v_a_1796_);
lean_dec(v_a_1774_);
lean_dec(v_a_1752_);
lean_dec(v_a_1731_);
lean_dec(v_a_1708_);
v_a_1851_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1840_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1840_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 0);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1870_; 
v_a_1859_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1861_ = v___x_1840_;
v_isShared_1862_ = v_isSharedCheck_1870_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1840_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1870_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; uint8_t v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1868_; 
v___x_1863_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1863_, 0, v_a_1708_);
lean_ctor_set(v___x_1863_, 1, v_a_1731_);
lean_ctor_set(v___x_1863_, 2, v_a_1752_);
lean_ctor_set(v___x_1863_, 3, v_a_1838_);
lean_ctor_set(v___x_1863_, 4, v_a_1859_);
v___x_1864_ = lean_unbox(v_a_1774_);
lean_dec(v_a_1774_);
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*5, v___x_1864_);
v___x_1865_ = lean_unbox(v_a_1796_);
lean_dec(v_a_1796_);
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*5 + 1, v___x_1865_);
v___x_1866_ = lean_unbox(v_a_1817_);
lean_dec(v_a_1817_);
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*5 + 2, v___x_1866_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1868_ = v___x_1861_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_1871_, lean_object* v_inst_1872_, lean_object* v_json_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_1872_, v_json_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, v_inst_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_1877_, lean_object* v_inst_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1879_, 0, lean_box(0));
lean_closure_set(v___x_1879_, 1, v_inst_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_1880_){
_start:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_box(0);
return v___x_1881_;
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1883_; 
v_val_1882_ = lean_ctor_get(v_x_1880_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v_x_1880_);
v___x_1883_ = l_Lean_instToJsonPosition_toJson(v_val_1882_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
if (lean_obj_tag(v_a_1884_) == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_array_to_list(v_a_1885_);
return v___x_1886_;
}
else
{
lean_object* v_head_1887_; lean_object* v_tail_1888_; lean_object* v___x_1889_; 
v_head_1887_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_head_1887_);
v_tail_1888_ = lean_ctor_get(v_a_1884_, 1);
lean_inc(v_tail_1888_);
lean_dec_ref(v_a_1884_);
v___x_1889_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1885_, v_head_1887_);
v_a_1884_ = v_tail_1888_;
v_a_1885_ = v___x_1889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_1892_){
_start:
{
lean_object* v_toBaseMessage_1893_; lean_object* v_kind_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1959_; 
v_toBaseMessage_1893_ = lean_ctor_get(v_x_1892_, 0);
v_kind_1894_ = lean_ctor_get(v_x_1892_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_x_1892_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1896_ = v_x_1892_;
v_isShared_1897_ = v_isSharedCheck_1959_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_kind_1894_);
lean_inc(v_toBaseMessage_1893_);
lean_dec(v_x_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1959_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_fileName_1898_; lean_object* v_pos_1899_; lean_object* v_endPos_1900_; uint8_t v_keepFullRange_1901_; uint8_t v_severity_1902_; uint8_t v_isSilent_1903_; lean_object* v_caption_1904_; lean_object* v_data_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v_fileName_1898_ = lean_ctor_get(v_toBaseMessage_1893_, 0);
lean_inc_ref(v_fileName_1898_);
v_pos_1899_ = lean_ctor_get(v_toBaseMessage_1893_, 1);
lean_inc_ref(v_pos_1899_);
v_endPos_1900_ = lean_ctor_get(v_toBaseMessage_1893_, 2);
lean_inc(v_endPos_1900_);
v_keepFullRange_1901_ = lean_ctor_get_uint8(v_toBaseMessage_1893_, sizeof(void*)*5);
v_severity_1902_ = lean_ctor_get_uint8(v_toBaseMessage_1893_, sizeof(void*)*5 + 1);
v_isSilent_1903_ = lean_ctor_get_uint8(v_toBaseMessage_1893_, sizeof(void*)*5 + 2);
v_caption_1904_ = lean_ctor_get(v_toBaseMessage_1893_, 3);
lean_inc_ref(v_caption_1904_);
v_data_1905_ = lean_ctor_get(v_toBaseMessage_1893_, 4);
lean_inc(v_data_1905_);
lean_dec_ref(v_toBaseMessage_1893_);
v___x_1906_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_fileName_1898_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1907_);
lean_ctor_set(v___x_1896_, 0, v___x_1906_);
v___x_1909_ = v___x_1896_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1913_ = l_Lean_instToJsonPosition_toJson(v_pos_1899_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1910_);
v___x_1916_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1917_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_1900_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1910_);
v___x_1920_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1921_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1921_, 0, v_keepFullRange_1901_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1910_);
v___x_1924_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1925_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1902_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1910_);
v___x_1928_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1929_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1929_, 0, v_isSilent_1903_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1910_);
v___x_1932_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_caption_1904_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1910_);
v___x_1936_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_data_1905_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1910_);
v___x_1940_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_1941_ = 1;
v___x_1942_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1894_, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1940_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1910_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1910_);
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1939_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1935_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1931_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1927_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1923_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1919_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1915_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1911_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1956_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_1954_, v___x_1955_);
v___x_1957_ = l_Lean_Json_mkObj(v___x_1956_);
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_1962_, lean_object* v_k_1963_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = l_Lean_Json_getObjValD(v_j_1962_, v_k_1963_);
v___x_1965_ = l_Lean_Json_getStr_x3f(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_1966_, lean_object* v_k_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_1966_, v_k_1967_);
lean_dec_ref(v_k_1967_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = l_Lean_Json_getObjValD(v_j_1969_, v_k_1970_);
v___x_1972_ = l_Lean_instFromJsonPosition_fromJson(v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_1973_, lean_object* v_k_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_1973_, v_k_1974_);
lean_dec_ref(v_k_1974_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_1976_, lean_object* v_k_1977_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = l_Lean_Json_getObjValD(v_j_1976_, v_k_1977_);
v___x_1979_ = l_Lean_Json_getBool_x3f(v___x_1978_);
lean_dec(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_1980_, lean_object* v_k_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_1980_, v_k_1981_);
lean_dec_ref(v_k_1981_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_1983_, lean_object* v_k_1984_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = l_Lean_Json_getObjValD(v_j_1983_, v_k_1984_);
v___x_1986_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_1987_, lean_object* v_k_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_1987_, v_k_1988_);
lean_dec_ref(v_k_1988_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_1990_, lean_object* v_k_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = l_Lean_Json_getObjValD(v_j_1990_, v_k_1991_);
v___x_1993_ = l_Lean_Name_fromJson_x3f(v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_1994_, lean_object* v_k_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_1994_, v_k_1995_);
lean_dec_ref(v_k_1995_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_instFromJsonPosition_fromJson(v_x_1999_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v_a_2010_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2012_ = v___x_2001_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2001_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_a_2010_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2019_, lean_object* v_k_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = l_Lean_Json_getObjValD(v_j_2019_, v_k_2020_);
v___x_2022_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2023_, lean_object* v_k_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2023_, v_k_2024_);
lean_dec_ref(v_k_2024_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = 1;
v___x_2031_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2032_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2031_, v___x_2030_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2034_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2035_ = lean_string_append(v___x_2034_, v___x_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2037_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2038_ = lean_string_append(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2040_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2041_ = lean_string_append(v___x_2040_, v___x_2039_);
return v___x_2041_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2043_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2044_ = lean_string_append(v___x_2043_, v___x_2042_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2046_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2047_ = lean_string_append(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2049_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2050_ = lean_string_append(v___x_2049_, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2052_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2053_ = lean_string_append(v___x_2052_, v___x_2051_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2055_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2056_ = lean_string_append(v___x_2055_, v___x_2054_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2058_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2059_ = lean_string_append(v___x_2058_, v___x_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2061_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2062_ = lean_string_append(v___x_2061_, v___x_2060_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2064_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2065_ = lean_string_append(v___x_2064_, v___x_2063_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2067_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2068_ = lean_string_append(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2070_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2071_ = lean_string_append(v___x_2070_, v___x_2069_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2073_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2074_ = lean_string_append(v___x_2073_, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2076_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2077_ = lean_string_append(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2079_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2080_ = lean_string_append(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2082_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2083_ = lean_string_append(v___x_2082_, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = 1;
v___x_2087_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2088_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2087_, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2090_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2091_ = lean_string_append(v___x_2090_, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2093_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2094_ = lean_string_append(v___x_2093_, v___x_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2095_){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2095_);
v___x_2097_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2095_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_json_2095_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2103_ = lean_string_append(v___x_2102_, v_a_2098_);
lean_dec(v_a_2098_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2103_);
v___x_2105_ = v___x_2100_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_json_2095_);
v_a_2108_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2097_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2097_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 0);
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2116_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2097_);
v___x_2117_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2095_);
v___x_2118_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2095_, v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2124_ = lean_string_append(v___x_2123_, v_a_2119_);
lean_dec(v_a_2119_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2129_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2118_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2118_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2118_);
v___x_2138_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2095_);
v___x_2139_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2095_, v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2149_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2145_ = lean_string_append(v___x_2144_, v_a_2140_);
lean_dec(v_a_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2150_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2139_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2139_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 0);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2158_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2139_);
v___x_2159_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2095_);
v___x_2160_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2095_, v___x_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2166_ = lean_string_append(v___x_2165_, v_a_2161_);
lean_dec(v_a_2161_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2171_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2160_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2160_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 0);
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2179_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2160_);
v___x_2180_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2095_);
v___x_2181_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2095_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2191_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2191_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2187_ = lean_string_append(v___x_2186_, v_a_2182_);
lean_dec(v_a_2182_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2187_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2192_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2181_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2181_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 0);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_a_2200_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2181_);
v___x_2201_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2095_);
v___x_2202_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2095_, v___x_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2208_ = lean_string_append(v___x_2207_, v_a_2203_);
lean_dec(v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2213_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2202_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2202_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 0);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2202_);
v___x_2222_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2095_);
v___x_2223_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2095_, v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2233_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2233_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2229_ = lean_string_append(v___x_2228_, v_a_2224_);
lean_dec(v_a_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2229_);
v___x_2231_ = v___x_2226_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2234_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2223_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2223_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 0);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_a_2242_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2223_);
v___x_2243_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2095_);
v___x_2244_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2095_, v___x_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_a_2242_);
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2249_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2250_ = lean_string_append(v___x_2249_, v_a_2245_);
lean_dec(v_a_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2250_);
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2242_);
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
lean_dec(v_json_2095_);
v_a_2255_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2244_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2244_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set_tag(v___x_2257_, 0);
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2263_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2244_);
v___x_2264_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2265_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2095_, v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2263_);
lean_dec(v_a_2242_);
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2270_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2271_ = lean_string_append(v___x_2270_, v_a_2266_);
lean_dec(v_a_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
else
{
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_a_2263_);
lean_dec(v_a_2242_);
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2158_);
lean_dec(v_a_2137_);
lean_dec(v_a_2116_);
v_a_2276_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2265_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2265_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 0);
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2296_; 
v_a_2284_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2286_ = v___x_2265_;
v_isShared_2287_ = v_isSharedCheck_2296_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2265_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2296_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2288_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2288_, 0, v_a_2116_);
lean_ctor_set(v___x_2288_, 1, v_a_2137_);
lean_ctor_set(v___x_2288_, 2, v_a_2158_);
lean_ctor_set(v___x_2288_, 3, v_a_2242_);
lean_ctor_set(v___x_2288_, 4, v_a_2263_);
v___x_2289_ = lean_unbox(v_a_2179_);
lean_dec(v_a_2179_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*5, v___x_2289_);
v___x_2290_ = lean_unbox(v_a_2200_);
lean_dec(v_a_2200_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*5 + 1, v___x_2290_);
v___x_2291_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*5 + 2, v___x_2291_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2288_);
lean_ctor_set(v___x_2292_, 1, v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2292_);
v___x_2294_ = v___x_2286_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2303_ = l_Lean_Name_str___override(v_errorName_2301_, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2304_, lean_object* v_name_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = l_Lean_kindOfErrorName(v_name_2305_);
v___x_2307_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_msg_2304_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2309_){
_start:
{
switch(lean_obj_tag(v_a_2309_))
{
case 0:
{
return v_a_2309_;
}
case 1:
{
lean_object* v_pre_2310_; lean_object* v_str_2311_; lean_object* v_p_x27_2312_; uint8_t v___y_2314_; uint8_t v___x_2317_; 
v_pre_2310_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_pre_2310_);
v_str_2311_ = lean_ctor_get(v_a_2309_, 1);
lean_inc_ref(v_str_2311_);
lean_dec_ref(v_a_2309_);
v_p_x27_2312_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2310_);
v___x_2317_ = l_Lean_Name_isAnonymous(v_p_x27_2312_);
if (v___x_2317_ == 0)
{
v___y_2314_ = v___x_2317_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2319_ = lean_string_dec_eq(v_str_2311_, v___x_2318_);
v___y_2314_ = v___x_2319_;
goto v___jp_2313_;
}
v___jp_2313_:
{
if (v___y_2314_ == 0)
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Name_str___override(v_p_x27_2312_, v_str_2311_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; 
lean_dec(v_p_x27_2312_);
lean_dec_ref(v_str_2311_);
v___x_2316_ = lean_box(0);
return v___x_2316_;
}
}
}
default: 
{
lean_object* v_pre_2320_; lean_object* v_i_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_pre_2320_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_pre_2320_);
v_i_2321_ = lean_ctor_get(v_a_2309_, 1);
lean_inc(v_i_2321_);
lean_dec_ref(v_a_2309_);
v___x_2322_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2320_);
v___x_2323_ = l_Lean_Name_num___override(v___x_2322_, v_i_2321_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2324_){
_start:
{
switch(lean_obj_tag(v_x_2324_))
{
case 3:
{
lean_object* v_a_2325_; lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_a_2325_ = lean_ctor_get(v_x_2324_, 0);
v_a_2326_ = lean_ctor_get(v_x_2324_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_x_2324_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_inc(v_a_2325_);
lean_dec(v_x_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = l_Lean_MessageData_stripNestedTags(v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
case 4:
{
lean_object* v_a_2335_; lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2344_; 
v_a_2335_ = lean_ctor_get(v_x_2324_, 0);
v_a_2336_ = lean_ctor_get(v_x_2324_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2338_ = v_x_2324_;
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_inc(v_a_2335_);
lean_dec(v_x_2324_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = l_Lean_MessageData_stripNestedTags(v_a_2336_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v___x_2340_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
case 8:
{
lean_object* v_a_2345_; lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2354_; 
v_a_2345_ = lean_ctor_get(v_x_2324_, 0);
v_a_2346_ = lean_ctor_get(v_x_2324_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2348_ = v_x_2324_;
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_inc(v_a_2345_);
lean_dec(v_x_2324_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2345_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_a_2346_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
default: 
{
return v_x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2355_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 1)
{
lean_object* v_pre_2356_; lean_object* v_str_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_pre_2356_ = lean_ctor_get(v_x_2355_, 0);
v_str_2357_ = lean_ctor_get(v_x_2355_, 1);
v___x_2358_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2359_ = lean_string_dec_eq(v_str_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_box(0);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; 
lean_inc(v_pre_2356_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_pre_2356_);
return v___x_2361_;
}
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_box(0);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_errorNameOfKind_x3f(v_x_2363_);
lean_dec(v_x_2363_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_Lean_MessageData_kind(v_msg_2365_);
v___x_2367_ = l_Lean_errorNameOfKind_x3f(v___x_2366_);
lean_dec(v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_MessageData_errorName_x3f(v_msg_2368_);
lean_dec_ref(v_msg_2368_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2370_){
_start:
{
lean_object* v_data_2371_; lean_object* v___x_2372_; 
v_data_2371_ = lean_ctor_get(v_msg_2370_, 4);
v___x_2372_ = l_Lean_MessageData_errorName_x3f(v_data_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Message_errorName_x3f(v_msg_2373_);
lean_dec_ref(v_msg_2373_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2375_){
_start:
{
lean_object* v_toBaseMessage_2376_; lean_object* v_fileName_2377_; lean_object* v_pos_2378_; lean_object* v_endPos_2379_; uint8_t v_keepFullRange_2380_; uint8_t v_severity_2381_; uint8_t v_isSilent_2382_; lean_object* v_caption_2383_; lean_object* v_data_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2393_; 
v_toBaseMessage_2376_ = lean_ctor_get(v_msg_2375_, 0);
lean_inc_ref(v_toBaseMessage_2376_);
lean_dec_ref(v_msg_2375_);
v_fileName_2377_ = lean_ctor_get(v_toBaseMessage_2376_, 0);
v_pos_2378_ = lean_ctor_get(v_toBaseMessage_2376_, 1);
v_endPos_2379_ = lean_ctor_get(v_toBaseMessage_2376_, 2);
v_keepFullRange_2380_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5);
v_severity_2381_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5 + 1);
v_isSilent_2382_ = lean_ctor_get_uint8(v_toBaseMessage_2376_, sizeof(void*)*5 + 2);
v_caption_2383_ = lean_ctor_get(v_toBaseMessage_2376_, 3);
v_data_2384_ = lean_ctor_get(v_toBaseMessage_2376_, 4);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_toBaseMessage_2376_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2386_ = v_toBaseMessage_2376_;
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_data_2384_);
lean_inc(v_caption_2383_);
lean_inc(v_endPos_2379_);
lean_inc(v_pos_2378_);
lean_inc(v_fileName_2377_);
lean_dec(v_toBaseMessage_2376_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_data_2384_);
v___x_2389_ = l_Lean_MessageData_ofFormat(v___x_2388_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 4, v___x_2389_);
v___x_2391_ = v___x_2386_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_fileName_2377_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_pos_2378_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_endPos_2379_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_caption_2383_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v___x_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*5, v_keepFullRange_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*5 + 1, v_severity_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*5 + 2, v_isSilent_2382_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2399_, uint8_t v_includeEndPos_2400_){
_start:
{
lean_object* v___y_2402_; uint8_t v___y_2406_; lean_object* v___y_2407_; uint32_t v___y_2408_; lean_object* v_str_2412_; lean_object* v_toBaseMessage_2424_; lean_object* v_kind_2425_; lean_object* v_fileName_2426_; lean_object* v_pos_2427_; lean_object* v_endPos_2428_; uint8_t v_severity_2429_; lean_object* v_caption_2430_; lean_object* v_data_2431_; lean_object* v___y_2433_; lean_object* v_str_2434_; lean_object* v___y_2442_; 
v_toBaseMessage_2424_ = lean_ctor_get(v_msg_2399_, 0);
lean_inc_ref(v_toBaseMessage_2424_);
v_kind_2425_ = lean_ctor_get(v_msg_2399_, 1);
lean_inc(v_kind_2425_);
lean_dec_ref(v_msg_2399_);
v_fileName_2426_ = lean_ctor_get(v_toBaseMessage_2424_, 0);
lean_inc_ref(v_fileName_2426_);
v_pos_2427_ = lean_ctor_get(v_toBaseMessage_2424_, 1);
lean_inc_ref(v_pos_2427_);
v_endPos_2428_ = lean_ctor_get(v_toBaseMessage_2424_, 2);
lean_inc(v_endPos_2428_);
v_severity_2429_ = lean_ctor_get_uint8(v_toBaseMessage_2424_, sizeof(void*)*5 + 1);
v_caption_2430_ = lean_ctor_get(v_toBaseMessage_2424_, 3);
lean_inc_ref(v_caption_2430_);
v_data_2431_ = lean_ctor_get(v_toBaseMessage_2424_, 4);
lean_inc(v_data_2431_);
lean_dec_ref(v_toBaseMessage_2424_);
if (v_includeEndPos_2400_ == 0)
{
lean_object* v___x_2448_; 
lean_dec(v_endPos_2428_);
v___x_2448_ = lean_box(0);
v___y_2442_ = v___x_2448_;
goto v___jp_2441_;
}
else
{
v___y_2442_ = v_endPos_2428_;
goto v___jp_2441_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v_str_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2404_ = lean_string_append(v___y_2402_, v___x_2403_);
return v_str_2404_;
}
v___jp_2405_:
{
uint32_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = 10;
v___x_2410_ = lean_uint32_dec_eq(v___y_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
v___y_2402_ = v___y_2407_;
goto v___jp_2401_;
}
else
{
if (v___y_2406_ == 0)
{
return v___y_2407_;
}
else
{
v___y_2402_ = v___y_2407_;
goto v___jp_2401_;
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = lean_string_utf8_byte_size(v_str_2412_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_nat_dec_eq(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_inc_ref(v_str_2412_);
v___x_2416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2416_, 0, v_str_2412_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
lean_ctor_set(v___x_2416_, 2, v___x_2413_);
v___x_2417_ = l_String_Slice_Pos_prev_x3f(v___x_2416_, v___x_2413_);
if (lean_obj_tag(v___x_2417_) == 0)
{
uint32_t v___x_2418_; 
lean_dec_ref(v___x_2416_);
v___x_2418_ = 65;
v___y_2406_ = v___x_2415_;
v___y_2407_ = v_str_2412_;
v___y_2408_ = v___x_2418_;
goto v___jp_2405_;
}
else
{
lean_object* v_val_2419_; lean_object* v___x_2420_; 
v_val_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_val_2419_);
lean_dec_ref(v___x_2417_);
v___x_2420_ = l_String_Slice_Pos_get_x3f(v___x_2416_, v_val_2419_);
lean_dec(v_val_2419_);
lean_dec_ref(v___x_2416_);
if (lean_obj_tag(v___x_2420_) == 0)
{
uint32_t v___x_2421_; 
v___x_2421_ = 65;
v___y_2406_ = v___x_2415_;
v___y_2407_ = v_str_2412_;
v___y_2408_ = v___x_2421_;
goto v___jp_2405_;
}
else
{
lean_object* v_val_2422_; uint32_t v___x_2423_; 
v_val_2422_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_val_2422_);
lean_dec_ref(v___x_2420_);
v___x_2423_ = lean_unbox_uint32(v_val_2422_);
lean_dec(v_val_2422_);
v___y_2406_ = v___x_2415_;
v___y_2407_ = v_str_2412_;
v___y_2408_ = v___x_2423_;
goto v___jp_2405_;
}
}
}
else
{
v___y_2402_ = v_str_2412_;
goto v___jp_2401_;
}
}
v___jp_2432_:
{
switch(v_severity_2429_)
{
case 0:
{
lean_dec(v___y_2433_);
lean_dec_ref(v_pos_2427_);
lean_dec_ref(v_fileName_2426_);
lean_dec(v_kind_2425_);
v_str_2412_ = v_str_2434_;
goto v___jp_2411_;
}
case 1:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v_str_2437_; 
v___x_2435_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2436_ = l_Lean_errorNameOfKind_x3f(v_kind_2425_);
lean_dec(v_kind_2425_);
v_str_2437_ = l_Lean_mkErrorStringWithPos(v_fileName_2426_, v_pos_2427_, v_str_2434_, v___y_2433_, v___x_2435_, v___x_2436_);
lean_dec_ref(v_str_2434_);
v_str_2412_ = v_str_2437_;
goto v___jp_2411_;
}
default: 
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_str_2440_; 
v___x_2438_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2439_ = l_Lean_errorNameOfKind_x3f(v_kind_2425_);
lean_dec(v_kind_2425_);
v_str_2440_ = l_Lean_mkErrorStringWithPos(v_fileName_2426_, v_pos_2427_, v_str_2434_, v___y_2433_, v___x_2438_, v___x_2439_);
lean_dec_ref(v_str_2434_);
v_str_2412_ = v_str_2440_;
goto v___jp_2411_;
}
}
}
v___jp_2441_:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2444_ = lean_string_dec_eq(v_caption_2430_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_str_2447_; 
v___x_2445_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2446_ = lean_string_append(v_caption_2430_, v___x_2445_);
v_str_2447_ = lean_string_append(v___x_2446_, v_data_2431_);
lean_dec(v_data_2431_);
v___y_2433_ = v___y_2442_;
v_str_2434_ = v_str_2447_;
goto v___jp_2432_;
}
else
{
lean_dec_ref(v_caption_2430_);
v___y_2433_ = v___y_2442_;
v_str_2434_ = v_data_2431_;
goto v___jp_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2449_, lean_object* v_includeEndPos_2450_){
_start:
{
uint8_t v_includeEndPos_boxed_2451_; lean_object* v_res_2452_; 
v_includeEndPos_boxed_2451_ = lean_unbox(v_includeEndPos_2450_);
v_res_2452_ = l_Lean_SerialMessage_toString(v_msg_2449_, v_includeEndPos_boxed_2451_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2453_){
_start:
{
uint8_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = 0;
v___x_2455_ = l_Lean_SerialMessage_toString(v_msg_2453_, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2458_){
_start:
{
lean_object* v_data_2459_; lean_object* v___x_2460_; 
v_data_2459_ = lean_ctor_get(v_msg_2458_, 4);
v___x_2460_ = l_Lean_MessageData_kind(v_data_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_Message_kind(v_msg_2461_);
lean_dec_ref(v_msg_2461_);
return v_res_2462_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2463_){
_start:
{
lean_object* v_data_2464_; uint8_t v___x_2465_; 
v_data_2464_ = lean_ctor_get(v_msg_2463_, 4);
v___x_2465_ = l_Lean_MessageData_isTrace(v_data_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2466_){
_start:
{
uint8_t v_res_2467_; lean_object* v_r_2468_; 
v_res_2467_ = l_Lean_Message_isTrace(v_msg_2466_);
lean_dec_ref(v_msg_2466_);
v_r_2468_ = lean_box(v_res_2467_);
return v_r_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2469_){
_start:
{
lean_object* v_fileName_2471_; lean_object* v_pos_2472_; lean_object* v_endPos_2473_; uint8_t v_keepFullRange_2474_; uint8_t v_severity_2475_; uint8_t v_isSilent_2476_; lean_object* v_caption_2477_; lean_object* v_data_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2488_; 
v_fileName_2471_ = lean_ctor_get(v_msg_2469_, 0);
v_pos_2472_ = lean_ctor_get(v_msg_2469_, 1);
v_endPos_2473_ = lean_ctor_get(v_msg_2469_, 2);
v_keepFullRange_2474_ = lean_ctor_get_uint8(v_msg_2469_, sizeof(void*)*5);
v_severity_2475_ = lean_ctor_get_uint8(v_msg_2469_, sizeof(void*)*5 + 1);
v_isSilent_2476_ = lean_ctor_get_uint8(v_msg_2469_, sizeof(void*)*5 + 2);
v_caption_2477_ = lean_ctor_get(v_msg_2469_, 3);
v_data_2478_ = lean_ctor_get(v_msg_2469_, 4);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_msg_2469_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2480_ = v_msg_2469_;
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_data_2478_);
lean_inc(v_caption_2477_);
lean_inc(v_endPos_2473_);
lean_inc(v_pos_2472_);
lean_inc(v_fileName_2471_);
lean_dec(v_msg_2469_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
lean_inc(v_data_2478_);
v___x_2482_ = l_Lean_MessageData_toString(v_data_2478_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 4, v___x_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_fileName_2471_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_pos_2472_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_endPos_2473_);
lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_caption_2477_);
lean_ctor_set(v_reuseFailAlloc_2487_, 4, v___x_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*5, v_keepFullRange_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*5 + 1, v_severity_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*5 + 2, v_isSilent_2476_);
v___x_2484_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = l_Lean_MessageData_kind(v_data_2478_);
lean_dec(v_data_2478_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Message_serialize(v_msg_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2492_, uint8_t v_includeEndPos_2493_){
_start:
{
lean_object* v_fileName_2495_; lean_object* v_pos_2496_; lean_object* v_endPos_2497_; uint8_t v_severity_2498_; lean_object* v_caption_2499_; lean_object* v_data_2500_; lean_object* v___x_2501_; lean_object* v___y_2503_; lean_object* v___y_2507_; uint8_t v___y_2508_; uint32_t v___y_2509_; lean_object* v_str_2513_; lean_object* v___x_2525_; lean_object* v___y_2527_; lean_object* v_str_2528_; lean_object* v___y_2536_; 
v_fileName_2495_ = lean_ctor_get(v_msg_2492_, 0);
lean_inc_ref(v_fileName_2495_);
v_pos_2496_ = lean_ctor_get(v_msg_2492_, 1);
lean_inc_ref(v_pos_2496_);
v_endPos_2497_ = lean_ctor_get(v_msg_2492_, 2);
lean_inc(v_endPos_2497_);
v_severity_2498_ = lean_ctor_get_uint8(v_msg_2492_, sizeof(void*)*5 + 1);
v_caption_2499_ = lean_ctor_get(v_msg_2492_, 3);
lean_inc_ref(v_caption_2499_);
v_data_2500_ = lean_ctor_get(v_msg_2492_, 4);
lean_inc_n(v_data_2500_, 2);
lean_dec_ref(v_msg_2492_);
v___x_2501_ = l_Lean_MessageData_toString(v_data_2500_);
v___x_2525_ = l_Lean_MessageData_kind(v_data_2500_);
lean_dec(v_data_2500_);
if (v_includeEndPos_2493_ == 0)
{
lean_object* v___x_2542_; 
lean_dec(v_endPos_2497_);
v___x_2542_ = lean_box(0);
v___y_2536_ = v___x_2542_;
goto v___jp_2535_;
}
else
{
v___y_2536_ = v_endPos_2497_;
goto v___jp_2535_;
}
v___jp_2502_:
{
lean_object* v___x_2504_; lean_object* v_str_2505_; 
v___x_2504_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2505_ = lean_string_append(v___y_2503_, v___x_2504_);
return v_str_2505_;
}
v___jp_2506_:
{
uint32_t v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = 10;
v___x_2511_ = lean_uint32_dec_eq(v___y_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
v___y_2503_ = v___y_2507_;
goto v___jp_2502_;
}
else
{
if (v___y_2508_ == 0)
{
return v___y_2507_;
}
else
{
v___y_2503_ = v___y_2507_;
goto v___jp_2502_;
}
}
}
v___jp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2514_ = lean_string_utf8_byte_size(v_str_2513_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_nat_dec_eq(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_inc_ref(v_str_2513_);
v___x_2517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2517_, 0, v_str_2513_);
lean_ctor_set(v___x_2517_, 1, v___x_2515_);
lean_ctor_set(v___x_2517_, 2, v___x_2514_);
v___x_2518_ = l_String_Slice_Pos_prev_x3f(v___x_2517_, v___x_2514_);
if (lean_obj_tag(v___x_2518_) == 0)
{
uint32_t v___x_2519_; 
lean_dec_ref(v___x_2517_);
v___x_2519_ = 65;
v___y_2507_ = v_str_2513_;
v___y_2508_ = v___x_2516_;
v___y_2509_ = v___x_2519_;
goto v___jp_2506_;
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2521_; 
v_val_2520_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_val_2520_);
lean_dec_ref(v___x_2518_);
v___x_2521_ = l_String_Slice_Pos_get_x3f(v___x_2517_, v_val_2520_);
lean_dec(v_val_2520_);
lean_dec_ref(v___x_2517_);
if (lean_obj_tag(v___x_2521_) == 0)
{
uint32_t v___x_2522_; 
v___x_2522_ = 65;
v___y_2507_ = v_str_2513_;
v___y_2508_ = v___x_2516_;
v___y_2509_ = v___x_2522_;
goto v___jp_2506_;
}
else
{
lean_object* v_val_2523_; uint32_t v___x_2524_; 
v_val_2523_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2523_);
lean_dec_ref(v___x_2521_);
v___x_2524_ = lean_unbox_uint32(v_val_2523_);
lean_dec(v_val_2523_);
v___y_2507_ = v_str_2513_;
v___y_2508_ = v___x_2516_;
v___y_2509_ = v___x_2524_;
goto v___jp_2506_;
}
}
}
else
{
v___y_2503_ = v_str_2513_;
goto v___jp_2502_;
}
}
v___jp_2526_:
{
switch(v_severity_2498_)
{
case 0:
{
lean_dec(v___y_2527_);
lean_dec(v___x_2525_);
lean_dec_ref(v_pos_2496_);
lean_dec_ref(v_fileName_2495_);
v_str_2513_ = v_str_2528_;
goto v___jp_2512_;
}
case 1:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_str_2531_; 
v___x_2529_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2530_ = l_Lean_errorNameOfKind_x3f(v___x_2525_);
lean_dec(v___x_2525_);
v_str_2531_ = l_Lean_mkErrorStringWithPos(v_fileName_2495_, v_pos_2496_, v_str_2528_, v___y_2527_, v___x_2529_, v___x_2530_);
lean_dec_ref(v_str_2528_);
v_str_2513_ = v_str_2531_;
goto v___jp_2512_;
}
default: 
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_str_2534_; 
v___x_2532_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2533_ = l_Lean_errorNameOfKind_x3f(v___x_2525_);
lean_dec(v___x_2525_);
v_str_2534_ = l_Lean_mkErrorStringWithPos(v_fileName_2495_, v_pos_2496_, v_str_2528_, v___y_2527_, v___x_2532_, v___x_2533_);
lean_dec_ref(v_str_2528_);
v_str_2513_ = v_str_2534_;
goto v___jp_2512_;
}
}
}
v___jp_2535_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2538_ = lean_string_dec_eq(v_caption_2499_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_str_2541_; 
v___x_2539_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2540_ = lean_string_append(v_caption_2499_, v___x_2539_);
v_str_2541_ = lean_string_append(v___x_2540_, v___x_2501_);
lean_dec_ref(v___x_2501_);
v___y_2527_ = v___y_2536_;
v_str_2528_ = v_str_2541_;
goto v___jp_2526_;
}
else
{
lean_dec_ref(v_caption_2499_);
v___y_2527_ = v___y_2536_;
v_str_2528_ = v___x_2501_;
goto v___jp_2526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2543_, lean_object* v_includeEndPos_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_includeEndPos_boxed_2546_; lean_object* v_res_2547_; 
v_includeEndPos_boxed_2546_ = lean_unbox(v_includeEndPos_2544_);
v_res_2547_ = l_Lean_Message_toString(v_msg_2543_, v_includeEndPos_boxed_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2548_){
_start:
{
lean_object* v_fileName_2550_; lean_object* v_pos_2551_; lean_object* v_endPos_2552_; uint8_t v_keepFullRange_2553_; uint8_t v_severity_2554_; uint8_t v_isSilent_2555_; lean_object* v_caption_2556_; lean_object* v_data_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_fileName_2550_ = lean_ctor_get(v_msg_2548_, 0);
lean_inc_ref(v_fileName_2550_);
v_pos_2551_ = lean_ctor_get(v_msg_2548_, 1);
lean_inc_ref(v_pos_2551_);
v_endPos_2552_ = lean_ctor_get(v_msg_2548_, 2);
lean_inc(v_endPos_2552_);
v_keepFullRange_2553_ = lean_ctor_get_uint8(v_msg_2548_, sizeof(void*)*5);
v_severity_2554_ = lean_ctor_get_uint8(v_msg_2548_, sizeof(void*)*5 + 1);
v_isSilent_2555_ = lean_ctor_get_uint8(v_msg_2548_, sizeof(void*)*5 + 2);
v_caption_2556_ = lean_ctor_get(v_msg_2548_, 3);
lean_inc_ref(v_caption_2556_);
v_data_2557_ = lean_ctor_get(v_msg_2548_, 4);
lean_inc_n(v_data_2557_, 2);
lean_dec_ref(v_msg_2548_);
v___x_2558_ = l_Lean_MessageData_toString(v_data_2557_);
v___x_2559_ = l_Lean_MessageData_kind(v_data_2557_);
lean_dec(v_data_2557_);
v___x_2560_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_fileName_2550_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2566_ = l_Lean_instToJsonPosition_toJson(v_pos_2551_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2563_);
v___x_2569_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2570_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2552_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2563_);
v___x_2573_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2574_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2574_, 0, v_keepFullRange_2553_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___x_2563_);
v___x_2577_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2578_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2554_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2563_);
v___x_2581_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2582_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2582_, 0, v_isSilent_2555_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2563_);
v___x_2585_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_caption_2556_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2563_);
v___x_2589_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2558_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2563_);
v___x_2593_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2594_ = 1;
v___x_2595_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2559_, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2593_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2563_);
v___x_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2563_);
v___x_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2592_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2588_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2584_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2580_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2576_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2572_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2568_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2564_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2609_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2607_, v___x_2608_);
v___x_2610_ = l_Lean_Json_mkObj(v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Message_toJson(v_msg_2611_);
return v_res_2613_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_unsigned_to_nat(32u);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2617_ = ((size_t)5ULL);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_unsigned_to_nat(32u);
v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2619_);
v___x_2621_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_2622_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2620_);
lean_ctor_set(v___x_2622_, 2, v___x_2618_);
lean_ctor_set(v___x_2622_, 3, v___x_2618_);
lean_ctor_set_usize(v___x_2622_, 4, v___x_2617_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = l_Lean_NameSet_empty;
v___x_2624_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_2625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
lean_ctor_set(v___x_2625_, 2, v___x_2623_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_instInhabitedMessageLog_default;
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_unsigned_to_nat(32u);
v___x_2629_ = lean_mk_empty_array_with_capacity(v___x_2628_);
lean_dec_ref(v___x_2629_);
v___x_2630_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_2631_){
_start:
{
lean_object* v_unreported_2632_; 
v_unreported_2632_ = lean_ctor_get(v_self_2631_, 1);
lean_inc_ref(v_unreported_2632_);
return v_unreported_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_MessageLog_msgs(v_self_2633_);
lean_dec_ref(v_self_2633_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_2635_){
_start:
{
lean_object* v_reported_2636_; lean_object* v_unreported_2637_; lean_object* v___x_2638_; 
v_reported_2636_ = lean_ctor_get(v_x_2635_, 0);
lean_inc_ref(v_reported_2636_);
v_unreported_2637_ = lean_ctor_get(v_x_2635_, 1);
lean_inc_ref(v_unreported_2637_);
lean_dec_ref(v_x_2635_);
v___x_2638_ = l_Lean_PersistentArray_append___redArg(v_reported_2636_, v_unreported_2637_);
lean_dec_ref(v_unreported_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_2639_){
_start:
{
lean_object* v_unreported_2640_; uint8_t v___x_2641_; 
v_unreported_2640_ = lean_ctor_get(v_log_2639_, 1);
v___x_2641_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_2640_);
if (v___x_2641_ == 0)
{
uint8_t v___x_2642_; 
v___x_2642_ = 1;
return v___x_2642_;
}
else
{
uint8_t v___x_2643_; 
v___x_2643_ = 0;
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Lean_MessageLog_hasUnreported(v_log_2644_);
lean_dec_ref(v_log_2644_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_2647_, lean_object* v_log_2648_){
_start:
{
lean_object* v_reported_2649_; lean_object* v_unreported_2650_; lean_object* v_loggedKinds_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2659_; 
v_reported_2649_ = lean_ctor_get(v_log_2648_, 0);
v_unreported_2650_ = lean_ctor_get(v_log_2648_, 1);
v_loggedKinds_2651_ = lean_ctor_get(v_log_2648_, 2);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_log_2648_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2653_ = v_log_2648_;
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_loggedKinds_2651_);
lean_inc(v_unreported_2650_);
lean_inc(v_reported_2649_);
lean_dec(v_log_2648_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2655_ = l_Lean_PersistentArray_push___redArg(v_unreported_2650_, v_msg_2647_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2655_);
v___x_2657_ = v___x_2653_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_reported_2649_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_loggedKinds_2651_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_2662_, lean_object* v_x_2663_){
_start:
{
if (lean_obj_tag(v_x_2663_) == 0)
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_b_u2082_2662_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; 
v___x_2665_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2666_, v_x_2667_);
lean_dec(v_x_2667_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_2669_, lean_object* v_k_2670_, lean_object* v_t_2671_){
_start:
{
if (lean_obj_tag(v_t_2671_) == 0)
{
lean_object* v_size_2672_; lean_object* v_k_2673_; lean_object* v_v_2674_; lean_object* v_l_2675_; lean_object* v_r_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2691_; 
v_size_2672_ = lean_ctor_get(v_t_2671_, 0);
v_k_2673_ = lean_ctor_get(v_t_2671_, 1);
v_v_2674_ = lean_ctor_get(v_t_2671_, 2);
v_l_2675_ = lean_ctor_get(v_t_2671_, 3);
v_r_2676_ = lean_ctor_get(v_t_2671_, 4);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_t_2671_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2678_ = v_t_2671_;
v_isShared_2679_ = v_isSharedCheck_2691_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_r_2676_);
lean_inc(v_l_2675_);
lean_inc(v_v_2674_);
lean_inc(v_k_2673_);
lean_inc(v_size_2672_);
lean_dec(v_t_2671_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2691_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
uint8_t v___x_2680_; 
v___x_2680_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2670_, v_k_2673_);
switch(v___x_2680_)
{
case 0:
{
lean_object* v_impl_2681_; lean_object* v___x_2682_; 
lean_del_object(v___x_2678_);
lean_dec(v_size_2672_);
v_impl_2681_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2669_, v_k_2670_, v_l_2675_);
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2673_, v_v_2674_, v_impl_2681_, v_r_2676_);
return v___x_2682_;
}
case 1:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v_val_2685_; lean_object* v___x_2687_; 
lean_dec(v_k_2673_);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_v_2674_);
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2669_, v___x_2683_);
lean_dec_ref(v___x_2683_);
v_val_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_val_2685_);
lean_dec(v___x_2684_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 2, v_val_2685_);
lean_ctor_set(v___x_2678_, 1, v_k_2670_);
v___x_2687_ = v___x_2678_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_size_2672_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_k_2670_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_val_2685_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_l_2675_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_r_2676_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
default: 
{
lean_object* v_impl_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2678_);
lean_dec(v_size_2672_);
v_impl_2689_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2669_, v_k_2670_, v_r_2676_);
v___x_2690_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2673_, v_v_2674_, v_l_2675_, v_impl_2689_);
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v_val_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2669_, v___x_2692_);
v_val_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_val_2694_);
lean_dec(v___x_2693_);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v_k_2670_);
lean_ctor_set(v___x_2696_, 2, v_val_2694_);
lean_ctor_set(v___x_2696_, 3, v_t_2671_);
lean_ctor_set(v___x_2696_, 4, v_t_2671_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2698_) == 0)
{
lean_object* v_k_2699_; lean_object* v_v_2700_; lean_object* v_l_2701_; lean_object* v_r_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_k_2699_ = lean_ctor_get(v_x_2698_, 1);
lean_inc(v_k_2699_);
v_v_2700_ = lean_ctor_get(v_x_2698_, 2);
lean_inc(v_v_2700_);
v_l_2701_ = lean_ctor_get(v_x_2698_, 3);
lean_inc(v_l_2701_);
v_r_2702_ = lean_ctor_get(v_x_2698_, 4);
lean_inc(v_r_2702_);
lean_dec_ref(v_x_2698_);
v___x_2703_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2697_, v_l_2701_);
v___x_2704_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_2700_, v_k_2699_, v___x_2703_);
v_init_2697_ = v___x_2704_;
v_x_2698_ = v_r_2702_;
goto _start;
}
else
{
return v_init_2697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_2706_, lean_object* v_l_u2082_2707_){
_start:
{
lean_object* v_reported_2708_; lean_object* v_unreported_2709_; lean_object* v_loggedKinds_2710_; lean_object* v_reported_2711_; lean_object* v_unreported_2712_; lean_object* v_loggedKinds_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2723_; 
v_reported_2708_ = lean_ctor_get(v_l_u2081_2706_, 0);
lean_inc_ref(v_reported_2708_);
v_unreported_2709_ = lean_ctor_get(v_l_u2081_2706_, 1);
lean_inc_ref(v_unreported_2709_);
v_loggedKinds_2710_ = lean_ctor_get(v_l_u2081_2706_, 2);
lean_inc(v_loggedKinds_2710_);
lean_dec_ref(v_l_u2081_2706_);
v_reported_2711_ = lean_ctor_get(v_l_u2082_2707_, 0);
v_unreported_2712_ = lean_ctor_get(v_l_u2082_2707_, 1);
v_loggedKinds_2713_ = lean_ctor_get(v_l_u2082_2707_, 2);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_l_u2082_2707_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2715_ = v_l_u2082_2707_;
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_loggedKinds_2713_);
lean_inc(v_unreported_2712_);
lean_inc(v_reported_2711_);
lean_dec(v_l_u2082_2707_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2717_ = l_Lean_PersistentArray_append___redArg(v_reported_2708_, v_reported_2711_);
lean_dec_ref(v_reported_2711_);
v___x_2718_ = l_Lean_PersistentArray_append___redArg(v_unreported_2709_, v_unreported_2712_);
lean_dec_ref(v_unreported_2712_);
v___x_2719_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_2710_, v_loggedKinds_2713_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 2, v___x_2719_);
lean_ctor_set(v___x_2715_, 1, v___x_2718_);
lean_ctor_set(v___x_2715_, 0, v___x_2717_);
v___x_2721_ = v___x_2715_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_2724_, lean_object* v_k_2725_, lean_object* v_t_2726_, lean_object* v_hl_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2724_, v_k_2725_, v_t_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_2729_, lean_object* v_t_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2729_, v_t_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_2734_, size_t v_i_2735_, size_t v_stop_2736_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_usize_dec_eq(v_i_2735_, v_stop_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; uint8_t v_severity_2739_; uint8_t v___x_2740_; 
v___x_2738_ = lean_array_uget_borrowed(v_as_2734_, v_i_2735_);
v_severity_2739_ = lean_ctor_get_uint8(v___x_2738_, sizeof(void*)*5 + 1);
v___x_2740_ = 1;
if (v_severity_2739_ == 2)
{
return v___x_2740_;
}
else
{
if (v___x_2737_ == 0)
{
size_t v___x_2741_; size_t v___x_2742_; 
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2735_, v___x_2741_);
v_i_2735_ = v___x_2742_;
goto _start;
}
else
{
return v___x_2740_;
}
}
}
else
{
uint8_t v___x_2744_; 
v___x_2744_ = 0;
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_2745_, lean_object* v_i_2746_, lean_object* v_stop_2747_){
_start:
{
size_t v_i_boxed_2748_; size_t v_stop_boxed_2749_; uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_i_boxed_2748_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_stop_boxed_2749_ = lean_unbox_usize(v_stop_2747_);
lean_dec(v_stop_2747_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_2745_, v_i_boxed_2748_, v_stop_boxed_2749_);
lean_dec_ref(v_as_2745_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
lean_object* v_cs_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_cs_2753_ = lean_ctor_get(v_x_2752_, 0);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_array_get_size(v_cs_2753_);
v___x_2756_ = lean_nat_dec_lt(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
return v___x_2756_;
}
else
{
if (v___x_2756_ == 0)
{
return v___x_2756_;
}
else
{
size_t v___x_2757_; size_t v___x_2758_; uint8_t v___x_2759_; 
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = lean_usize_of_nat(v___x_2755_);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_2753_, v___x_2757_, v___x_2758_);
return v___x_2759_;
}
}
}
else
{
lean_object* v_vs_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_vs_2760_ = lean_ctor_get(v_x_2752_, 0);
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = lean_array_get_size(v_vs_2760_);
v___x_2763_ = lean_nat_dec_lt(v___x_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
return v___x_2763_;
}
else
{
if (v___x_2763_ == 0)
{
return v___x_2763_;
}
else
{
size_t v___x_2764_; size_t v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = ((size_t)0ULL);
v___x_2765_ = lean_usize_of_nat(v___x_2762_);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_2760_, v___x_2764_, v___x_2765_);
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_2767_, size_t v_i_2768_, size_t v_stop_2769_){
_start:
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_usize_dec_eq(v_i_2768_, v_stop_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = lean_array_uget_borrowed(v_as_2767_, v_i_2768_);
v___x_2772_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_2771_);
if (v___x_2772_ == 0)
{
size_t v___x_2773_; size_t v___x_2774_; 
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2768_, v___x_2773_);
v_i_2768_ = v___x_2774_;
goto _start;
}
else
{
return v___x_2772_;
}
}
else
{
uint8_t v___x_2776_; 
v___x_2776_ = 0;
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_2777_, lean_object* v_i_2778_, lean_object* v_stop_2779_){
_start:
{
size_t v_i_boxed_2780_; size_t v_stop_boxed_2781_; uint8_t v_res_2782_; lean_object* v_r_2783_; 
v_i_boxed_2780_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2779_);
lean_dec(v_stop_2779_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_2777_, v_i_boxed_2780_, v_stop_boxed_2781_);
lean_dec_ref(v_as_2777_);
v_r_2783_ = lean_box(v_res_2782_);
return v_r_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_2784_);
lean_dec_ref(v_x_2784_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_2787_){
_start:
{
lean_object* v_root_2788_; lean_object* v_tail_2789_; uint8_t v___x_2790_; 
v_root_2788_ = lean_ctor_get(v_t_2787_, 0);
v_tail_2789_ = lean_ctor_get(v_t_2787_, 1);
v___x_2790_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_2788_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_array_get_size(v_tail_2789_);
v___x_2793_ = lean_nat_dec_lt(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
return v___x_2790_;
}
else
{
if (v___x_2793_ == 0)
{
return v___x_2790_;
}
else
{
size_t v___x_2794_; size_t v___x_2795_; uint8_t v___x_2796_; 
v___x_2794_ = ((size_t)0ULL);
v___x_2795_ = lean_usize_of_nat(v___x_2792_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_2789_, v___x_2794_, v___x_2795_);
return v___x_2796_;
}
}
}
else
{
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_2797_){
_start:
{
uint8_t v_res_2798_; lean_object* v_r_2799_; 
v_res_2798_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_2797_);
lean_dec_ref(v_t_2797_);
v_r_2799_ = lean_box(v_res_2798_);
return v_r_2799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_2800_, lean_object* v_as_2801_, size_t v_i_2802_, size_t v_stop_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_eq(v_i_2802_, v_stop_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; uint8_t v_severity_2806_; uint8_t v___x_2807_; 
v___x_2805_ = lean_array_uget_borrowed(v_as_2801_, v_i_2802_);
v_severity_2806_ = lean_ctor_get_uint8(v___x_2805_, sizeof(void*)*5 + 1);
v___x_2807_ = 1;
if (v_severity_2806_ == 2)
{
return v___x_2807_;
}
else
{
if (v___x_2800_ == 0)
{
size_t v___x_2808_; size_t v___x_2809_; 
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2802_, v___x_2808_);
v_i_2802_ = v___x_2809_;
goto _start;
}
else
{
return v___x_2807_;
}
}
}
else
{
uint8_t v___x_2811_; 
v___x_2811_ = 0;
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_2812_, lean_object* v_as_2813_, lean_object* v_i_2814_, lean_object* v_stop_2815_){
_start:
{
uint8_t v___x_1884__boxed_2816_; size_t v_i_boxed_2817_; size_t v_stop_boxed_2818_; uint8_t v_res_2819_; lean_object* v_r_2820_; 
v___x_1884__boxed_2816_ = lean_unbox(v___x_2812_);
v_i_boxed_2817_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_stop_boxed_2818_ = lean_unbox_usize(v_stop_2815_);
lean_dec(v_stop_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_2816_, v_as_2813_, v_i_boxed_2817_, v_stop_boxed_2818_);
lean_dec_ref(v_as_2813_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_2821_, lean_object* v_x_2822_){
_start:
{
if (lean_obj_tag(v_x_2822_) == 0)
{
lean_object* v_cs_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_cs_2823_ = lean_ctor_get(v_x_2822_, 0);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_array_get_size(v_cs_2823_);
v___x_2826_ = lean_nat_dec_lt(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
return v___x_2826_;
}
else
{
if (v___x_2826_ == 0)
{
return v___x_2826_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_of_nat(v___x_2825_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_2821_, v_cs_2823_, v___x_2827_, v___x_2828_);
return v___x_2829_;
}
}
}
else
{
lean_object* v_vs_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v_vs_2830_ = lean_ctor_get(v_x_2822_, 0);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = lean_array_get_size(v_vs_2830_);
v___x_2833_ = lean_nat_dec_lt(v___x_2831_, v___x_2832_);
if (v___x_2833_ == 0)
{
return v___x_2833_;
}
else
{
if (v___x_2833_ == 0)
{
return v___x_2833_;
}
else
{
size_t v___x_2834_; size_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = ((size_t)0ULL);
v___x_2835_ = lean_usize_of_nat(v___x_2832_);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2821_, v_vs_2830_, v___x_2834_, v___x_2835_);
return v___x_2836_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_2837_, lean_object* v_as_2838_, size_t v_i_2839_, size_t v_stop_2840_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_eq(v_i_2839_, v_stop_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = lean_array_uget_borrowed(v_as_2838_, v_i_2839_);
v___x_2843_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2837_, v___x_2842_);
if (v___x_2843_ == 0)
{
size_t v___x_2844_; size_t v___x_2845_; 
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_i_2839_, v___x_2844_);
v_i_2839_ = v___x_2845_;
goto _start;
}
else
{
return v___x_2843_;
}
}
else
{
uint8_t v___x_2847_; 
v___x_2847_ = 0;
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2848_, lean_object* v_as_2849_, lean_object* v_i_2850_, lean_object* v_stop_2851_){
_start:
{
uint8_t v___x_1901__boxed_2852_; size_t v_i_boxed_2853_; size_t v_stop_boxed_2854_; uint8_t v_res_2855_; lean_object* v_r_2856_; 
v___x_1901__boxed_2852_ = lean_unbox(v___x_2848_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_stop_boxed_2854_ = lean_unbox_usize(v_stop_2851_);
lean_dec(v_stop_2851_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_2852_, v_as_2849_, v_i_boxed_2853_, v_stop_boxed_2854_);
lean_dec_ref(v_as_2849_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_2857_, lean_object* v_x_2858_){
_start:
{
uint8_t v___x_1909__boxed_2859_; uint8_t v_res_2860_; lean_object* v_r_2861_; 
v___x_1909__boxed_2859_ = lean_unbox(v___x_2857_);
v_res_2860_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_2859_, v_x_2858_);
lean_dec_ref(v_x_2858_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_2862_, lean_object* v_t_2863_){
_start:
{
lean_object* v_root_2864_; lean_object* v_tail_2865_; uint8_t v___x_2866_; 
v_root_2864_ = lean_ctor_get(v_t_2863_, 0);
v_tail_2865_ = lean_ctor_get(v_t_2863_, 1);
v___x_2866_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2862_, v_root_2864_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = lean_array_get_size(v_tail_2865_);
v___x_2869_ = lean_nat_dec_lt(v___x_2867_, v___x_2868_);
if (v___x_2869_ == 0)
{
return v___x_2866_;
}
else
{
if (v___x_2869_ == 0)
{
return v___x_2866_;
}
else
{
size_t v___x_2870_; size_t v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = lean_usize_of_nat(v___x_2868_);
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2862_, v_tail_2865_, v___x_2870_, v___x_2871_);
return v___x_2872_;
}
}
}
else
{
return v___x_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_2873_, lean_object* v_t_2874_){
_start:
{
uint8_t v___x_1952__boxed_2875_; uint8_t v_res_2876_; lean_object* v_r_2877_; 
v___x_1952__boxed_2875_ = lean_unbox(v___x_2873_);
v_res_2876_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_2875_, v_t_2874_);
lean_dec_ref(v_t_2874_);
v_r_2877_ = lean_box(v_res_2876_);
return v_r_2877_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_2878_){
_start:
{
lean_object* v_reported_2879_; lean_object* v_unreported_2880_; uint8_t v___x_2881_; 
v_reported_2879_ = lean_ctor_get(v_log_2878_, 0);
v_unreported_2880_ = lean_ctor_get(v_log_2878_, 1);
v___x_2881_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_2879_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
v___x_2882_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_2881_, v_unreported_2880_);
return v___x_2882_;
}
else
{
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_2883_){
_start:
{
uint8_t v_res_2884_; lean_object* v_r_2885_; 
v_res_2884_ = l_Lean_MessageLog_hasErrors(v_log_2883_);
lean_dec_ref(v_log_2883_);
v_r_2885_ = lean_box(v_res_2884_);
return v_r_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_2886_){
_start:
{
lean_object* v_reported_2887_; lean_object* v_unreported_2888_; lean_object* v_loggedKinds_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2900_; 
v_reported_2887_ = lean_ctor_get(v_log_2886_, 0);
v_unreported_2888_ = lean_ctor_get(v_log_2886_, 1);
v_loggedKinds_2889_ = lean_ctor_get(v_log_2886_, 2);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_log_2886_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2891_ = v_log_2886_;
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_loggedKinds_2889_);
lean_inc(v_unreported_2888_);
lean_inc(v_reported_2887_);
lean_dec(v_log_2886_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2893_ = l_Lean_PersistentArray_append___redArg(v_reported_2887_, v_unreported_2888_);
lean_dec_ref(v_unreported_2888_);
v___x_2894_ = lean_unsigned_to_nat(32u);
v___x_2895_ = lean_mk_empty_array_with_capacity(v___x_2894_);
lean_dec_ref(v___x_2895_);
v___x_2896_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2896_);
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2898_ = v___x_2891_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_loggedKinds_2889_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_bs_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
if (v___x_2904_ == 0)
{
return v_bs_2903_;
}
else
{
lean_object* v_v_2905_; lean_object* v_fileName_2906_; lean_object* v_pos_2907_; lean_object* v_endPos_2908_; uint8_t v_keepFullRange_2909_; uint8_t v_severity_2910_; uint8_t v_isSilent_2911_; lean_object* v_caption_2912_; lean_object* v_data_2913_; lean_object* v___x_2914_; lean_object* v_bs_x27_2915_; lean_object* v___y_2917_; 
v_v_2905_ = lean_array_uget(v_bs_2903_, v_i_2902_);
v_fileName_2906_ = lean_ctor_get(v_v_2905_, 0);
v_pos_2907_ = lean_ctor_get(v_v_2905_, 1);
v_endPos_2908_ = lean_ctor_get(v_v_2905_, 2);
v_keepFullRange_2909_ = lean_ctor_get_uint8(v_v_2905_, sizeof(void*)*5);
v_severity_2910_ = lean_ctor_get_uint8(v_v_2905_, sizeof(void*)*5 + 1);
v_isSilent_2911_ = lean_ctor_get_uint8(v_v_2905_, sizeof(void*)*5 + 2);
v_caption_2912_ = lean_ctor_get(v_v_2905_, 3);
v_data_2913_ = lean_ctor_get(v_v_2905_, 4);
v___x_2914_ = lean_unsigned_to_nat(0u);
v_bs_x27_2915_ = lean_array_uset(v_bs_2903_, v_i_2902_, v___x_2914_);
if (v_severity_2910_ == 2)
{
lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2929_; 
lean_inc(v_data_2913_);
lean_inc_ref(v_caption_2912_);
lean_inc(v_endPos_2908_);
lean_inc_ref(v_pos_2907_);
lean_inc_ref(v_fileName_2906_);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_v_2905_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; lean_object* v_unused_2931_; lean_object* v_unused_2932_; lean_object* v_unused_2933_; lean_object* v_unused_2934_; 
v_unused_2930_ = lean_ctor_get(v_v_2905_, 4);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_v_2905_, 3);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_v_2905_, 2);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_v_2905_, 1);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_v_2905_, 0);
lean_dec(v_unused_2934_);
v___x_2923_ = v_v_2905_;
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
else
{
lean_dec(v_v_2905_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
uint8_t v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = 1;
if (v_isShared_2924_ == 0)
{
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_fileName_2906_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_pos_2907_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_endPos_2908_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_caption_2912_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_data_2913_);
lean_ctor_set_uint8(v_reuseFailAlloc_2928_, sizeof(void*)*5, v_keepFullRange_2909_);
lean_ctor_set_uint8(v_reuseFailAlloc_2928_, sizeof(void*)*5 + 2, v_isSilent_2911_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*5 + 1, v___x_2925_);
v___y_2917_ = v___x_2927_;
goto v___jp_2916_;
}
}
}
else
{
v___y_2917_ = v_v_2905_;
goto v___jp_2916_;
}
v___jp_2916_:
{
size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2902_, v___x_2918_);
v___x_2920_ = lean_array_uset(v_bs_x27_2915_, v_i_2902_, v___y_2917_);
v_i_2902_ = v___x_2919_;
v_bs_2903_ = v___x_2920_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_bs_2937_){
_start:
{
size_t v_sz_boxed_2938_; size_t v_i_boxed_2939_; lean_object* v_res_2940_; 
v_sz_boxed_2938_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2939_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_2938_, v_i_boxed_2939_, v_bs_2937_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_2941_, size_t v_i_2942_, lean_object* v_bs_2943_){
_start:
{
uint8_t v___x_2944_; 
v___x_2944_ = lean_usize_dec_lt(v_i_2942_, v_sz_2941_);
if (v___x_2944_ == 0)
{
return v_bs_2943_;
}
else
{
lean_object* v_v_2945_; lean_object* v___x_2946_; lean_object* v_bs_x27_2947_; lean_object* v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v_v_2945_ = lean_array_uget(v_bs_2943_, v_i_2942_);
v___x_2946_ = lean_unsigned_to_nat(0u);
v_bs_x27_2947_ = lean_array_uset(v_bs_2943_, v_i_2942_, v___x_2946_);
v___x_2948_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_2945_);
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_add(v_i_2942_, v___x_2949_);
v___x_2951_ = lean_array_uset(v_bs_x27_2947_, v_i_2942_, v___x_2948_);
v_i_2942_ = v___x_2950_;
v_bs_2943_ = v___x_2951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_2953_){
_start:
{
if (lean_obj_tag(v_x_2953_) == 0)
{
lean_object* v_cs_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2964_; 
v_cs_2954_ = lean_ctor_get(v_x_2953_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2953_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2956_ = v_x_2953_;
v_isShared_2957_ = v_isSharedCheck_2964_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_cs_2954_);
lean_dec(v_x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2964_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
size_t v_sz_2958_; size_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v_sz_2958_ = lean_array_size(v_cs_2954_);
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_2958_, v___x_2959_, v_cs_2954_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2960_);
v___x_2962_ = v___x_2956_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v_vs_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2975_; 
v_vs_2965_ = lean_ctor_get(v_x_2953_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_x_2953_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2967_ = v_x_2953_;
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_vs_2965_);
lean_dec(v_x_2953_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
size_t v_sz_2969_; size_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v_sz_2969_ = lean_array_size(v_vs_2965_);
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2969_, v___x_2970_, v_vs_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2971_);
v___x_2973_ = v___x_2967_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2976_, lean_object* v_i_2977_, lean_object* v_bs_2978_){
_start:
{
size_t v_sz_boxed_2979_; size_t v_i_boxed_2980_; lean_object* v_res_2981_; 
v_sz_boxed_2979_ = lean_unbox_usize(v_sz_2976_);
lean_dec(v_sz_2976_);
v_i_boxed_2980_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_2979_, v_i_boxed_2980_, v_bs_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_2982_){
_start:
{
lean_object* v_root_2983_; lean_object* v_tail_2984_; lean_object* v_size_2985_; size_t v_shift_2986_; lean_object* v_tailOff_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2998_; 
v_root_2983_ = lean_ctor_get(v_t_2982_, 0);
v_tail_2984_ = lean_ctor_get(v_t_2982_, 1);
v_size_2985_ = lean_ctor_get(v_t_2982_, 2);
v_shift_2986_ = lean_ctor_get_usize(v_t_2982_, 4);
v_tailOff_2987_ = lean_ctor_get(v_t_2982_, 3);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_t_2982_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2989_ = v_t_2982_;
v_isShared_2990_ = v_isSharedCheck_2998_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_tailOff_2987_);
lean_inc(v_size_2985_);
lean_inc(v_tail_2984_);
lean_inc(v_root_2983_);
lean_dec(v_t_2982_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2998_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2991_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_2983_);
v_sz_2992_ = lean_array_size(v_tail_2984_);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2992_, v___x_2993_, v_tail_2984_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_2994_);
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2996_ = v___x_2989_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_size_2985_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v_tailOff_2987_);
lean_ctor_set_usize(v_reuseFailAlloc_2997_, 4, v_shift_2986_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_unreported_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3012_; 
v___x_3000_ = lean_unsigned_to_nat(32u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
lean_dec_ref(v___x_3001_);
v___x_3002_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3003_ = lean_ctor_get(v_log_2999_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_log_2999_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; lean_object* v_unused_3014_; 
v_unused_3013_ = lean_ctor_get(v_log_2999_, 2);
lean_dec(v_unused_3013_);
v_unused_3014_ = lean_ctor_get(v_log_2999_, 0);
lean_dec(v_unused_3014_);
v___x_3005_ = v_log_2999_;
v_isShared_3006_ = v_isSharedCheck_3012_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_unreported_3003_);
lean_dec(v_log_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3012_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3007_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3003_);
v___x_3008_ = l_Lean_NameSet_empty;
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 2, v___x_3008_);
lean_ctor_set(v___x_3005_, 1, v___x_3007_);
lean_ctor_set(v___x_3005_, 0, v___x_3002_);
v___x_3010_ = v___x_3005_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3015_, size_t v_i_3016_, lean_object* v_bs_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_usize_dec_lt(v_i_3016_, v_sz_3015_);
if (v___x_3018_ == 0)
{
return v_bs_3017_;
}
else
{
lean_object* v_v_3019_; lean_object* v_fileName_3020_; lean_object* v_pos_3021_; lean_object* v_endPos_3022_; uint8_t v_keepFullRange_3023_; uint8_t v_severity_3024_; uint8_t v_isSilent_3025_; lean_object* v_caption_3026_; lean_object* v_data_3027_; lean_object* v___x_3028_; lean_object* v_bs_x27_3029_; lean_object* v___y_3031_; 
v_v_3019_ = lean_array_uget(v_bs_3017_, v_i_3016_);
v_fileName_3020_ = lean_ctor_get(v_v_3019_, 0);
v_pos_3021_ = lean_ctor_get(v_v_3019_, 1);
v_endPos_3022_ = lean_ctor_get(v_v_3019_, 2);
v_keepFullRange_3023_ = lean_ctor_get_uint8(v_v_3019_, sizeof(void*)*5);
v_severity_3024_ = lean_ctor_get_uint8(v_v_3019_, sizeof(void*)*5 + 1);
v_isSilent_3025_ = lean_ctor_get_uint8(v_v_3019_, sizeof(void*)*5 + 2);
v_caption_3026_ = lean_ctor_get(v_v_3019_, 3);
v_data_3027_ = lean_ctor_get(v_v_3019_, 4);
v___x_3028_ = lean_unsigned_to_nat(0u);
v_bs_x27_3029_ = lean_array_uset(v_bs_3017_, v_i_3016_, v___x_3028_);
if (v_severity_3024_ == 2)
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3043_; 
lean_inc(v_data_3027_);
lean_inc_ref(v_caption_3026_);
lean_inc(v_endPos_3022_);
lean_inc_ref(v_pos_3021_);
lean_inc_ref(v_fileName_3020_);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_v_3019_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; lean_object* v_unused_3045_; lean_object* v_unused_3046_; lean_object* v_unused_3047_; lean_object* v_unused_3048_; 
v_unused_3044_ = lean_ctor_get(v_v_3019_, 4);
lean_dec(v_unused_3044_);
v_unused_3045_ = lean_ctor_get(v_v_3019_, 3);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v_v_3019_, 2);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_v_3019_, 1);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v_v_3019_, 0);
lean_dec(v_unused_3048_);
v___x_3037_ = v_v_3019_;
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v_v_3019_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
uint8_t v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = 0;
if (v_isShared_3038_ == 0)
{
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_fileName_3020_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_pos_3021_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_endPos_3022_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_caption_3026_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_data_3027_);
lean_ctor_set_uint8(v_reuseFailAlloc_3042_, sizeof(void*)*5, v_keepFullRange_3023_);
lean_ctor_set_uint8(v_reuseFailAlloc_3042_, sizeof(void*)*5 + 2, v_isSilent_3025_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_ctor_set_uint8(v___x_3041_, sizeof(void*)*5 + 1, v___x_3039_);
v___y_3031_ = v___x_3041_;
goto v___jp_3030_;
}
}
}
else
{
v___y_3031_ = v_v_3019_;
goto v___jp_3030_;
}
v___jp_3030_:
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_add(v_i_3016_, v___x_3032_);
v___x_3034_ = lean_array_uset(v_bs_x27_3029_, v_i_3016_, v___y_3031_);
v_i_3016_ = v___x_3033_;
v_bs_3017_ = v___x_3034_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3049_, lean_object* v_i_3050_, lean_object* v_bs_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3049_);
lean_dec(v_sz_3049_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3050_);
lean_dec(v_i_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3052_, v_i_boxed_3053_, v_bs_3051_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_bs_3057_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3056_, v_sz_3055_);
if (v___x_3058_ == 0)
{
return v_bs_3057_;
}
else
{
lean_object* v_v_3059_; lean_object* v___x_3060_; lean_object* v_bs_x27_3061_; lean_object* v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v_v_3059_ = lean_array_uget(v_bs_3057_, v_i_3056_);
v___x_3060_ = lean_unsigned_to_nat(0u);
v_bs_x27_3061_ = lean_array_uset(v_bs_3057_, v_i_3056_, v___x_3060_);
v___x_3062_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3059_);
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3056_, v___x_3063_);
v___x_3065_ = lean_array_uset(v_bs_x27_3061_, v_i_3056_, v___x_3062_);
v_i_3056_ = v___x_3064_;
v_bs_3057_ = v___x_3065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3067_){
_start:
{
if (lean_obj_tag(v_x_3067_) == 0)
{
lean_object* v_cs_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3078_; 
v_cs_3068_ = lean_ctor_get(v_x_3067_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_x_3067_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3070_ = v_x_3067_;
v_isShared_3071_ = v_isSharedCheck_3078_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_cs_3068_);
lean_dec(v_x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3078_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
size_t v_sz_3072_; size_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v_sz_3072_ = lean_array_size(v_cs_3068_);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3072_, v___x_3073_, v_cs_3068_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3074_);
v___x_3076_ = v___x_3070_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
else
{
lean_object* v_vs_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3089_; 
v_vs_3079_ = lean_ctor_get(v_x_3067_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_x_3067_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3081_ = v_x_3067_;
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_vs_3079_);
lean_dec(v_x_3067_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
size_t v_sz_3083_; size_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v_sz_3083_ = lean_array_size(v_vs_3079_);
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3083_, v___x_3084_, v_vs_3079_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3085_);
v___x_3087_ = v___x_3081_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3090_, lean_object* v_i_3091_, lean_object* v_bs_3092_){
_start:
{
size_t v_sz_boxed_3093_; size_t v_i_boxed_3094_; lean_object* v_res_3095_; 
v_sz_boxed_3093_ = lean_unbox_usize(v_sz_3090_);
lean_dec(v_sz_3090_);
v_i_boxed_3094_ = lean_unbox_usize(v_i_3091_);
lean_dec(v_i_3091_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3093_, v_i_boxed_3094_, v_bs_3092_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3096_){
_start:
{
lean_object* v_root_3097_; lean_object* v_tail_3098_; lean_object* v_size_3099_; size_t v_shift_3100_; lean_object* v_tailOff_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3112_; 
v_root_3097_ = lean_ctor_get(v_t_3096_, 0);
v_tail_3098_ = lean_ctor_get(v_t_3096_, 1);
v_size_3099_ = lean_ctor_get(v_t_3096_, 2);
v_shift_3100_ = lean_ctor_get_usize(v_t_3096_, 4);
v_tailOff_3101_ = lean_ctor_get(v_t_3096_, 3);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_t_3096_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3103_ = v_t_3096_;
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_tailOff_3101_);
lean_inc(v_size_3099_);
lean_inc(v_tail_3098_);
lean_inc(v_root_3097_);
lean_dec(v_t_3096_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; size_t v_sz_3106_; size_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3105_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3097_);
v_sz_3106_ = lean_array_size(v_tail_3098_);
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3106_, v___x_3107_, v_tail_3098_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 1, v___x_3108_);
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3110_ = v___x_3103_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_size_3099_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_tailOff_3101_);
lean_ctor_set_usize(v_reuseFailAlloc_3111_, 4, v_shift_3100_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3113_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_unreported_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3126_; 
v___x_3114_ = lean_unsigned_to_nat(32u);
v___x_3115_ = lean_mk_empty_array_with_capacity(v___x_3114_);
lean_dec_ref(v___x_3115_);
v___x_3116_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3117_ = lean_ctor_get(v_log_3113_, 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_log_3113_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; lean_object* v_unused_3128_; 
v_unused_3127_ = lean_ctor_get(v_log_3113_, 2);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_log_3113_, 0);
lean_dec(v_unused_3128_);
v___x_3119_ = v_log_3113_;
v_isShared_3120_ = v_isSharedCheck_3126_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_unreported_3117_);
lean_dec(v_log_3113_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3126_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3121_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3117_);
v___x_3122_ = l_Lean_NameSet_empty;
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 2, v___x_3122_);
lean_ctor_set(v___x_3119_, 1, v___x_3121_);
lean_ctor_set(v___x_3119_, 0, v___x_3116_);
v___x_3124_ = v___x_3119_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3129_, size_t v_i_3130_, size_t v_stop_3131_, lean_object* v_b_3132_){
_start:
{
lean_object* v___y_3134_; uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; uint8_t v_severity_3140_; 
v___x_3139_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
v_severity_3140_ = lean_ctor_get_uint8(v___x_3139_, sizeof(void*)*5 + 1);
if (v_severity_3140_ == 0)
{
lean_object* v___x_3141_; 
lean_inc(v___x_3139_);
v___x_3141_ = l_Lean_PersistentArray_push___redArg(v_b_3132_, v___x_3139_);
v___y_3134_ = v___x_3141_;
goto v___jp_3133_;
}
else
{
v___y_3134_ = v_b_3132_;
goto v___jp_3133_;
}
}
else
{
return v_b_3132_;
}
v___jp_3133_:
{
size_t v___x_3135_; size_t v___x_3136_; 
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = lean_usize_add(v_i_3130_, v___x_3135_);
v_i_3130_ = v___x_3136_;
v_b_3132_ = v___y_3134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3142_, lean_object* v_i_3143_, lean_object* v_stop_3144_, lean_object* v_b_3145_){
_start:
{
size_t v_i_boxed_3146_; size_t v_stop_boxed_3147_; lean_object* v_res_3148_; 
v_i_boxed_3146_ = lean_unbox_usize(v_i_3143_);
lean_dec(v_i_3143_);
v_stop_boxed_3147_ = lean_unbox_usize(v_stop_3144_);
lean_dec(v_stop_3144_);
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3142_, v_i_boxed_3146_, v_stop_boxed_3147_, v_b_3145_);
lean_dec_ref(v_as_3142_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3149_, lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3149_) == 0)
{
lean_object* v_cs_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_cs_3151_ = lean_ctor_get(v_x_3149_, 0);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_array_get_size(v_cs_3151_);
v___x_3154_ = lean_nat_dec_lt(v___x_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
return v_x_3150_;
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_nat_dec_le(v___x_3153_, v___x_3153_);
if (v___x_3155_ == 0)
{
if (v___x_3154_ == 0)
{
return v_x_3150_;
}
else
{
size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = lean_usize_of_nat(v___x_3153_);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3151_, v___x_3156_, v___x_3157_, v_x_3150_);
return v___x_3158_;
}
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3153_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3151_, v___x_3159_, v___x_3160_, v_x_3150_);
return v___x_3161_;
}
}
}
else
{
lean_object* v_vs_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_vs_3162_ = lean_ctor_get(v_x_3149_, 0);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_array_get_size(v_vs_3162_);
v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
return v_x_3150_;
}
else
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_nat_dec_le(v___x_3164_, v___x_3164_);
if (v___x_3166_ == 0)
{
if (v___x_3165_ == 0)
{
return v_x_3150_;
}
else
{
size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = ((size_t)0ULL);
v___x_3168_ = lean_usize_of_nat(v___x_3164_);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3162_, v___x_3167_, v___x_3168_, v_x_3150_);
return v___x_3169_;
}
}
else
{
size_t v___x_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = lean_usize_of_nat(v___x_3164_);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3162_, v___x_3170_, v___x_3171_, v_x_3150_);
return v___x_3172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3173_, size_t v_i_3174_, size_t v_stop_3175_, lean_object* v_b_3176_){
_start:
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_usize_dec_eq(v_i_3174_, v_stop_3175_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; size_t v___x_3180_; size_t v___x_3181_; 
v___x_3178_ = lean_array_uget_borrowed(v_as_3173_, v_i_3174_);
v___x_3179_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3178_, v_b_3176_);
v___x_3180_ = ((size_t)1ULL);
v___x_3181_ = lean_usize_add(v_i_3174_, v___x_3180_);
v_i_3174_ = v___x_3181_;
v_b_3176_ = v___x_3179_;
goto _start;
}
else
{
return v_b_3176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3183_, lean_object* v_i_3184_, lean_object* v_stop_3185_, lean_object* v_b_3186_){
_start:
{
size_t v_i_boxed_3187_; size_t v_stop_boxed_3188_; lean_object* v_res_3189_; 
v_i_boxed_3187_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_stop_boxed_3188_ = lean_unbox_usize(v_stop_3185_);
lean_dec(v_stop_3185_);
v_res_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3183_, v_i_boxed_3187_, v_stop_boxed_3188_, v_b_3186_);
lean_dec_ref(v_as_3183_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3190_, v_x_3191_);
lean_dec_ref(v_x_3190_);
return v_res_3192_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3194_, size_t v_x_3195_, size_t v_x_3196_, lean_object* v_x_3197_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_object* v_cs_3198_; lean_object* v___x_3199_; size_t v___x_3200_; lean_object* v_j_3201_; lean_object* v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; size_t v___x_3205_; size_t v___x_3206_; size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_cs_3198_ = lean_ctor_get(v_x_3194_, 0);
v___x_3199_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3200_ = lean_usize_shift_right(v_x_3195_, v_x_3196_);
v_j_3201_ = lean_usize_to_nat(v___x_3200_);
v___x_3202_ = lean_array_get_borrowed(v___x_3199_, v_cs_3198_, v_j_3201_);
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_shift_left(v___x_3203_, v_x_3196_);
v___x_3205_ = lean_usize_sub(v___x_3204_, v___x_3203_);
v___x_3206_ = lean_usize_land(v_x_3195_, v___x_3205_);
v___x_3207_ = ((size_t)5ULL);
v___x_3208_ = lean_usize_sub(v_x_3196_, v___x_3207_);
v___x_3209_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3202_, v___x_3206_, v___x_3208_, v_x_3197_);
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_j_3201_, v___x_3210_);
lean_dec(v_j_3201_);
v___x_3212_ = lean_array_get_size(v_cs_3198_);
v___x_3213_ = lean_nat_dec_lt(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_dec(v___x_3211_);
return v___x_3209_;
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = lean_nat_dec_le(v___x_3212_, v___x_3212_);
if (v___x_3214_ == 0)
{
if (v___x_3213_ == 0)
{
lean_dec(v___x_3211_);
return v___x_3209_;
}
else
{
size_t v___x_3215_; size_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_usize_of_nat(v___x_3211_);
lean_dec(v___x_3211_);
v___x_3216_ = lean_usize_of_nat(v___x_3212_);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3198_, v___x_3215_, v___x_3216_, v___x_3209_);
return v___x_3217_;
}
}
else
{
size_t v___x_3218_; size_t v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_usize_of_nat(v___x_3211_);
lean_dec(v___x_3211_);
v___x_3219_ = lean_usize_of_nat(v___x_3212_);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3198_, v___x_3218_, v___x_3219_, v___x_3209_);
return v___x_3220_;
}
}
}
else
{
lean_object* v_vs_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_vs_3221_ = lean_ctor_get(v_x_3194_, 0);
v___x_3222_ = lean_usize_to_nat(v_x_3195_);
v___x_3223_ = lean_array_get_size(v_vs_3221_);
v___x_3224_ = lean_nat_dec_lt(v___x_3222_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_dec(v___x_3222_);
return v_x_3197_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_nat_dec_le(v___x_3223_, v___x_3223_);
if (v___x_3225_ == 0)
{
if (v___x_3224_ == 0)
{
lean_dec(v___x_3222_);
return v_x_3197_;
}
else
{
size_t v___x_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_usize_of_nat(v___x_3222_);
lean_dec(v___x_3222_);
v___x_3227_ = lean_usize_of_nat(v___x_3223_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3221_, v___x_3226_, v___x_3227_, v_x_3197_);
return v___x_3228_;
}
}
else
{
size_t v___x_3229_; size_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_usize_of_nat(v___x_3222_);
lean_dec(v___x_3222_);
v___x_3230_ = lean_usize_of_nat(v___x_3223_);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3221_, v___x_3229_, v___x_3230_, v_x_3197_);
return v___x_3231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_, lean_object* v_x_3235_){
_start:
{
size_t v_x_1528__boxed_3236_; size_t v_x_1529__boxed_3237_; lean_object* v_res_3238_; 
v_x_1528__boxed_3236_ = lean_unbox_usize(v_x_3233_);
lean_dec(v_x_3233_);
v_x_1529__boxed_3237_ = lean_unbox_usize(v_x_3234_);
lean_dec(v_x_3234_);
v_res_3238_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3232_, v_x_1528__boxed_3236_, v_x_1529__boxed_3237_, v_x_3235_);
lean_dec_ref(v_x_3232_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3239_, lean_object* v_init_3240_, lean_object* v_start_3241_){
_start:
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = lean_nat_dec_eq(v_start_3241_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v_root_3244_; lean_object* v_tail_3245_; size_t v_shift_3246_; lean_object* v_tailOff_3247_; uint8_t v___x_3248_; 
v_root_3244_ = lean_ctor_get(v_t_3239_, 0);
v_tail_3245_ = lean_ctor_get(v_t_3239_, 1);
v_shift_3246_ = lean_ctor_get_usize(v_t_3239_, 4);
v_tailOff_3247_ = lean_ctor_get(v_t_3239_, 3);
v___x_3248_ = lean_nat_dec_le(v_tailOff_3247_, v_start_3241_);
if (v___x_3248_ == 0)
{
size_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3249_ = lean_usize_of_nat(v_start_3241_);
v___x_3250_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3244_, v___x_3249_, v_shift_3246_, v_init_3240_);
v___x_3251_ = lean_array_get_size(v_tail_3245_);
v___x_3252_ = lean_nat_dec_lt(v___x_3242_, v___x_3251_);
if (v___x_3252_ == 0)
{
return v___x_3250_;
}
else
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_nat_dec_le(v___x_3251_, v___x_3251_);
if (v___x_3253_ == 0)
{
if (v___x_3252_ == 0)
{
return v___x_3250_;
}
else
{
size_t v___x_3254_; size_t v___x_3255_; lean_object* v___x_3256_; 
v___x_3254_ = ((size_t)0ULL);
v___x_3255_ = lean_usize_of_nat(v___x_3251_);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3245_, v___x_3254_, v___x_3255_, v___x_3250_);
return v___x_3256_;
}
}
else
{
size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = ((size_t)0ULL);
v___x_3258_ = lean_usize_of_nat(v___x_3251_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3245_, v___x_3257_, v___x_3258_, v___x_3250_);
return v___x_3259_;
}
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3260_ = lean_nat_sub(v_start_3241_, v_tailOff_3247_);
v___x_3261_ = lean_array_get_size(v_tail_3245_);
v___x_3262_ = lean_nat_dec_lt(v___x_3260_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_dec(v___x_3260_);
return v_init_3240_;
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_le(v___x_3261_, v___x_3261_);
if (v___x_3263_ == 0)
{
if (v___x_3262_ == 0)
{
lean_dec(v___x_3260_);
return v_init_3240_;
}
else
{
size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = lean_usize_of_nat(v___x_3260_);
lean_dec(v___x_3260_);
v___x_3265_ = lean_usize_of_nat(v___x_3261_);
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3245_, v___x_3264_, v___x_3265_, v_init_3240_);
return v___x_3266_;
}
}
else
{
size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = lean_usize_of_nat(v___x_3260_);
lean_dec(v___x_3260_);
v___x_3268_ = lean_usize_of_nat(v___x_3261_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3245_, v___x_3267_, v___x_3268_, v_init_3240_);
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_root_3270_; lean_object* v_tail_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_root_3270_ = lean_ctor_get(v_t_3239_, 0);
v_tail_3271_ = lean_ctor_get(v_t_3239_, 1);
v___x_3272_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3270_, v_init_3240_);
v___x_3273_ = lean_array_get_size(v_tail_3271_);
v___x_3274_ = lean_nat_dec_lt(v___x_3242_, v___x_3273_);
if (v___x_3274_ == 0)
{
return v___x_3272_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_le(v___x_3273_, v___x_3273_);
if (v___x_3275_ == 0)
{
if (v___x_3274_ == 0)
{
return v___x_3272_;
}
else
{
size_t v___x_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = lean_usize_of_nat(v___x_3273_);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3271_, v___x_3276_, v___x_3277_, v___x_3272_);
return v___x_3278_;
}
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = lean_usize_of_nat(v___x_3273_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3271_, v___x_3279_, v___x_3280_, v___x_3272_);
return v___x_3281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3282_, lean_object* v_init_3283_, lean_object* v_start_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3282_, v_init_3283_, v_start_3284_);
lean_dec(v_start_3284_);
lean_dec_ref(v_t_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v_unreported_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3300_; 
v___x_3287_ = lean_unsigned_to_nat(32u);
v___x_3288_ = lean_mk_empty_array_with_capacity(v___x_3287_);
lean_dec_ref(v___x_3288_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3291_ = lean_ctor_get(v_log_3286_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_log_3286_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; 
v_unused_3301_ = lean_ctor_get(v_log_3286_, 2);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_log_3286_, 0);
lean_dec(v_unused_3302_);
v___x_3293_ = v_log_3286_;
v_isShared_3294_ = v_isSharedCheck_3300_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_unreported_3291_);
lean_dec(v_log_3286_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3300_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3295_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3291_, v___x_3290_, v___x_3289_);
lean_dec_ref(v_unreported_3291_);
v___x_3296_ = l_Lean_NameSet_empty;
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 2, v___x_3296_);
lean_ctor_set(v___x_3293_, 1, v___x_3295_);
lean_ctor_set(v___x_3293_, 0, v___x_3290_);
v___x_3298_ = v___x_3293_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3303_, size_t v_i_3304_, size_t v_stop_3305_, lean_object* v_b_3306_){
_start:
{
lean_object* v___y_3308_; uint8_t v___x_3312_; 
v___x_3312_ = lean_usize_dec_eq(v_i_3304_, v_stop_3305_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; uint8_t v_severity_3314_; 
v___x_3313_ = lean_array_uget_borrowed(v_as_3303_, v_i_3304_);
v_severity_3314_ = lean_ctor_get_uint8(v___x_3313_, sizeof(void*)*5 + 1);
if (v_severity_3314_ == 1)
{
lean_object* v___x_3315_; 
lean_inc(v___x_3313_);
v___x_3315_ = l_Lean_PersistentArray_push___redArg(v_b_3306_, v___x_3313_);
v___y_3308_ = v___x_3315_;
goto v___jp_3307_;
}
else
{
v___y_3308_ = v_b_3306_;
goto v___jp_3307_;
}
}
else
{
return v_b_3306_;
}
v___jp_3307_:
{
size_t v___x_3309_; size_t v___x_3310_; 
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = lean_usize_add(v_i_3304_, v___x_3309_);
v_i_3304_ = v___x_3310_;
v_b_3306_ = v___y_3308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3316_, lean_object* v_i_3317_, lean_object* v_stop_3318_, lean_object* v_b_3319_){
_start:
{
size_t v_i_boxed_3320_; size_t v_stop_boxed_3321_; lean_object* v_res_3322_; 
v_i_boxed_3320_ = lean_unbox_usize(v_i_3317_);
lean_dec(v_i_3317_);
v_stop_boxed_3321_ = lean_unbox_usize(v_stop_3318_);
lean_dec(v_stop_3318_);
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3316_, v_i_boxed_3320_, v_stop_boxed_3321_, v_b_3319_);
lean_dec_ref(v_as_3316_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3323_, lean_object* v_x_3324_){
_start:
{
if (lean_obj_tag(v_x_3323_) == 0)
{
lean_object* v_cs_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_cs_3325_ = lean_ctor_get(v_x_3323_, 0);
v___x_3326_ = lean_unsigned_to_nat(0u);
v___x_3327_ = lean_array_get_size(v_cs_3325_);
v___x_3328_ = lean_nat_dec_lt(v___x_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
return v_x_3324_;
}
else
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_nat_dec_le(v___x_3327_, v___x_3327_);
if (v___x_3329_ == 0)
{
if (v___x_3328_ == 0)
{
return v_x_3324_;
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3327_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3325_, v___x_3330_, v___x_3331_, v_x_3324_);
return v___x_3332_;
}
}
else
{
size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = lean_usize_of_nat(v___x_3327_);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3325_, v___x_3333_, v___x_3334_, v_x_3324_);
return v___x_3335_;
}
}
}
else
{
lean_object* v_vs_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_vs_3336_ = lean_ctor_get(v_x_3323_, 0);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_array_get_size(v_vs_3336_);
v___x_3339_ = lean_nat_dec_lt(v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
return v_x_3324_;
}
else
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_nat_dec_le(v___x_3338_, v___x_3338_);
if (v___x_3340_ == 0)
{
if (v___x_3339_ == 0)
{
return v_x_3324_;
}
else
{
size_t v___x_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = lean_usize_of_nat(v___x_3338_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3336_, v___x_3341_, v___x_3342_, v_x_3324_);
return v___x_3343_;
}
}
else
{
size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = lean_usize_of_nat(v___x_3338_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3336_, v___x_3344_, v___x_3345_, v_x_3324_);
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3347_, size_t v_i_3348_, size_t v_stop_3349_, lean_object* v_b_3350_){
_start:
{
uint8_t v___x_3351_; 
v___x_3351_ = lean_usize_dec_eq(v_i_3348_, v_stop_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; size_t v___x_3354_; size_t v___x_3355_; 
v___x_3352_ = lean_array_uget_borrowed(v_as_3347_, v_i_3348_);
v___x_3353_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3352_, v_b_3350_);
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3348_, v___x_3354_);
v_i_3348_ = v___x_3355_;
v_b_3350_ = v___x_3353_;
goto _start;
}
else
{
return v_b_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3357_, lean_object* v_i_3358_, lean_object* v_stop_3359_, lean_object* v_b_3360_){
_start:
{
size_t v_i_boxed_3361_; size_t v_stop_boxed_3362_; lean_object* v_res_3363_; 
v_i_boxed_3361_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_stop_boxed_3362_ = lean_unbox_usize(v_stop_3359_);
lean_dec(v_stop_3359_);
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3357_, v_i_boxed_3361_, v_stop_boxed_3362_, v_b_3360_);
lean_dec_ref(v_as_3357_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3364_, lean_object* v_x_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3364_, v_x_3365_);
lean_dec_ref(v_x_3364_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3367_, size_t v_x_3368_, size_t v_x_3369_, lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3367_) == 0)
{
lean_object* v_cs_3371_; lean_object* v___x_3372_; size_t v___x_3373_; lean_object* v_j_3374_; lean_object* v___x_3375_; size_t v___x_3376_; size_t v___x_3377_; size_t v___x_3378_; size_t v___x_3379_; size_t v___x_3380_; size_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_cs_3371_ = lean_ctor_get(v_x_3367_, 0);
v___x_3372_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3373_ = lean_usize_shift_right(v_x_3368_, v_x_3369_);
v_j_3374_ = lean_usize_to_nat(v___x_3373_);
v___x_3375_ = lean_array_get_borrowed(v___x_3372_, v_cs_3371_, v_j_3374_);
v___x_3376_ = ((size_t)1ULL);
v___x_3377_ = lean_usize_shift_left(v___x_3376_, v_x_3369_);
v___x_3378_ = lean_usize_sub(v___x_3377_, v___x_3376_);
v___x_3379_ = lean_usize_land(v_x_3368_, v___x_3378_);
v___x_3380_ = ((size_t)5ULL);
v___x_3381_ = lean_usize_sub(v_x_3369_, v___x_3380_);
v___x_3382_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3375_, v___x_3379_, v___x_3381_, v_x_3370_);
v___x_3383_ = lean_unsigned_to_nat(1u);
v___x_3384_ = lean_nat_add(v_j_3374_, v___x_3383_);
lean_dec(v_j_3374_);
v___x_3385_ = lean_array_get_size(v_cs_3371_);
v___x_3386_ = lean_nat_dec_lt(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec(v___x_3384_);
return v___x_3382_;
}
else
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_nat_dec_le(v___x_3385_, v___x_3385_);
if (v___x_3387_ == 0)
{
if (v___x_3386_ == 0)
{
lean_dec(v___x_3384_);
return v___x_3382_;
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_usize_of_nat(v___x_3384_);
lean_dec(v___x_3384_);
v___x_3389_ = lean_usize_of_nat(v___x_3385_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3371_, v___x_3388_, v___x_3389_, v___x_3382_);
return v___x_3390_;
}
}
else
{
size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_usize_of_nat(v___x_3384_);
lean_dec(v___x_3384_);
v___x_3392_ = lean_usize_of_nat(v___x_3385_);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3371_, v___x_3391_, v___x_3392_, v___x_3382_);
return v___x_3393_;
}
}
}
else
{
lean_object* v_vs_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_vs_3394_ = lean_ctor_get(v_x_3367_, 0);
v___x_3395_ = lean_usize_to_nat(v_x_3368_);
v___x_3396_ = lean_array_get_size(v_vs_3394_);
v___x_3397_ = lean_nat_dec_lt(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec(v___x_3395_);
return v_x_3370_;
}
else
{
uint8_t v___x_3398_; 
v___x_3398_ = lean_nat_dec_le(v___x_3396_, v___x_3396_);
if (v___x_3398_ == 0)
{
if (v___x_3397_ == 0)
{
lean_dec(v___x_3395_);
return v_x_3370_;
}
else
{
size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
v___x_3399_ = lean_usize_of_nat(v___x_3395_);
lean_dec(v___x_3395_);
v___x_3400_ = lean_usize_of_nat(v___x_3396_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3394_, v___x_3399_, v___x_3400_, v_x_3370_);
return v___x_3401_;
}
}
else
{
size_t v___x_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = lean_usize_of_nat(v___x_3395_);
lean_dec(v___x_3395_);
v___x_3403_ = lean_usize_of_nat(v___x_3396_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3394_, v___x_3402_, v___x_3403_, v_x_3370_);
return v___x_3404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3405_, lean_object* v_x_3406_, lean_object* v_x_3407_, lean_object* v_x_3408_){
_start:
{
size_t v_x_1527__boxed_3409_; size_t v_x_1528__boxed_3410_; lean_object* v_res_3411_; 
v_x_1527__boxed_3409_ = lean_unbox_usize(v_x_3406_);
lean_dec(v_x_3406_);
v_x_1528__boxed_3410_ = lean_unbox_usize(v_x_3407_);
lean_dec(v_x_3407_);
v_res_3411_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3405_, v_x_1527__boxed_3409_, v_x_1528__boxed_3410_, v_x_3408_);
lean_dec_ref(v_x_3405_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3412_, lean_object* v_init_3413_, lean_object* v_start_3414_){
_start:
{
lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = lean_unsigned_to_nat(0u);
v___x_3416_ = lean_nat_dec_eq(v_start_3414_, v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v_root_3417_; lean_object* v_tail_3418_; size_t v_shift_3419_; lean_object* v_tailOff_3420_; uint8_t v___x_3421_; 
v_root_3417_ = lean_ctor_get(v_t_3412_, 0);
v_tail_3418_ = lean_ctor_get(v_t_3412_, 1);
v_shift_3419_ = lean_ctor_get_usize(v_t_3412_, 4);
v_tailOff_3420_ = lean_ctor_get(v_t_3412_, 3);
v___x_3421_ = lean_nat_dec_le(v_tailOff_3420_, v_start_3414_);
if (v___x_3421_ == 0)
{
size_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3422_ = lean_usize_of_nat(v_start_3414_);
v___x_3423_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3417_, v___x_3422_, v_shift_3419_, v_init_3413_);
v___x_3424_ = lean_array_get_size(v_tail_3418_);
v___x_3425_ = lean_nat_dec_lt(v___x_3415_, v___x_3424_);
if (v___x_3425_ == 0)
{
return v___x_3423_;
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_nat_dec_le(v___x_3424_, v___x_3424_);
if (v___x_3426_ == 0)
{
if (v___x_3425_ == 0)
{
return v___x_3423_;
}
else
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = lean_usize_of_nat(v___x_3424_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3418_, v___x_3427_, v___x_3428_, v___x_3423_);
return v___x_3429_;
}
}
else
{
size_t v___x_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = lean_usize_of_nat(v___x_3424_);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3418_, v___x_3430_, v___x_3431_, v___x_3423_);
return v___x_3432_;
}
}
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3433_ = lean_nat_sub(v_start_3414_, v_tailOff_3420_);
v___x_3434_ = lean_array_get_size(v_tail_3418_);
v___x_3435_ = lean_nat_dec_lt(v___x_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_dec(v___x_3433_);
return v_init_3413_;
}
else
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_nat_dec_le(v___x_3434_, v___x_3434_);
if (v___x_3436_ == 0)
{
if (v___x_3435_ == 0)
{
lean_dec(v___x_3433_);
return v_init_3413_;
}
else
{
size_t v___x_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = lean_usize_of_nat(v___x_3433_);
lean_dec(v___x_3433_);
v___x_3438_ = lean_usize_of_nat(v___x_3434_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3418_, v___x_3437_, v___x_3438_, v_init_3413_);
return v___x_3439_;
}
}
else
{
size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = lean_usize_of_nat(v___x_3433_);
lean_dec(v___x_3433_);
v___x_3441_ = lean_usize_of_nat(v___x_3434_);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3418_, v___x_3440_, v___x_3441_, v_init_3413_);
return v___x_3442_;
}
}
}
}
else
{
lean_object* v_root_3443_; lean_object* v_tail_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_root_3443_ = lean_ctor_get(v_t_3412_, 0);
v_tail_3444_ = lean_ctor_get(v_t_3412_, 1);
v___x_3445_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3443_, v_init_3413_);
v___x_3446_ = lean_array_get_size(v_tail_3444_);
v___x_3447_ = lean_nat_dec_lt(v___x_3415_, v___x_3446_);
if (v___x_3447_ == 0)
{
return v___x_3445_;
}
else
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_nat_dec_le(v___x_3446_, v___x_3446_);
if (v___x_3448_ == 0)
{
if (v___x_3447_ == 0)
{
return v___x_3445_;
}
else
{
size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = ((size_t)0ULL);
v___x_3450_ = lean_usize_of_nat(v___x_3446_);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3444_, v___x_3449_, v___x_3450_, v___x_3445_);
return v___x_3451_;
}
}
else
{
size_t v___x_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = lean_usize_of_nat(v___x_3446_);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3444_, v___x_3452_, v___x_3453_, v___x_3445_);
return v___x_3454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3455_, lean_object* v_init_3456_, lean_object* v_start_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3455_, v_init_3456_, v_start_3457_);
lean_dec(v_start_3457_);
lean_dec_ref(v_t_3455_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3459_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_unreported_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3473_; 
v___x_3460_ = lean_unsigned_to_nat(32u);
v___x_3461_ = lean_mk_empty_array_with_capacity(v___x_3460_);
lean_dec_ref(v___x_3461_);
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3463_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3464_ = lean_ctor_get(v_log_3459_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_log_3459_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; lean_object* v_unused_3475_; 
v_unused_3474_ = lean_ctor_get(v_log_3459_, 2);
lean_dec(v_unused_3474_);
v_unused_3475_ = lean_ctor_get(v_log_3459_, 0);
lean_dec(v_unused_3475_);
v___x_3466_ = v_log_3459_;
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_unreported_3464_);
lean_dec(v_log_3459_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3464_, v___x_3463_, v___x_3462_);
lean_dec_ref(v_unreported_3464_);
v___x_3469_ = l_Lean_NameSet_empty;
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 2, v___x_3469_);
lean_ctor_set(v___x_3466_, 1, v___x_3468_);
lean_ctor_set(v___x_3466_, 0, v___x_3463_);
v___x_3471_ = v___x_3466_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3476_, lean_object* v_log_3477_, lean_object* v_f_3478_){
_start:
{
lean_object* v_unreported_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_unreported_3479_ = lean_ctor_get(v_log_3477_, 1);
lean_inc_ref(v_unreported_3479_);
lean_dec_ref(v_log_3477_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = l_Lean_PersistentArray_forM___redArg(v_inst_3476_, v_unreported_3479_, v_f_3478_, v___x_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3482_, lean_object* v_inst_3483_, lean_object* v_log_3484_, lean_object* v_f_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_MessageLog_forM___redArg(v_inst_3483_, v_log_3484_, v_f_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3487_){
_start:
{
lean_object* v_unreported_3488_; lean_object* v___x_3489_; 
v_unreported_3488_ = lean_ctor_get(v_log_3487_, 1);
v___x_3489_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_MessageLog_toList(v_log_3490_);
lean_dec_ref(v_log_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3492_){
_start:
{
lean_object* v_unreported_3493_; lean_object* v___x_3494_; 
v_unreported_3493_ = lean_ctor_get(v_log_3492_, 1);
v___x_3494_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_MessageLog_toArray(v_log_3495_);
lean_dec_ref(v_log_3495_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_unsigned_to_nat(2u);
v___x_3499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v_msg_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3500_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v_msg_3500_);
v___x_3503_ = l_Lean_MessageData_nestD(v___x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3504_){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = l_Lean_MessageData_ofExpr(v_e_3504_);
v___x_3506_ = l_Lean_indentD(v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3507_, lean_object* v_msg_3508_){
_start:
{
lean_object* v_env_3510_; lean_object* v_mctx_3511_; lean_object* v_lctx_3512_; lean_object* v_opts_3513_; lean_object* v_currNamespace_3514_; lean_object* v_openDecls_3515_; lean_object* v___x_3516_; lean_object* v_msg_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_env_3510_ = lean_ctor_get(v_ctx_3507_, 0);
v_mctx_3511_ = lean_ctor_get(v_ctx_3507_, 1);
v_lctx_3512_ = lean_ctor_get(v_ctx_3507_, 2);
v_opts_3513_ = lean_ctor_get(v_ctx_3507_, 3);
v_currNamespace_3514_ = lean_ctor_get(v_ctx_3507_, 4);
v_openDecls_3515_ = lean_ctor_get(v_ctx_3507_, 5);
lean_inc(v_openDecls_3515_);
lean_inc(v_currNamespace_3514_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_currNamespace_3514_);
lean_ctor_set(v___x_3516_, 1, v_openDecls_3515_);
v_msg_3517_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3517_, 0, v___x_3516_);
lean_ctor_set(v_msg_3517_, 1, v_msg_3508_);
lean_inc_ref(v_opts_3513_);
lean_inc_ref(v_lctx_3512_);
lean_inc_ref(v_mctx_3511_);
lean_inc_ref(v_env_3510_);
v___x_3518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3518_, 0, v_env_3510_);
lean_ctor_set(v___x_3518_, 1, v_mctx_3511_);
lean_ctor_set(v___x_3518_, 2, v_lctx_3512_);
lean_ctor_set(v___x_3518_, 3, v_opts_3513_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
v___x_3520_ = l_Lean_MessageData_format(v_msg_3517_, v___x_3519_);
v___x_3521_ = l_Std_Format_defWidth;
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = l_Std_Format_pretty(v___x_3520_, v___x_3521_, v___x_3522_, v___x_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3524_, lean_object* v_msg_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3524_, v_msg_3525_);
lean_dec_ref(v_ctx_3524_);
return v_res_3527_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object* v_s_3528_, lean_object* v_a_3529_, uint8_t v_b_3530_){
_start:
{
lean_object* v_str_3531_; lean_object* v_startInclusive_3532_; lean_object* v_endExclusive_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_str_3531_ = lean_ctor_get(v_s_3528_, 0);
v_startInclusive_3532_ = lean_ctor_get(v_s_3528_, 1);
v_endExclusive_3533_ = lean_ctor_get(v_s_3528_, 2);
v___x_3534_ = lean_nat_sub(v_endExclusive_3533_, v_startInclusive_3532_);
v___x_3535_ = lean_nat_dec_eq(v_a_3529_, v___x_3534_);
lean_dec(v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; uint32_t v___x_3537_; uint32_t v___x_3538_; uint8_t v___x_3539_; 
v___x_3536_ = lean_nat_add(v_startInclusive_3532_, v_a_3529_);
lean_dec(v_a_3529_);
v___x_3537_ = lean_string_utf8_get_fast(v_str_3531_, v___x_3536_);
v___x_3538_ = 10;
v___x_3539_ = lean_uint32_dec_eq(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_string_utf8_next_fast(v_str_3531_, v___x_3536_);
lean_dec(v___x_3536_);
v___x_3541_ = lean_nat_sub(v___x_3540_, v_startInclusive_3532_);
v_a_3529_ = v___x_3541_;
v_b_3530_ = v___x_3539_;
goto _start;
}
else
{
lean_dec(v___x_3536_);
return v___x_3539_;
}
}
else
{
lean_dec(v_a_3529_);
return v_b_3530_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object* v_s_3543_, lean_object* v_a_3544_, lean_object* v_b_3545_){
_start:
{
uint8_t v_b_boxed_3546_; uint8_t v_res_3547_; lean_object* v_r_3548_; 
v_b_boxed_3546_ = lean_unbox(v_b_3545_);
v_res_3547_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3543_, v_a_3544_, v_b_boxed_3546_);
lean_dec_ref(v_s_3543_);
v_r_3548_ = lean_box(v_res_3547_);
return v_r_3548_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object* v_s_3549_){
_start:
{
lean_object* v_searcher_3550_; uint8_t v___x_3551_; uint8_t v___x_3552_; 
v_searcher_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = 0;
v___x_3552_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3549_, v_searcher_3550_, v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v_s_3553_){
_start:
{
uint8_t v_res_3554_; lean_object* v_r_3555_; 
v_res_3554_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v_s_3553_);
lean_dec_ref(v_s_3553_);
v_r_3555_ = lean_box(v_res_3554_);
return v_r_3555_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_3560_ = l_Lean_MessageData_ofFormat(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_3565_ = l_Lean_MessageData_ofFormat(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3567_ = l_Lean_MessageData_ofFormat(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3568_, lean_object* v_maxInlineLength_3569_, lean_object* v_ctx_3570_){
_start:
{
lean_object* v_msg_3572_; lean_object* v___x_3573_; uint8_t v___y_3575_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v_msg_3572_ = l_Lean_MessageData_ofExpr(v_e_3568_);
lean_inc_ref(v_msg_3572_);
v___x_3573_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3570_, v_msg_3572_);
v___x_3583_ = lean_string_length(v___x_3573_);
v___x_3584_ = lean_nat_dec_lt(v_maxInlineLength_3569_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = lean_string_utf8_byte_size(v___x_3573_);
v___x_3587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3573_);
lean_ctor_set(v___x_3587_, 1, v___x_3585_);
lean_ctor_set(v___x_3587_, 2, v___x_3586_);
v___x_3588_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3587_);
lean_dec_ref(v___x_3587_);
v___y_3575_ = v___x_3588_;
goto v___jp_3574_;
}
else
{
lean_dec_ref(v___x_3573_);
v___y_3575_ = v___x_3584_;
goto v___jp_3574_;
}
v___jp_3574_:
{
if (v___y_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3576_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v_msg_3572_);
v___x_3578_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = l_Lean_indentD(v_msg_3572_);
v___x_3581_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
return v___x_3582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3589_, lean_object* v_maxInlineLength_3590_, lean_object* v_ctx_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_inlineExpr___lam__0(v_e_3589_, v_maxInlineLength_3590_, v_ctx_3591_);
lean_dec_ref(v_ctx_3591_);
lean_dec(v_maxInlineLength_3590_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3597_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3598_ = l_Lean_MessageData_ofExpr(v_e_3594_);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_inlineExpr___lam__2(v_e_3602_, v_x_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3606_, lean_object* v_maxInlineLength_3607_){
_start:
{
lean_object* v___f_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; 
lean_inc_ref_n(v_e_3606_, 2);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3608_, 0, v_e_3606_);
lean_closure_set(v___f_3608_, 1, v_maxInlineLength_3607_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3609_, 0, v_e_3606_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3610_, 0, v_e_3606_);
v___x_3611_ = l_Lean_MessageData_lazy(v___f_3608_, v___f_3609_, v___f_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object* v_s_3612_, lean_object* v_inst_3613_, lean_object* v_R_3614_, lean_object* v_a_3615_, uint8_t v_b_3616_, lean_object* v_c_3617_){
_start:
{
uint8_t v___x_3618_; 
v___x_3618_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3612_, v_a_3615_, v_b_3616_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object* v_s_3619_, lean_object* v_inst_3620_, lean_object* v_R_3621_, lean_object* v_a_3622_, lean_object* v_b_3623_, lean_object* v_c_3624_){
_start:
{
uint8_t v_b_boxed_3625_; uint8_t v_res_3626_; lean_object* v_r_3627_; 
v_b_boxed_3625_ = lean_unbox(v_b_3623_);
v_res_3626_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(v_s_3619_, v_inst_3620_, v_R_3621_, v_a_3622_, v_b_boxed_3625_, v_c_3624_);
lean_dec_ref(v_s_3619_);
v_r_3627_ = lean_box(v_res_3626_);
return v_r_3627_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_3632_ = l_Lean_MessageData_ofFormat(v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_3633_, lean_object* v_maxInlineLength_3634_, lean_object* v_ctx_3635_){
_start:
{
lean_object* v_msg_3637_; lean_object* v___x_3638_; uint8_t v___y_3640_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v_msg_3637_ = l_Lean_MessageData_ofExpr(v_e_3633_);
lean_inc_ref(v_msg_3637_);
v___x_3638_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3635_, v_msg_3637_);
v___x_3646_ = lean_string_length(v___x_3638_);
v___x_3647_ = lean_nat_dec_lt(v_maxInlineLength_3634_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3648_ = lean_unsigned_to_nat(0u);
v___x_3649_ = lean_string_utf8_byte_size(v___x_3638_);
v___x_3650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3638_);
lean_ctor_set(v___x_3650_, 1, v___x_3648_);
lean_ctor_set(v___x_3650_, 2, v___x_3649_);
v___x_3651_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3650_);
lean_dec_ref(v___x_3650_);
v___y_3640_ = v___x_3651_;
goto v___jp_3639_;
}
else
{
lean_dec_ref(v___x_3638_);
v___y_3640_ = v___x_3647_;
goto v___jp_3639_;
}
v___jp_3639_:
{
if (v___y_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3641_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v_msg_3637_);
v___x_3643_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
return v___x_3644_;
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_indentD(v_msg_3637_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_3652_, lean_object* v_maxInlineLength_3653_, lean_object* v_ctx_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_inlineExprTrailing___lam__0(v_e_3652_, v_maxInlineLength_3653_, v_ctx_3654_);
lean_dec_ref(v_ctx_3654_);
lean_dec(v_maxInlineLength_3653_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_3657_, lean_object* v_x_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3660_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3661_ = l_Lean_MessageData_ofExpr(v_e_3657_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_3665_, lean_object* v_x_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_inlineExprTrailing___lam__2(v_e_3665_, v_x_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_3669_, lean_object* v_maxInlineLength_3670_){
_start:
{
lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___x_3674_; 
lean_inc_ref_n(v_e_3669_, 2);
v___f_3671_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3671_, 0, v_e_3669_);
lean_closure_set(v___f_3671_, 1, v_maxInlineLength_3670_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3672_, 0, v_e_3669_);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3673_, 0, v_e_3669_);
v___x_3674_ = l_Lean_MessageData_lazy(v___f_3671_, v___f_3672_, v___f_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_3679_ = l_Lean_MessageData_ofFormat(v___x_3678_);
return v___x_3679_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_3684_ = l_Lean_MessageData_ofFormat(v___x_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_3685_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3686_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v_msg_3685_);
v___x_3688_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_3690_, lean_object* v_inst_3691_, lean_object* v_msg_3692_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = lean_apply_1(v_inst_3690_, v_msg_3692_);
v___x_3694_ = lean_apply_2(v_inst_3691_, lean_box(0), v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_3695_, lean_object* v_inst_3696_){
_start:
{
lean_object* v___f_3697_; 
v___f_3697_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3697_, 0, v_inst_3696_);
lean_closure_set(v___f_3697_, 1, v_inst_3695_);
return v___f_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_3698_, lean_object* v_n_3699_, lean_object* v_inst_3700_, lean_object* v_inst_3701_){
_start:
{
lean_object* v___f_3702_; 
v___f_3702_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3702_, 0, v_inst_3701_);
lean_closure_set(v___f_3702_, 1, v_inst_3700_);
return v___f_3702_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_unsigned_to_nat(32u);
v___x_3704_ = lean_mk_empty_array_with_capacity(v___x_3703_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3706_ = ((size_t)5ULL);
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_unsigned_to_nat(32u);
v___x_3709_ = lean_mk_empty_array_with_capacity(v___x_3708_);
v___x_3710_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_3711_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
lean_ctor_set(v___x_3711_, 1, v___x_3709_);
lean_ctor_set(v___x_3711_, 2, v___x_3707_);
lean_ctor_set(v___x_3711_, 3, v___x_3707_);
lean_ctor_set_usize(v___x_3711_, 4, v___x_3706_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3712_ = lean_box(1);
v___x_3713_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_3714_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_3715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___x_3713_);
lean_ctor_set(v___x_3715_, 2, v___x_3712_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_3716_, lean_object* v_msgData_3717_, lean_object* v_toPure_3718_, lean_object* v_opts_3719_){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3720_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_3721_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_3722_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3722_, 0, v_env_3716_);
lean_ctor_set(v___x_3722_, 1, v___x_3720_);
lean_ctor_set(v___x_3722_, 2, v___x_3721_);
lean_ctor_set(v___x_3722_, 3, v_opts_3719_);
v___x_3723_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v_msgData_3717_);
v___x_3724_ = lean_apply_2(v_toPure_3718_, lean_box(0), v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_3725_, lean_object* v_toPure_3726_, lean_object* v_toBind_3727_, lean_object* v_inst_3728_, lean_object* v_env_3729_){
_start:
{
lean_object* v___f_3730_; lean_object* v___x_3731_; 
v___f_3730_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3730_, 0, v_env_3729_);
lean_closure_set(v___f_3730_, 1, v_msgData_3725_);
lean_closure_set(v___f_3730_, 2, v_toPure_3726_);
v___x_3731_ = lean_apply_4(v_toBind_3727_, lean_box(0), lean_box(0), v_inst_3728_, v___f_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_3732_, lean_object* v_inst_3733_, lean_object* v_inst_3734_, lean_object* v_msgData_3735_){
_start:
{
lean_object* v_toApplicative_3736_; lean_object* v_toBind_3737_; lean_object* v_getEnv_3738_; lean_object* v_toPure_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; 
v_toApplicative_3736_ = lean_ctor_get(v_inst_3732_, 0);
lean_inc_ref(v_toApplicative_3736_);
v_toBind_3737_ = lean_ctor_get(v_inst_3732_, 1);
lean_inc_n(v_toBind_3737_, 2);
lean_dec_ref(v_inst_3732_);
v_getEnv_3738_ = lean_ctor_get(v_inst_3733_, 0);
lean_inc(v_getEnv_3738_);
lean_dec_ref(v_inst_3733_);
v_toPure_3739_ = lean_ctor_get(v_toApplicative_3736_, 1);
lean_inc(v_toPure_3739_);
lean_dec_ref(v_toApplicative_3736_);
v___f_3740_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3740_, 0, v_msgData_3735_);
lean_closure_set(v___f_3740_, 1, v_toPure_3739_);
lean_closure_set(v___f_3740_, 2, v_toBind_3737_);
lean_closure_set(v___f_3740_, 3, v_inst_3734_);
v___x_3741_ = lean_apply_4(v_toBind_3737_, lean_box(0), lean_box(0), v_getEnv_3738_, v___f_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_3742_, lean_object* v_inst_3743_, lean_object* v_inst_3744_, lean_object* v_inst_3745_, lean_object* v_msgData_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_addMessageContextPartial___redArg(v_inst_3743_, v_inst_3744_, v_inst_3745_, v_msgData_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_3748_, lean_object* v_mctx_3749_, lean_object* v_lctx_3750_, lean_object* v_msgData_3751_, lean_object* v_toPure_3752_, lean_object* v_opts_3753_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3754_, 0, v_env_3748_);
lean_ctor_set(v___x_3754_, 1, v_mctx_3749_);
lean_ctor_set(v___x_3754_, 2, v_lctx_3750_);
lean_ctor_set(v___x_3754_, 3, v_opts_3753_);
v___x_3755_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
lean_ctor_set(v___x_3755_, 1, v_msgData_3751_);
v___x_3756_ = lean_apply_2(v_toPure_3752_, lean_box(0), v___x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_3757_, lean_object* v_mctx_3758_, lean_object* v_msgData_3759_, lean_object* v_toPure_3760_, lean_object* v_toBind_3761_, lean_object* v_inst_3762_, lean_object* v_lctx_3763_){
_start:
{
lean_object* v___f_3764_; lean_object* v___x_3765_; 
v___f_3764_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3764_, 0, v_env_3757_);
lean_closure_set(v___f_3764_, 1, v_mctx_3758_);
lean_closure_set(v___f_3764_, 2, v_lctx_3763_);
lean_closure_set(v___f_3764_, 3, v_msgData_3759_);
lean_closure_set(v___f_3764_, 4, v_toPure_3760_);
v___x_3765_ = lean_apply_4(v_toBind_3761_, lean_box(0), lean_box(0), v_inst_3762_, v___f_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_3766_, lean_object* v_msgData_3767_, lean_object* v_toPure_3768_, lean_object* v_toBind_3769_, lean_object* v_inst_3770_, lean_object* v_inst_3771_, lean_object* v_mctx_3772_){
_start:
{
lean_object* v___f_3773_; lean_object* v___x_3774_; 
lean_inc(v_toBind_3769_);
v___f_3773_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3773_, 0, v_env_3766_);
lean_closure_set(v___f_3773_, 1, v_mctx_3772_);
lean_closure_set(v___f_3773_, 2, v_msgData_3767_);
lean_closure_set(v___f_3773_, 3, v_toPure_3768_);
lean_closure_set(v___f_3773_, 4, v_toBind_3769_);
lean_closure_set(v___f_3773_, 5, v_inst_3770_);
v___x_3774_ = lean_apply_4(v_toBind_3769_, lean_box(0), lean_box(0), v_inst_3771_, v___f_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_3775_, lean_object* v_msgData_3776_, lean_object* v_toPure_3777_, lean_object* v_toBind_3778_, lean_object* v_inst_3779_, lean_object* v_inst_3780_, lean_object* v_env_3781_){
_start:
{
lean_object* v_getMCtx_3782_; lean_object* v___f_3783_; lean_object* v___x_3784_; 
v_getMCtx_3782_ = lean_ctor_get(v_inst_3775_, 0);
lean_inc(v_getMCtx_3782_);
lean_dec_ref(v_inst_3775_);
lean_inc(v_toBind_3778_);
v___f_3783_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3783_, 0, v_env_3781_);
lean_closure_set(v___f_3783_, 1, v_msgData_3776_);
lean_closure_set(v___f_3783_, 2, v_toPure_3777_);
lean_closure_set(v___f_3783_, 3, v_toBind_3778_);
lean_closure_set(v___f_3783_, 4, v_inst_3779_);
lean_closure_set(v___f_3783_, 5, v_inst_3780_);
v___x_3784_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v_getMCtx_3782_, v___f_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_inst_3787_, lean_object* v_inst_3788_, lean_object* v_inst_3789_, lean_object* v_msgData_3790_){
_start:
{
lean_object* v_toApplicative_3791_; lean_object* v_toBind_3792_; lean_object* v_getEnv_3793_; lean_object* v_toPure_3794_; lean_object* v___f_3795_; lean_object* v___x_3796_; 
v_toApplicative_3791_ = lean_ctor_get(v_inst_3785_, 0);
lean_inc_ref(v_toApplicative_3791_);
v_toBind_3792_ = lean_ctor_get(v_inst_3785_, 1);
lean_inc_n(v_toBind_3792_, 2);
lean_dec_ref(v_inst_3785_);
v_getEnv_3793_ = lean_ctor_get(v_inst_3786_, 0);
lean_inc(v_getEnv_3793_);
lean_dec_ref(v_inst_3786_);
v_toPure_3794_ = lean_ctor_get(v_toApplicative_3791_, 1);
lean_inc(v_toPure_3794_);
lean_dec_ref(v_toApplicative_3791_);
v___f_3795_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_3795_, 0, v_inst_3787_);
lean_closure_set(v___f_3795_, 1, v_msgData_3790_);
lean_closure_set(v___f_3795_, 2, v_toPure_3794_);
lean_closure_set(v___f_3795_, 3, v_toBind_3792_);
lean_closure_set(v___f_3795_, 4, v_inst_3789_);
lean_closure_set(v___f_3795_, 5, v_inst_3788_);
v___x_3796_ = lean_apply_4(v_toBind_3792_, lean_box(0), lean_box(0), v_getEnv_3793_, v___f_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_3797_, lean_object* v_inst_3798_, lean_object* v_inst_3799_, lean_object* v_inst_3800_, lean_object* v_inst_3801_, lean_object* v_inst_3802_, lean_object* v_msgData_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_addMessageContextFull___redArg(v_inst_3798_, v_inst_3799_, v_inst_3800_, v_inst_3801_, v_inst_3802_, v_msgData_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_3809_);
lean_dec_ref(v_s_3809_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_3811_, lean_object* v___x_3812_, lean_object* v___x_3813_, lean_object* v_a_3814_, lean_object* v_b_3815_){
_start:
{
lean_object* v_it_3817_; lean_object* v_startInclusive_3818_; lean_object* v_endExclusive_3819_; 
if (lean_obj_tag(v_a_3814_) == 0)
{
lean_object* v_currPos_3825_; lean_object* v_searcher_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3852_; 
v_currPos_3825_ = lean_ctor_get(v_a_3814_, 0);
v_searcher_3826_ = lean_ctor_get(v_a_3814_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3814_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3828_ = v_a_3814_;
v_isShared_3829_ = v_isSharedCheck_3852_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_searcher_3826_);
lean_inc(v_currPos_3825_);
lean_dec(v_a_3814_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3852_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v_startInclusive_3830_; lean_object* v_endExclusive_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_startInclusive_3830_ = lean_ctor_get(v___x_3812_, 1);
v_endExclusive_3831_ = lean_ctor_get(v___x_3812_, 2);
v___x_3832_ = lean_nat_sub(v_endExclusive_3831_, v_startInclusive_3830_);
v___x_3833_ = lean_nat_dec_eq(v_searcher_3826_, v___x_3832_);
lean_dec(v___x_3832_);
if (v___x_3833_ == 0)
{
uint32_t v___x_3834_; uint32_t v___x_3835_; uint8_t v___x_3836_; 
v___x_3834_ = 10;
v___x_3835_ = lean_string_utf8_get_fast(v_str_3811_, v_searcher_3826_);
v___x_3836_ = lean_uint32_dec_eq(v___x_3835_, v___x_3834_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = lean_string_utf8_next_fast(v_str_3811_, v_searcher_3826_);
lean_dec(v_searcher_3826_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v___x_3837_);
v___x_3839_ = v___x_3828_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_currPos_3825_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
v_a_3814_ = v___x_3839_;
goto _start;
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v_slice_3845_; lean_object* v_nextIt_3847_; 
v___x_3842_ = lean_string_utf8_next_fast(v_str_3811_, v_searcher_3826_);
v___x_3843_ = lean_nat_sub(v___x_3842_, v_searcher_3826_);
v___x_3844_ = lean_nat_add(v_searcher_3826_, v___x_3843_);
lean_dec(v___x_3843_);
v_slice_3845_ = l_String_Slice_subslice_x21(v___x_3812_, v_currPos_3825_, v_searcher_3826_);
lean_inc(v___x_3844_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v___x_3844_);
lean_ctor_set(v___x_3828_, 0, v___x_3844_);
v_nextIt_3847_ = v___x_3828_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3844_);
v_nextIt_3847_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v_startInclusive_3848_; lean_object* v_endExclusive_3849_; 
v_startInclusive_3848_ = lean_ctor_get(v_slice_3845_, 0);
lean_inc(v_startInclusive_3848_);
v_endExclusive_3849_ = lean_ctor_get(v_slice_3845_, 1);
lean_inc(v_endExclusive_3849_);
lean_dec_ref(v_slice_3845_);
v_it_3817_ = v_nextIt_3847_;
v_startInclusive_3818_ = v_startInclusive_3848_;
v_endExclusive_3819_ = v_endExclusive_3849_;
goto v___jp_3816_;
}
}
}
else
{
lean_object* v___x_3851_; 
lean_del_object(v___x_3828_);
lean_dec(v_searcher_3826_);
v___x_3851_ = lean_box(1);
lean_inc(v___x_3813_);
v_it_3817_ = v___x_3851_;
v_startInclusive_3818_ = v_currPos_3825_;
v_endExclusive_3819_ = v___x_3813_;
goto v___jp_3816_;
}
}
}
else
{
lean_dec(v___x_3813_);
return v_b_3815_;
}
v___jp_3816_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3820_ = lean_string_utf8_extract(v_str_3811_, v_startInclusive_3818_, v_endExclusive_3819_);
lean_dec(v_endExclusive_3819_);
lean_dec(v_startInclusive_3818_);
v___x_3821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
v___x_3822_ = l_Lean_MessageData_ofFormat(v___x_3821_);
v___x_3823_ = lean_array_push(v_b_3815_, v___x_3822_);
v_a_3814_ = v_it_3817_;
v_b_3815_ = v___x_3823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_3853_, lean_object* v___x_3854_, lean_object* v___x_3855_, lean_object* v_a_3856_, lean_object* v_b_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3853_, v___x_3854_, v___x_3855_, v_a_3856_, v_b_3857_);
lean_dec_ref(v___x_3854_);
lean_dec_ref(v_str_3853_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_3861_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_lines_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3862_ = lean_unsigned_to_nat(0u);
v___x_3863_ = lean_string_utf8_byte_size(v_str_3861_);
lean_inc_ref(v_str_3861_);
v___x_3864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3864_, 0, v_str_3861_);
lean_ctor_set(v___x_3864_, 1, v___x_3862_);
lean_ctor_set(v___x_3864_, 2, v___x_3863_);
v_lines_3865_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_3864_);
v___x_3866_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_3867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3861_, v___x_3864_, v___x_3863_, v_lines_3865_, v___x_3866_);
lean_dec_ref(v___x_3864_);
lean_dec_ref(v_str_3861_);
v___x_3868_ = lean_array_to_list(v___x_3867_);
v___x_3869_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3870_ = l_Lean_MessageData_joinSep(v___x_3868_, v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_3871_, lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v_inst_3874_, lean_object* v_R_3875_, lean_object* v_a_3876_, lean_object* v_b_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3871_, v___x_3872_, v___x_3873_, v_a_3876_, v_b_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_3879_, lean_object* v___x_3880_, lean_object* v___x_3881_, lean_object* v_inst_3882_, lean_object* v_R_3883_, lean_object* v_a_3884_, lean_object* v_b_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_3879_, v___x_3880_, v___x_3881_, v_inst_3882_, v_R_3883_, v_a_3884_, v_b_3885_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v_str_3879_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_3887_){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_3889_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_3889_, 0, lean_box(0));
lean_closure_set(v___x_3889_, 1, lean_box(0));
lean_closure_set(v___x_3889_, 2, lean_box(0));
lean_closure_set(v___x_3889_, 3, v___x_3888_);
lean_closure_set(v___x_3889_, 4, v_inst_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_3890_, lean_object* v_inst_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_3899_){
_start:
{
lean_object* v___f_3900_; 
v___f_3900_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_instToMessageDataTSyntax(v_k_3901_);
lean_dec(v_k_3901_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_3907_, lean_object* v_as_3908_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = lean_box(0);
v___x_3910_ = l_List_mapTR_loop___redArg(v_inst_3907_, v_as_3908_, v___x_3909_);
v___x_3911_ = l_Lean_MessageData_ofList(v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_3912_){
_start:
{
lean_object* v___f_3913_; 
v___f_3913_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3913_, 0, v_inst_3912_);
return v___f_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_3914_, lean_object* v_inst_3915_){
_start:
{
lean_object* v___f_3916_; 
v___f_3916_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3916_, 0, v_inst_3915_);
return v___f_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_3917_, lean_object* v_as_3918_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3919_ = lean_array_to_list(v_as_3918_);
v___x_3920_ = lean_box(0);
v___x_3921_ = l_List_mapTR_loop___redArg(v_inst_3917_, v___x_3919_, v___x_3920_);
v___x_3922_ = l_Lean_MessageData_ofList(v___x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_3923_){
_start:
{
lean_object* v___f_3924_; 
v___f_3924_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3924_, 0, v_inst_3923_);
return v___f_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_3925_, lean_object* v_inst_3926_){
_start:
{
lean_object* v___f_3927_; 
v___f_3927_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3927_, 0, v_inst_3926_);
return v___f_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_3928_, lean_object* v_acc_3929_, lean_object* v_recur_3930_){
_start:
{
lean_object* v_array_3931_; lean_object* v_start_3932_; lean_object* v_stop_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3946_; 
v_array_3931_ = lean_ctor_get(v_it_3928_, 0);
v_start_3932_ = lean_ctor_get(v_it_3928_, 1);
v_stop_3933_ = lean_ctor_get(v_it_3928_, 2);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_it_3928_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3935_ = v_it_3928_;
v_isShared_3936_ = v_isSharedCheck_3946_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_stop_3933_);
lean_inc(v_start_3932_);
lean_inc(v_array_3931_);
lean_dec(v_it_3928_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3946_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_lt(v_start_3932_, v_stop_3933_);
if (v___x_3937_ == 0)
{
lean_del_object(v___x_3935_);
lean_dec(v_stop_3933_);
lean_dec(v_start_3932_);
lean_dec_ref(v_array_3931_);
lean_dec_ref(v_recur_3930_);
return v_acc_3929_;
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = lean_nat_add(v_start_3932_, v___x_3938_);
lean_inc_ref(v_array_3931_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 1, v___x_3939_);
v___x_3941_ = v___x_3935_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_array_3931_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3945_, 2, v_stop_3933_);
v___x_3941_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_array_fget(v_array_3931_, v_start_3932_);
lean_dec(v_start_3932_);
lean_dec_ref(v_array_3931_);
v___x_3943_ = lean_array_push(v_acc_3929_, v___x_3942_);
v___x_3944_ = lean_apply_3(v_recur_3930_, v___x_3941_, v___x_3943_, lean_box(0));
return v___x_3944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_3949_, lean_object* v_inst_3950_, lean_object* v_as_3951_){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3952_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_3953_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_3949_, v_as_3951_, v___x_3952_);
v___x_3954_ = lean_array_to_list(v___x_3953_);
v___x_3955_ = lean_box(0);
v___x_3956_ = l_List_mapTR_loop___redArg(v_inst_3950_, v___x_3954_, v___x_3955_);
v___x_3957_ = l_Lean_MessageData_ofList(v___x_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_3959_){
_start:
{
lean_object* v___f_3960_; lean_object* v___f_3961_; 
v___f_3960_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_3961_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3961_, 0, v___f_3960_);
lean_closure_set(v___f_3961_, 1, v_inst_3959_);
return v___f_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_3962_, lean_object* v_inst_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_3963_);
return v___x_3964_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_3969_ = l_Lean_MessageData_ofFormat(v___x_3968_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_3973_ = l_Lean_MessageData_ofFormat(v___x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_3974_, lean_object* v_x_3975_){
_start:
{
if (lean_obj_tag(v_x_3975_) == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref(v_inst_3974_);
v___x_3976_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_3976_;
}
else
{
lean_object* v_val_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_val_3977_ = lean_ctor_get(v_x_3975_, 0);
lean_inc(v_val_3977_);
lean_dec_ref(v_x_3975_);
v___x_3978_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_3979_ = lean_apply_1(v_inst_3974_, v_val_3977_);
v___x_3980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_3983_){
_start:
{
lean_object* v___f_3984_; 
v___f_3984_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3984_, 0, v_inst_3983_);
return v___f_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_3985_, lean_object* v_inst_3986_){
_start:
{
lean_object* v___f_3987_; 
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3987_, 0, v_inst_3986_);
return v___f_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_3988_, lean_object* v_inst_3989_, lean_object* v_x_3990_){
_start:
{
lean_object* v_fst_3991_; lean_object* v_snd_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4006_; 
v_fst_3991_ = lean_ctor_get(v_x_3990_, 0);
v_snd_3992_ = lean_ctor_get(v_x_3990_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_x_3990_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3994_ = v_x_3990_;
v_isShared_3995_ = v_isSharedCheck_4006_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_snd_3992_);
lean_inc(v_fst_3991_);
lean_dec(v_x_3990_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4006_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3996_ = lean_apply_1(v_inst_3988_, v_fst_3991_);
v___x_3997_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 7);
lean_ctor_set(v___x_3994_, 1, v___x_3997_);
lean_ctor_set(v___x_3994_, 0, v___x_3996_);
v___x_3999_ = v___x_3994_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4000_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = lean_apply_1(v_inst_3989_, v_snd_3992_);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l_Lean_MessageData_paren(v___x_4003_);
return v___x_4004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4007_, lean_object* v_inst_4008_){
_start:
{
lean_object* v___f_4009_; 
v___f_4009_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4009_, 0, v_inst_4007_);
lean_closure_set(v___f_4009_, 1, v_inst_4008_);
return v___f_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4010_, lean_object* v_00_u03b2_4011_, lean_object* v_inst_4012_, lean_object* v_inst_4013_){
_start:
{
lean_object* v___f_4014_; 
v___f_4014_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4014_, 0, v_inst_4012_);
lean_closure_set(v___f_4014_, 1, v_inst_4013_);
return v___f_4014_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4019_ = l_Lean_MessageData_ofFormat(v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4020_){
_start:
{
if (lean_obj_tag(v_x_4020_) == 0)
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4021_;
}
else
{
lean_object* v_val_4022_; lean_object* v___x_4023_; 
v_val_4022_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_val_4022_);
lean_dec_ref(v_x_4020_);
v___x_4023_ = l_Lean_MessageData_ofExpr(v_val_4022_);
return v___x_4023_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___x_4058_ = l_String_toRawSubstring_x27(v___x_4057_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4074_ = l_String_toRawSubstring_x27(v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4091_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4088_);
v___x_4092_ = l_Lean_Syntax_isOfKind(v_x_4088_, v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_dec(v_x_4088_);
v___x_4093_ = lean_box(1);
v___x_4094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v_a_4090_);
return v___x_4094_;
}
else
{
lean_object* v_quotContext_4095_; lean_object* v_currMacroScope_4096_; lean_object* v_ref_4097_; lean_object* v___x_4098_; lean_object* v_interpStr_4099_; uint8_t v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_quotContext_4095_ = lean_ctor_get(v_a_4089_, 1);
v_currMacroScope_4096_ = lean_ctor_get(v_a_4089_, 2);
v_ref_4097_ = lean_ctor_get(v_a_4089_, 5);
v___x_4098_ = lean_unsigned_to_nat(1u);
v_interpStr_4099_ = l_Lean_Syntax_getArg(v_x_4088_, v___x_4098_);
lean_dec(v_x_4088_);
v___x_4100_ = 0;
v___x_4101_ = l_Lean_SourceInfo_fromRef(v_ref_4097_, v___x_4100_);
v___x_4102_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4103_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4096_, 2);
lean_inc_n(v_quotContext_4095_, 2);
v___x_4104_ = l_Lean_addMacroScope(v_quotContext_4095_, v___x_4103_, v_currMacroScope_4096_);
v___x_4105_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4101_);
v___x_4106_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4101_);
lean_ctor_set(v___x_4106_, 1, v___x_4102_);
lean_ctor_set(v___x_4106_, 2, v___x_4104_);
lean_ctor_set(v___x_4106_, 3, v___x_4105_);
v___x_4107_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4108_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4109_ = l_Lean_addMacroScope(v_quotContext_4095_, v___x_4108_, v_currMacroScope_4096_);
v___x_4110_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4111_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4101_);
lean_ctor_set(v___x_4111_, 1, v___x_4107_);
lean_ctor_set(v___x_4111_, 2, v___x_4109_);
lean_ctor_set(v___x_4111_, 3, v___x_4110_);
lean_inc_ref(v___x_4111_);
v___x_4112_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4099_, v___x_4106_, v___x_4111_, v___x_4111_, v_a_4089_, v_a_4090_);
lean_dec(v_interpStr_4099_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_a_4114_ = lean_ctor_get(v___x_4112_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4112_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4113_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
v_a_4122_ = lean_ctor_get(v___x_4112_, 0);
v_a_4123_ = lean_ctor_get(v___x_4112_, 1);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4112_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_inc(v_a_4122_);
lean_dec(v___x_4112_);
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
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4122_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_a_4123_);
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
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4131_, v_a_4132_, v_a_4133_);
lean_dec_ref(v_a_4132_);
return v_res_4134_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4138_){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4139_ = lean_array_to_list(v_msgs_4138_);
v___x_4140_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4141_ = l_Lean_MessageData_joinSep(v___x_4139_, v___x_4140_);
v___x_4142_ = l_Lean_indentD(v___x_4141_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4143_, lean_object* v_lctx_4144_, lean_object* v_opts_4145_, lean_object* v_msg_4146_){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4147_ = lean_elab_environment_of_kernel_env(v_env_4143_);
v___x_4148_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
lean_ctor_set(v___x_4149_, 2, v_lctx_4144_);
lean_ctor_set(v___x_4149_, 3, v_opts_4145_);
v___x_4150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v_msg_4146_);
return v___x_4150_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4153_ = l_Lean_stringToMessageData(v___x_4152_);
return v___x_4153_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4156_ = l_Lean_stringToMessageData(v___x_4155_);
return v___x_4156_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4159_ = l_Lean_stringToMessageData(v___x_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4160_, lean_object* v_n_4161_, lean_object* v_expectedType_4162_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4163_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4164_ = l_Lean_MessageData_ofName(v_n_4161_);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_indentExpr(v_givenType_4160_);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4167_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l_Lean_indentExpr(v_expectedType_4162_);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4171_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
return v___x_4173_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4174_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4177_ = lean_box(1);
v___x_4178_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4179_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4178_);
lean_ctor_set(v___x_4180_, 2, v___x_4177_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4183_ = l_Lean_stringToMessageData(v___x_4182_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4185_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4186_ = l_Lean_stringToMessageData(v___x_4185_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4189_ = l_Lean_stringToMessageData(v___x_4188_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4194_ = l_Lean_MessageData_ofFormat(v___x_4193_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4197_ = l_Lean_stringToMessageData(v___x_4196_);
return v___x_4197_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4200_ = l_Lean_stringToMessageData(v___x_4199_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4206_ = l_Lean_stringToMessageData(v___x_4205_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4209_ = l_Lean_stringToMessageData(v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4212_ = l_Lean_stringToMessageData(v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4215_ = l_Lean_stringToMessageData(v___x_4214_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4218_ = l_Lean_stringToMessageData(v___x_4217_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4221_ = l_Lean_stringToMessageData(v___x_4220_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4224_ = l_Lean_stringToMessageData(v___x_4223_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4233_ = l_Lean_stringToMessageData(v___x_4232_);
return v___x_4233_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4236_ = l_Lean_stringToMessageData(v___x_4235_);
return v___x_4236_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4241_ = l_Lean_MessageData_ofFormat(v___x_4240_);
return v___x_4241_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4246_ = l_Lean_MessageData_ofFormat(v___x_4245_);
return v___x_4246_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4251_ = l_Lean_MessageData_ofFormat(v___x_4250_);
return v___x_4251_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4256_ = l_Lean_MessageData_ofFormat(v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4257_, lean_object* v_opts_4258_){
_start:
{
switch(lean_obj_tag(v_e_4257_))
{
case 0:
{
lean_object* v_env_4259_; lean_object* v_name_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4273_; 
v_env_4259_ = lean_ctor_get(v_e_4257_, 0);
v_name_4260_ = lean_ctor_get(v_e_4257_, 1);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_e_4257_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4262_ = v_e_4257_;
v_isShared_4263_ = v_isSharedCheck_4273_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_name_4260_);
lean_inc(v_env_4259_);
lean_dec(v_e_4257_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4273_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4264_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4265_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4266_ = l_Lean_MessageData_ofName(v_name_4260_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 7);
lean_ctor_set(v___x_4262_, 1, v___x_4266_);
lean_ctor_set(v___x_4262_, 0, v___x_4265_);
v___x_4268_ = v___x_4262_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4272_, 1, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4268_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4259_, v___x_4264_, v_opts_4258_, v___x_4270_);
return v___x_4271_;
}
}
}
case 1:
{
lean_object* v_env_4274_; lean_object* v_name_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4289_; 
v_env_4274_ = lean_ctor_get(v_e_4257_, 0);
v_name_4275_ = lean_ctor_get(v_e_4257_, 1);
v_isSharedCheck_4289_ = !lean_is_exclusive(v_e_4257_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4277_ = v_e_4257_;
v_isShared_4278_ = v_isSharedCheck_4289_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_name_4275_);
lean_inc(v_env_4274_);
lean_dec(v_e_4257_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4289_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4279_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4280_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4281_ = 1;
v___x_4282_ = l_Lean_MessageData_ofConstName(v_name_4275_, v___x_4281_);
if (v_isShared_4278_ == 0)
{
lean_ctor_set_tag(v___x_4277_, 7);
lean_ctor_set(v___x_4277_, 1, v___x_4282_);
lean_ctor_set(v___x_4277_, 0, v___x_4280_);
v___x_4284_ = v___x_4277_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4280_);
lean_ctor_set(v_reuseFailAlloc_4288_, 1, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4274_, v___x_4279_, v_opts_4258_, v___x_4286_);
return v___x_4287_;
}
}
}
case 2:
{
lean_object* v_env_4290_; lean_object* v_decl_4291_; lean_object* v_givenType_4292_; lean_object* v___x_4293_; 
v_env_4290_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4290_);
v_decl_4291_ = lean_ctor_get(v_e_4257_, 1);
lean_inc(v_decl_4291_);
v_givenType_4292_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_givenType_4292_);
lean_dec_ref(v_e_4257_);
v___x_4293_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4291_))
{
case 1:
{
lean_object* v_val_4294_; lean_object* v_toConstantVal_4295_; lean_object* v_name_4296_; lean_object* v_type_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_val_4294_ = lean_ctor_get(v_decl_4291_, 0);
lean_inc_ref(v_val_4294_);
lean_dec_ref(v_decl_4291_);
v_toConstantVal_4295_ = lean_ctor_get(v_val_4294_, 0);
lean_inc_ref(v_toConstantVal_4295_);
lean_dec_ref(v_val_4294_);
v_name_4296_ = lean_ctor_get(v_toConstantVal_4295_, 0);
lean_inc(v_name_4296_);
v_type_4297_ = lean_ctor_get(v_toConstantVal_4295_, 2);
lean_inc_ref(v_type_4297_);
lean_dec_ref(v_toConstantVal_4295_);
v___x_4298_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4292_, v_name_4296_, v_type_4297_);
v___x_4299_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4290_, v___x_4293_, v_opts_4258_, v___x_4298_);
return v___x_4299_;
}
case 2:
{
lean_object* v_val_4300_; lean_object* v_toConstantVal_4301_; lean_object* v_name_4302_; lean_object* v_type_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_val_4300_ = lean_ctor_get(v_decl_4291_, 0);
lean_inc_ref(v_val_4300_);
lean_dec_ref(v_decl_4291_);
v_toConstantVal_4301_ = lean_ctor_get(v_val_4300_, 0);
lean_inc_ref(v_toConstantVal_4301_);
lean_dec_ref(v_val_4300_);
v_name_4302_ = lean_ctor_get(v_toConstantVal_4301_, 0);
lean_inc(v_name_4302_);
v_type_4303_ = lean_ctor_get(v_toConstantVal_4301_, 2);
lean_inc_ref(v_type_4303_);
lean_dec_ref(v_toConstantVal_4301_);
v___x_4304_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4292_, v_name_4302_, v_type_4303_);
v___x_4305_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4290_, v___x_4293_, v_opts_4258_, v___x_4304_);
return v___x_4305_;
}
default: 
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_dec_ref(v_givenType_4292_);
lean_dec(v_decl_4291_);
v___x_4306_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4307_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4290_, v___x_4293_, v_opts_4258_, v___x_4306_);
return v___x_4307_;
}
}
}
case 3:
{
lean_object* v_env_4308_; lean_object* v_name_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_env_4308_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4308_);
v_name_4309_ = lean_ctor_get(v_e_4257_, 1);
lean_inc(v_name_4309_);
lean_dec_ref(v_e_4257_);
v___x_4310_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4311_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4312_ = 1;
v___x_4313_ = l_Lean_MessageData_ofConstName(v_name_4309_, v___x_4312_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4311_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4308_, v___x_4310_, v_opts_4258_, v___x_4316_);
return v___x_4317_;
}
case 4:
{
lean_object* v_env_4318_; lean_object* v_name_4319_; lean_object* v_expr_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_env_4318_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4318_);
v_name_4319_ = lean_ctor_get(v_e_4257_, 1);
lean_inc(v_name_4319_);
v_expr_4320_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_expr_4320_);
lean_dec_ref(v_e_4257_);
v___x_4321_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4322_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4323_ = 1;
v___x_4324_ = l_Lean_MessageData_ofConstName(v_name_4319_, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4322_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = l_Lean_indentExpr(v_expr_4320_);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4318_, v___x_4321_, v_opts_4258_, v___x_4329_);
return v___x_4330_;
}
case 5:
{
lean_object* v_env_4331_; lean_object* v_lctx_4332_; lean_object* v_expr_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_env_4331_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4331_);
v_lctx_4332_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4332_);
v_expr_4333_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_expr_4333_);
lean_dec_ref(v_e_4257_);
v___x_4334_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4335_ = l_Lean_indentExpr(v_expr_4333_);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4331_, v_lctx_4332_, v_opts_4258_, v___x_4336_);
return v___x_4337_;
}
case 6:
{
lean_object* v_env_4338_; lean_object* v_lctx_4339_; lean_object* v_expr_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_env_4338_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4338_);
v_lctx_4339_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4339_);
v_expr_4340_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_expr_4340_);
lean_dec_ref(v_e_4257_);
v___x_4341_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4342_ = l_Lean_indentExpr(v_expr_4340_);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4338_, v_lctx_4339_, v_opts_4258_, v___x_4343_);
return v___x_4344_;
}
case 7:
{
lean_object* v_env_4345_; lean_object* v_lctx_4346_; lean_object* v_name_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v_env_4345_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4345_);
v_lctx_4346_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4346_);
v_name_4347_ = lean_ctor_get(v_e_4257_, 2);
lean_inc(v_name_4347_);
lean_dec_ref(v_e_4257_);
v___x_4348_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4349_ = l_Lean_MessageData_ofName(v_name_4347_);
v___x_4350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4348_);
lean_ctor_set(v___x_4350_, 1, v___x_4349_);
v___x_4351_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4350_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
v___x_4353_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4345_, v_lctx_4346_, v_opts_4258_, v___x_4352_);
return v___x_4353_;
}
case 8:
{
lean_object* v_env_4354_; lean_object* v_lctx_4355_; lean_object* v_expr_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_env_4354_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4354_);
v_lctx_4355_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4355_);
v_expr_4356_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_expr_4356_);
lean_dec_ref(v_e_4257_);
v___x_4357_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4358_ = l_Lean_indentExpr(v_expr_4356_);
v___x_4359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4357_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4354_, v_lctx_4355_, v_opts_4258_, v___x_4359_);
return v___x_4360_;
}
case 9:
{
lean_object* v_env_4361_; lean_object* v_lctx_4362_; lean_object* v_app_4363_; lean_object* v_funType_4364_; lean_object* v_argType_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_env_4361_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4361_);
v_lctx_4362_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4362_);
v_app_4363_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_app_4363_);
v_funType_4364_ = lean_ctor_get(v_e_4257_, 3);
lean_inc_ref(v_funType_4364_);
v_argType_4365_ = lean_ctor_get(v_e_4257_, 4);
lean_inc_ref(v_argType_4365_);
lean_dec_ref(v_e_4257_);
v___x_4366_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4367_ = l_Lean_indentExpr(v_app_4363_);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = l_Lean_indentExpr(v_argType_4365_);
v___x_4372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = l_Lean_indentExpr(v_funType_4364_);
v___x_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4361_, v_lctx_4362_, v_opts_4258_, v___x_4376_);
return v___x_4377_;
}
case 10:
{
lean_object* v_env_4378_; lean_object* v_lctx_4379_; lean_object* v_proj_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_env_4378_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4378_);
v_lctx_4379_ = lean_ctor_get(v_e_4257_, 1);
lean_inc_ref(v_lctx_4379_);
v_proj_4380_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_proj_4380_);
lean_dec_ref(v_e_4257_);
v___x_4381_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4382_ = l_Lean_indentExpr(v_proj_4380_);
v___x_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4378_, v_lctx_4379_, v_opts_4258_, v___x_4383_);
return v___x_4384_;
}
case 11:
{
lean_object* v_env_4385_; lean_object* v_name_4386_; lean_object* v_type_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v_env_4385_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_env_4385_);
v_name_4386_ = lean_ctor_get(v_e_4257_, 1);
lean_inc(v_name_4386_);
v_type_4387_ = lean_ctor_get(v_e_4257_, 2);
lean_inc_ref(v_type_4387_);
lean_dec_ref(v_e_4257_);
v___x_4388_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4389_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4390_ = 1;
v___x_4391_ = l_Lean_MessageData_ofConstName(v_name_4386_, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4389_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4392_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = l_Lean_indentExpr(v_type_4387_);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4385_, v___x_4388_, v_opts_4258_, v___x_4396_);
return v___x_4397_;
}
case 12:
{
lean_object* v_msg_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_dec_ref(v_opts_4258_);
v_msg_4398_ = lean_ctor_get(v_e_4257_, 0);
lean_inc_ref(v_msg_4398_);
lean_dec_ref(v_e_4257_);
v___x_4399_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4400_ = l_Lean_stringToMessageData(v_msg_4398_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
return v___x_4401_;
}
case 13:
{
lean_object* v___x_4402_; 
lean_dec_ref(v_opts_4258_);
v___x_4402_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4402_;
}
case 14:
{
lean_object* v___x_4403_; 
lean_dec_ref(v_opts_4258_);
v___x_4403_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4403_;
}
case 15:
{
lean_object* v___x_4404_; 
lean_dec_ref(v_opts_4258_);
v___x_4404_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4404_;
}
default: 
{
lean_object* v___x_4405_; 
lean_dec_ref(v_opts_4258_);
v___x_4405_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4406_, lean_object* v_e_4407_, lean_object* v_cls_4408_){
_start:
{
lean_object* v___x_4409_; double v___x_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4411_ = 1;
v___x_4412_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4413_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4413_, 0, v_cls_4408_);
lean_ctor_set(v___x_4413_, 1, v___x_4409_);
lean_ctor_set(v___x_4413_, 2, v___x_4412_);
lean_ctor_set_float(v___x_4413_, sizeof(void*)*3, v___x_4410_);
lean_ctor_set_float(v___x_4413_, sizeof(void*)*3 + 8, v___x_4410_);
lean_ctor_set_uint8(v___x_4413_, sizeof(void*)*3 + 16, v___x_4411_);
v___x_4414_ = lean_apply_1(v_inst_4406_, v_e_4407_);
v___x_4415_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4416_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4413_);
lean_ctor_set(v___x_4416_, 1, v___x_4414_);
lean_ctor_set(v___x_4416_, 2, v___x_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4417_, lean_object* v_inst_4418_, lean_object* v_e_4419_, lean_object* v_cls_4420_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_toTraceElem___redArg(v_inst_4418_, v_e_4419_, v_cls_4420_);
return v___x_4421_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Message(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Lean_instInhabitedMessageSeverity_default = _init_l_Lean_instInhabitedMessageSeverity_default();
l_Lean_instInhabitedMessageSeverity = _init_l_Lean_instInhabitedMessageSeverity();
l_Lean_instInhabitedTraceResult_default = _init_l_Lean_instInhabitedTraceResult_default();
l_Lean_instInhabitedTraceResult = _init_l_Lean_instInhabitedTraceResult();
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
res = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
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
