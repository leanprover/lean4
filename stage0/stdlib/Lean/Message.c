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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_endPos_10_, 1);
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
lean_inc_ref(v___y_41_);
v___x_43_ = lean_string_append(v___y_41_, v___y_42_);
if (lean_obj_tag(v___y_40_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___x_43_;
v___y_33_ = v___y_39_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_40_, 1);
v___y_32_ = v___x_43_;
v___y_33_ = v___y_39_;
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
v___y_40_ = v___y_48_;
v___y_41_ = v___x_49_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___y_47_;
v___y_40_ = v___y_48_;
v___y_41_ = v___x_49_;
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
lean_dec_ref_known(v___x_205_, 1);
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
lean_dec_ref_known(v_t_378_, 1);
v___x_381_ = lean_apply_1(v_k_379_, v_a_380_);
return v___x_381_;
}
case 1:
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v_t_378_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v_t_378_, 1);
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
lean_dec_ref_known(v_t_378_, 2);
v___x_386_ = lean_apply_2(v_k_379_, v_a_384_, v_a_385_);
return v___x_386_;
}
case 6:
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v_t_378_, 0);
lean_inc_ref(v_a_387_);
lean_dec_ref_known(v_t_378_, 1);
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
lean_dec_ref_known(v_t_378_, 2);
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
lean_dec_ref_known(v_t_378_, 3);
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
lean_dec_ref_known(v_ctx_x3f_517_, 1);
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
lean_dec_ref_known(v_x_539_, 2);
v_x_539_ = v_a_540_;
goto _start;
}
case 4:
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_542_);
lean_dec_ref_known(v_x_539_, 2);
v_x_539_ = v_a_542_;
goto _start;
}
case 5:
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v_x_539_, 1);
lean_inc_ref(v_a_544_);
lean_dec_ref_known(v_x_539_, 2);
v_x_539_ = v_a_544_;
goto _start;
}
case 6:
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v_x_539_, 0);
lean_inc_ref(v_a_546_);
lean_dec_ref_known(v_x_539_, 1);
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
lean_dec_ref_known(v_x_539_, 2);
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
lean_dec_ref_known(v_x_539_, 2);
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
lean_dec_ref_known(v_x_539_, 3);
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
lean_dec_ref_known(v_ctx_x3f_672_, 1);
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
lean_dec_ref_known(v_ctx_x3f_707_, 1);
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
lean_dec_ref_known(v_ctx_x3f_736_, 1);
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
lean_dec_ref_known(v_ctx_x3f_799_, 1);
v___x_813_ = l_Lean_ppConstNameWithInfos(v_val_812_, v_constName_797_);
v___y_806_ = v___x_813_;
goto v___jp_805_;
}
else
{
lean_object* v_val_814_; lean_object* v_env_815_; lean_object* v_mctx_816_; lean_object* v_lctx_817_; lean_object* v_opts_818_; lean_object* v_currNamespace_819_; lean_object* v_openDecls_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
v_val_814_ = lean_ctor_get(v_ctx_x3f_799_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_ctx_x3f_799_, 1);
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
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_val_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_MessageData_withExprHover___lam__0(v_val_853_, v___y_854_);
lean_dec_ref(v___y_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_857_, lean_object* v_v_858_, lean_object* v_t_859_){
_start:
{
if (lean_obj_tag(v_t_859_) == 0)
{
lean_object* v_size_860_; lean_object* v_k_861_; lean_object* v_v_862_; lean_object* v_l_863_; lean_object* v_r_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_1145_; 
v_size_860_ = lean_ctor_get(v_t_859_, 0);
v_k_861_ = lean_ctor_get(v_t_859_, 1);
v_v_862_ = lean_ctor_get(v_t_859_, 2);
v_l_863_ = lean_ctor_get(v_t_859_, 3);
v_r_864_ = lean_ctor_get(v_t_859_, 4);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_t_859_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_866_ = v_t_859_;
v_isShared_867_ = v_isSharedCheck_1145_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_r_864_);
lean_inc(v_l_863_);
lean_inc(v_v_862_);
lean_inc(v_k_861_);
lean_inc(v_size_860_);
lean_dec(v_t_859_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_1145_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
v___x_868_ = lean_nat_dec_lt(v_k_857_, v_k_861_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = lean_nat_dec_eq(v_k_857_, v_k_861_);
if (v___x_869_ == 0)
{
lean_object* v_impl_870_; lean_object* v___x_871_; 
lean_dec(v_size_860_);
v_impl_870_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_857_, v_v_858_, v_r_864_);
v___x_871_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_863_) == 0)
{
lean_object* v_size_872_; lean_object* v_size_873_; lean_object* v_k_874_; lean_object* v_v_875_; lean_object* v_l_876_; lean_object* v_r_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_size_872_ = lean_ctor_get(v_l_863_, 0);
v_size_873_ = lean_ctor_get(v_impl_870_, 0);
lean_inc(v_size_873_);
v_k_874_ = lean_ctor_get(v_impl_870_, 1);
lean_inc(v_k_874_);
v_v_875_ = lean_ctor_get(v_impl_870_, 2);
lean_inc(v_v_875_);
v_l_876_ = lean_ctor_get(v_impl_870_, 3);
lean_inc(v_l_876_);
v_r_877_ = lean_ctor_get(v_impl_870_, 4);
lean_inc(v_r_877_);
v___x_878_ = lean_unsigned_to_nat(3u);
v___x_879_ = lean_nat_mul(v___x_878_, v_size_872_);
v___x_880_ = lean_nat_dec_lt(v___x_879_, v_size_873_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_r_877_);
lean_dec(v_l_876_);
lean_dec(v_v_875_);
lean_dec(v_k_874_);
v___x_881_ = lean_nat_add(v___x_871_, v_size_872_);
v___x_882_ = lean_nat_add(v___x_881_, v_size_873_);
lean_dec(v_size_873_);
lean_dec(v___x_881_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_impl_870_);
lean_ctor_set(v___x_866_, 0, v___x_882_);
v___x_884_ = v___x_866_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_l_863_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_impl_870_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_949_; 
v_isSharedCheck_949_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_950_ = lean_ctor_get(v_impl_870_, 4);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_impl_870_, 2);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_impl_870_, 1);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_954_);
v___x_887_ = v_impl_870_;
v_isShared_888_ = v_isSharedCheck_949_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_impl_870_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_949_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_size_889_; lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v_l_892_; lean_object* v_r_893_; lean_object* v_size_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_size_889_ = lean_ctor_get(v_l_876_, 0);
v_k_890_ = lean_ctor_get(v_l_876_, 1);
v_v_891_ = lean_ctor_get(v_l_876_, 2);
v_l_892_ = lean_ctor_get(v_l_876_, 3);
v_r_893_ = lean_ctor_get(v_l_876_, 4);
v_size_894_ = lean_ctor_get(v_r_877_, 0);
v___x_895_ = lean_unsigned_to_nat(2u);
v___x_896_ = lean_nat_mul(v___x_895_, v_size_894_);
v___x_897_ = lean_nat_dec_lt(v_size_889_, v___x_896_);
lean_dec(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_925_; 
lean_inc(v_r_893_);
lean_inc(v_l_892_);
lean_inc(v_v_891_);
lean_inc(v_k_890_);
v_isSharedCheck_925_ = !lean_is_exclusive(v_l_876_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_926_ = lean_ctor_get(v_l_876_, 4);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_876_, 3);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_876_, 2);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_876_, 1);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_876_, 0);
lean_dec(v_unused_930_);
v___x_899_ = v_l_876_;
v_isShared_900_ = v_isSharedCheck_925_;
goto v_resetjp_898_;
}
else
{
lean_dec(v_l_876_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_925_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_915_; 
v___x_901_ = lean_nat_add(v___x_871_, v_size_872_);
v___x_902_ = lean_nat_add(v___x_901_, v_size_873_);
lean_dec(v_size_873_);
if (lean_obj_tag(v_l_892_) == 0)
{
lean_object* v_size_923_; 
v_size_923_ = lean_ctor_get(v_l_892_, 0);
lean_inc(v_size_923_);
v___y_915_ = v_size_923_;
goto v___jp_914_;
}
else
{
lean_object* v___x_924_; 
v___x_924_ = lean_unsigned_to_nat(0u);
v___y_915_ = v___x_924_;
goto v___jp_914_;
}
v___jp_903_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_nat_add(v___y_904_, v___y_906_);
lean_dec(v___y_906_);
lean_dec(v___y_904_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 4, v_r_877_);
lean_ctor_set(v___x_899_, 3, v_r_893_);
lean_ctor_set(v___x_899_, 2, v_v_875_);
lean_ctor_set(v___x_899_, 1, v_k_874_);
lean_ctor_set(v___x_899_, 0, v___x_907_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_874_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_875_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_893_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_877_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_909_);
lean_ctor_set(v___x_887_, 3, v___y_905_);
lean_ctor_set(v___x_887_, 2, v_v_891_);
lean_ctor_set(v___x_887_, 1, v_k_890_);
lean_ctor_set(v___x_887_, 0, v___x_902_);
v___x_911_ = v___x_887_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v___y_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
v___jp_914_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_nat_add(v___x_901_, v___y_915_);
lean_dec(v___y_915_);
lean_dec(v___x_901_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_l_892_);
lean_ctor_set(v___x_866_, 0, v___x_916_);
v___x_918_ = v___x_866_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_l_863_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_l_892_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_nat_add(v___x_871_, v_size_894_);
if (lean_obj_tag(v_r_893_) == 0)
{
lean_object* v_size_920_; 
v_size_920_ = lean_ctor_get(v_r_893_, 0);
lean_inc(v_size_920_);
v___y_904_ = v___x_919_;
v___y_905_ = v___x_918_;
v___y_906_ = v_size_920_;
goto v___jp_903_;
}
else
{
lean_object* v___x_921_; 
v___x_921_ = lean_unsigned_to_nat(0u);
v___y_904_ = v___x_919_;
v___y_905_ = v___x_918_;
v___y_906_ = v___x_921_;
goto v___jp_903_;
}
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
lean_del_object(v___x_866_);
v___x_931_ = lean_nat_add(v___x_871_, v_size_872_);
v___x_932_ = lean_nat_add(v___x_931_, v_size_873_);
lean_dec(v_size_873_);
v___x_933_ = lean_nat_add(v___x_931_, v_size_889_);
lean_dec(v___x_931_);
lean_inc_ref(v_l_863_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_l_876_);
lean_ctor_set(v___x_887_, 3, v_l_863_);
lean_ctor_set(v___x_887_, 2, v_v_862_);
lean_ctor_set(v___x_887_, 1, v_k_861_);
lean_ctor_set(v___x_887_, 0, v___x_933_);
v___x_935_ = v___x_887_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_l_863_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_l_876_);
v___x_935_ = v_reuseFailAlloc_948_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_isSharedCheck_942_ = !lean_is_exclusive(v_l_863_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_943_ = lean_ctor_get(v_l_863_, 4);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_l_863_, 3);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_863_, 2);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_863_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_l_863_, 0);
lean_dec(v_unused_947_);
v___x_937_ = v_l_863_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_dec(v_l_863_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_r_877_);
lean_ctor_set(v___x_937_, 3, v___x_935_);
lean_ctor_set(v___x_937_, 2, v_v_875_);
lean_ctor_set(v___x_937_, 1, v_k_874_);
lean_ctor_set(v___x_937_, 0, v___x_932_);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_874_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_875_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_r_877_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_955_; 
v_l_955_ = lean_ctor_get(v_impl_870_, 3);
lean_inc(v_l_955_);
if (lean_obj_tag(v_l_955_) == 0)
{
lean_object* v_r_956_; lean_object* v_k_957_; lean_object* v_v_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_981_; 
v_r_956_ = lean_ctor_get(v_impl_870_, 4);
v_k_957_ = lean_ctor_get(v_impl_870_, 1);
v_v_958_ = lean_ctor_get(v_impl_870_, 2);
v_isSharedCheck_981_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_982_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_983_);
v___x_960_ = v_impl_870_;
v_isShared_961_ = v_isSharedCheck_981_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_r_956_);
lean_inc(v_v_958_);
lean_inc(v_k_957_);
lean_dec(v_impl_870_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_981_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_977_; 
v_k_962_ = lean_ctor_get(v_l_955_, 1);
v_v_963_ = lean_ctor_get(v_l_955_, 2);
v_isSharedCheck_977_ = !lean_is_exclusive(v_l_955_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_978_ = lean_ctor_get(v_l_955_, 4);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_l_955_, 3);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_955_, 0);
lean_dec(v_unused_980_);
v___x_965_ = v_l_955_;
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_v_963_);
lean_inc(v_k_962_);
lean_dec(v_l_955_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_977_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_956_, 2);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 4, v_r_956_);
lean_ctor_set(v___x_965_, 3, v_r_956_);
lean_ctor_set(v___x_965_, 2, v_v_862_);
lean_ctor_set(v___x_965_, 1, v_k_861_);
lean_ctor_set(v___x_965_, 0, v___x_871_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_r_956_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_r_956_);
v___x_969_ = v_reuseFailAlloc_976_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
lean_inc(v_r_956_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 3, v_r_956_);
lean_ctor_set(v___x_960_, 0, v___x_871_);
v___x_971_ = v___x_960_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_r_956_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_r_956_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_971_);
lean_ctor_set(v___x_866_, 3, v___x_969_);
lean_ctor_set(v___x_866_, 2, v_v_963_);
lean_ctor_set(v___x_866_, 1, v_k_962_);
lean_ctor_set(v___x_866_, 0, v___x_967_);
v___x_973_ = v___x_866_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
else
{
lean_object* v_r_984_; 
v_r_984_ = lean_ctor_get(v_impl_870_, 4);
lean_inc(v_r_984_);
if (lean_obj_tag(v_r_984_) == 0)
{
lean_object* v_k_985_; lean_object* v_v_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
v_k_985_ = lean_ctor_get(v_impl_870_, 1);
v_v_986_ = lean_ctor_get(v_impl_870_, 2);
v_isSharedCheck_997_ = !lean_is_exclusive(v_impl_870_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_998_ = lean_ctor_get(v_impl_870_, 4);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_impl_870_, 3);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_impl_870_, 0);
lean_dec(v_unused_1000_);
v___x_988_ = v_impl_870_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_v_986_);
lean_inc(v_k_985_);
lean_dec(v_impl_870_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_unsigned_to_nat(3u);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 4, v_l_955_);
lean_ctor_set(v___x_988_, 2, v_v_862_);
lean_ctor_set(v___x_988_, 1, v_k_861_);
lean_ctor_set(v___x_988_, 0, v___x_871_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_l_955_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_l_955_);
v___x_992_ = v_reuseFailAlloc_996_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_r_984_);
lean_ctor_set(v___x_866_, 3, v___x_992_);
lean_ctor_set(v___x_866_, 2, v_v_986_);
lean_ctor_set(v___x_866_, 1, v_k_985_);
lean_ctor_set(v___x_866_, 0, v___x_990_);
v___x_994_ = v___x_866_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_k_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_v_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_r_984_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_unsigned_to_nat(2u);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_impl_870_);
lean_ctor_set(v___x_866_, 3, v_r_984_);
lean_ctor_set(v___x_866_, 0, v___x_1001_);
v___x_1003_ = v___x_866_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_r_984_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_impl_870_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v___x_1006_; 
lean_dec(v_v_862_);
lean_dec(v_k_861_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 2, v_v_858_);
lean_ctor_set(v___x_866_, 1, v_k_857_);
v___x_1006_ = v___x_866_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_size_860_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_857_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_858_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_l_863_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_r_864_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_impl_1008_; lean_object* v___x_1009_; 
lean_dec(v_size_860_);
v_impl_1008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_857_, v_v_858_, v_l_863_);
v___x_1009_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_864_) == 0)
{
lean_object* v_size_1010_; lean_object* v_size_1011_; lean_object* v_k_1012_; lean_object* v_v_1013_; lean_object* v_l_1014_; lean_object* v_r_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_size_1010_ = lean_ctor_get(v_r_864_, 0);
v_size_1011_ = lean_ctor_get(v_impl_1008_, 0);
lean_inc(v_size_1011_);
v_k_1012_ = lean_ctor_get(v_impl_1008_, 1);
lean_inc(v_k_1012_);
v_v_1013_ = lean_ctor_get(v_impl_1008_, 2);
lean_inc(v_v_1013_);
v_l_1014_ = lean_ctor_get(v_impl_1008_, 3);
lean_inc(v_l_1014_);
v_r_1015_ = lean_ctor_get(v_impl_1008_, 4);
lean_inc(v_r_1015_);
v___x_1016_ = lean_unsigned_to_nat(3u);
v___x_1017_ = lean_nat_mul(v___x_1016_, v_size_1010_);
v___x_1018_ = lean_nat_dec_lt(v___x_1017_, v_size_1011_);
lean_dec(v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_dec(v_r_1015_);
lean_dec(v_l_1014_);
lean_dec(v_v_1013_);
lean_dec(v_k_1012_);
v___x_1019_ = lean_nat_add(v___x_1009_, v_size_1011_);
lean_dec(v_size_1011_);
v___x_1020_ = lean_nat_add(v___x_1019_, v_size_1010_);
lean_dec(v___x_1019_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 3, v_impl_1008_);
lean_ctor_set(v___x_866_, 0, v___x_1020_);
v___x_1022_ = v___x_866_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_impl_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_r_864_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1089_; 
v_isSharedCheck_1089_ = !lean_is_exclusive(v_impl_1008_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1090_ = lean_ctor_get(v_impl_1008_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_impl_1008_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_impl_1008_, 2);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_impl_1008_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_impl_1008_, 0);
lean_dec(v_unused_1094_);
v___x_1025_ = v_impl_1008_;
v_isShared_1026_ = v_isSharedCheck_1089_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v_impl_1008_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1089_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_size_1027_; lean_object* v_size_1028_; lean_object* v_k_1029_; lean_object* v_v_1030_; lean_object* v_l_1031_; lean_object* v_r_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_size_1027_ = lean_ctor_get(v_l_1014_, 0);
v_size_1028_ = lean_ctor_get(v_r_1015_, 0);
v_k_1029_ = lean_ctor_get(v_r_1015_, 1);
v_v_1030_ = lean_ctor_get(v_r_1015_, 2);
v_l_1031_ = lean_ctor_get(v_r_1015_, 3);
v_r_1032_ = lean_ctor_get(v_r_1015_, 4);
v___x_1033_ = lean_unsigned_to_nat(2u);
v___x_1034_ = lean_nat_mul(v___x_1033_, v_size_1027_);
v___x_1035_ = lean_nat_dec_lt(v_size_1028_, v___x_1034_);
lean_dec(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1064_; 
lean_inc(v_r_1032_);
lean_inc(v_l_1031_);
lean_inc(v_v_1030_);
lean_inc(v_k_1029_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_r_1015_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1065_ = lean_ctor_get(v_r_1015_, 4);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_r_1015_, 3);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_r_1015_, 2);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_r_1015_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_r_1015_, 0);
lean_dec(v_unused_1069_);
v___x_1037_ = v_r_1015_;
v_isShared_1038_ = v_isSharedCheck_1064_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_r_1015_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1064_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1052_; lean_object* v___y_1054_; 
v___x_1039_ = lean_nat_add(v___x_1009_, v_size_1011_);
lean_dec(v_size_1011_);
v___x_1040_ = lean_nat_add(v___x_1039_, v_size_1010_);
lean_dec(v___x_1039_);
v___x_1052_ = lean_nat_add(v___x_1009_, v_size_1027_);
if (lean_obj_tag(v_l_1031_) == 0)
{
lean_object* v_size_1062_; 
v_size_1062_ = lean_ctor_get(v_l_1031_, 0);
lean_inc(v_size_1062_);
v___y_1054_ = v_size_1062_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___y_1054_ = v___x_1063_;
goto v___jp_1053_;
}
v___jp_1041_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_nat_add(v___y_1042_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec(v___y_1042_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 4, v_r_864_);
lean_ctor_set(v___x_1037_, 3, v_r_1032_);
lean_ctor_set(v___x_1037_, 2, v_v_862_);
lean_ctor_set(v___x_1037_, 1, v_k_861_);
lean_ctor_set(v___x_1037_, 0, v___x_1045_);
v___x_1047_ = v___x_1037_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_r_1032_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_r_864_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v___x_1047_);
lean_ctor_set(v___x_1025_, 3, v___y_1043_);
lean_ctor_set(v___x_1025_, 2, v_v_1030_);
lean_ctor_set(v___x_1025_, 1, v_k_1029_);
lean_ctor_set(v___x_1025_, 0, v___x_1040_);
v___x_1049_ = v___x_1025_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v___y_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
v___jp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_nat_add(v___x_1052_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec(v___x_1052_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_l_1031_);
lean_ctor_set(v___x_866_, 3, v_l_1014_);
lean_ctor_set(v___x_866_, 2, v_v_1013_);
lean_ctor_set(v___x_866_, 1, v_k_1012_);
lean_ctor_set(v___x_866_, 0, v___x_1055_);
v___x_1057_ = v___x_866_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_k_1012_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_v_1013_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_l_1014_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_l_1031_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_nat_add(v___x_1009_, v_size_1010_);
if (lean_obj_tag(v_r_1032_) == 0)
{
lean_object* v_size_1059_; 
v_size_1059_ = lean_ctor_get(v_r_1032_, 0);
lean_inc(v_size_1059_);
v___y_1042_ = v___x_1058_;
v___y_1043_ = v___x_1057_;
v___y_1044_ = v_size_1059_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___y_1042_ = v___x_1058_;
v___y_1043_ = v___x_1057_;
v___y_1044_ = v___x_1060_;
goto v___jp_1041_;
}
}
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_del_object(v___x_866_);
v___x_1070_ = lean_nat_add(v___x_1009_, v_size_1011_);
lean_dec(v_size_1011_);
v___x_1071_ = lean_nat_add(v___x_1070_, v_size_1010_);
lean_dec(v___x_1070_);
v___x_1072_ = lean_nat_add(v___x_1009_, v_size_1010_);
v___x_1073_ = lean_nat_add(v___x_1072_, v_size_1028_);
lean_dec(v___x_1072_);
lean_inc_ref(v_r_864_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v_r_864_);
lean_ctor_set(v___x_1025_, 3, v_r_1015_);
lean_ctor_set(v___x_1025_, 2, v_v_862_);
lean_ctor_set(v___x_1025_, 1, v_k_861_);
lean_ctor_set(v___x_1025_, 0, v___x_1073_);
v___x_1075_ = v___x_1025_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_r_1015_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_r_864_);
v___x_1075_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v_r_864_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1083_ = lean_ctor_get(v_r_864_, 4);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_r_864_, 3);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_r_864_, 2);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_r_864_, 1);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_r_864_, 0);
lean_dec(v_unused_1087_);
v___x_1077_ = v_r_864_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v_r_864_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 4, v___x_1075_);
lean_ctor_set(v___x_1077_, 3, v_l_1014_);
lean_ctor_set(v___x_1077_, 2, v_v_1013_);
lean_ctor_set(v___x_1077_, 1, v_k_1012_);
lean_ctor_set(v___x_1077_, 0, v___x_1071_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_k_1012_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_v_1013_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_l_1014_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1095_; 
v_l_1095_ = lean_ctor_get(v_impl_1008_, 3);
lean_inc(v_l_1095_);
if (lean_obj_tag(v_l_1095_) == 0)
{
lean_object* v_r_1096_; lean_object* v_k_1097_; lean_object* v_v_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1109_; 
v_r_1096_ = lean_ctor_get(v_impl_1008_, 4);
v_k_1097_ = lean_ctor_get(v_impl_1008_, 1);
v_v_1098_ = lean_ctor_get(v_impl_1008_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_impl_1008_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1110_ = lean_ctor_get(v_impl_1008_, 3);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_impl_1008_, 0);
lean_dec(v_unused_1111_);
v___x_1100_ = v_impl_1008_;
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_r_1096_);
lean_inc(v_v_1098_);
lean_inc(v_k_1097_);
lean_dec(v_impl_1008_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1096_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 3, v_r_1096_);
lean_ctor_set(v___x_1100_, 2, v_v_862_);
lean_ctor_set(v___x_1100_, 1, v_k_861_);
lean_ctor_set(v___x_1100_, 0, v___x_1009_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_r_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_r_1096_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_1104_);
lean_ctor_set(v___x_866_, 3, v_l_1095_);
lean_ctor_set(v___x_866_, 2, v_v_1098_);
lean_ctor_set(v___x_866_, 1, v_k_1097_);
lean_ctor_set(v___x_866_, 0, v___x_1102_);
v___x_1106_ = v___x_866_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1098_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___x_1104_);
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
else
{
lean_object* v_r_1112_; 
v_r_1112_ = lean_ctor_get(v_impl_1008_, 4);
lean_inc(v_r_1112_);
if (lean_obj_tag(v_r_1112_) == 0)
{
lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1137_; 
v_k_1113_ = lean_ctor_get(v_impl_1008_, 1);
v_v_1114_ = lean_ctor_get(v_impl_1008_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_impl_1008_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_impl_1008_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_impl_1008_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_impl_1008_, 0);
lean_dec(v_unused_1140_);
v___x_1116_ = v_impl_1008_;
v_isShared_1117_ = v_isSharedCheck_1137_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_v_1114_);
lean_inc(v_k_1113_);
lean_dec(v_impl_1008_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1137_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1133_; 
v_k_1118_ = lean_ctor_get(v_r_1112_, 1);
v_v_1119_ = lean_ctor_get(v_r_1112_, 2);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; lean_object* v_unused_1135_; lean_object* v_unused_1136_; 
v_unused_1134_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1136_);
v___x_1121_ = v_r_1112_;
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_v_1119_);
lean_inc(v_k_1118_);
lean_dec(v_r_1112_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1133_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_unsigned_to_nat(3u);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v_l_1095_);
lean_ctor_set(v___x_1121_, 3, v_l_1095_);
lean_ctor_set(v___x_1121_, 2, v_v_1114_);
lean_ctor_set(v___x_1121_, 1, v_k_1113_);
lean_ctor_set(v___x_1121_, 0, v___x_1009_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_1114_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_l_1095_);
v___x_1125_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v_l_1095_);
lean_ctor_set(v___x_1116_, 2, v_v_862_);
lean_ctor_set(v___x_1116_, 1, v_k_861_);
lean_ctor_set(v___x_1116_, 0, v___x_1009_);
v___x_1127_ = v___x_1116_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_l_1095_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_l_1095_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_1127_);
lean_ctor_set(v___x_866_, 3, v___x_1125_);
lean_ctor_set(v___x_866_, 2, v_v_1119_);
lean_ctor_set(v___x_866_, 1, v_k_1118_);
lean_ctor_set(v___x_866_, 0, v___x_1123_);
v___x_1129_ = v___x_866_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1118_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1119_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_unsigned_to_nat(2u);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v_r_1112_);
lean_ctor_set(v___x_866_, 3, v_impl_1008_);
lean_ctor_set(v___x_866_, 0, v___x_1141_);
v___x_1143_ = v___x_866_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_861_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_862_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_impl_1008_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1112_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_k_857_);
lean_ctor_set(v___x_1147_, 2, v_v_858_);
lean_ctor_set(v___x_1147_, 3, v_t_859_);
lean_ctor_set(v___x_1147_, 4, v_t_859_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1148_, lean_object* v_b_1149_){
_start:
{
if (lean_obj_tag(v_as_x27_1148_) == 0)
{
return v_b_1149_;
}
else
{
lean_object* v_head_1150_; lean_object* v_tail_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v_r_1154_; 
v_head_1150_ = lean_ctor_get(v_as_x27_1148_, 0);
v_tail_1151_ = lean_ctor_get(v_as_x27_1148_, 1);
v_fst_1152_ = lean_ctor_get(v_head_1150_, 0);
v_snd_1153_ = lean_ctor_get(v_head_1150_, 1);
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
v_r_1154_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1152_, v_snd_1153_, v_b_1149_);
v_as_x27_1148_ = v_tail_1151_;
v_b_1149_ = v_r_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1156_, v_b_1157_);
lean_dec(v_as_x27_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1167_, lean_object* v_expr_1168_, lean_object* v_lctx_1169_, lean_object* v_location_x3f_1170_, lean_object* v_docString_x3f_1171_, lean_object* v_mkDocString_x3f_1172_, uint8_t v_explicit_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___y_1181_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_fmt_1167_);
v___x_1176_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1177_ = lean_box(0);
v___x_1178_ = 0;
v___x_1179_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v_lctx_1169_);
lean_ctor_set(v___x_1179_, 2, v___x_1177_);
lean_ctor_set(v___x_1179_, 3, v_expr_1168_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*4, v___x_1178_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*4 + 1, v___x_1178_);
if (lean_obj_tag(v_mkDocString_x3f_1172_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1171_) == 0)
{
v___y_1181_ = v_mkDocString_x3f_1172_;
goto v___jp_1180_;
}
else
{
lean_object* v_val_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_val_1191_ = lean_ctor_get(v_docString_x3f_1171_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_docString_x3f_1171_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v_docString_x3f_1171_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_val_1191_);
lean_dec(v_docString_x3f_1171_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___f_1195_; lean_object* v___x_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1195_, 0, v_val_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___f_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___f_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v___y_1181_ = v___x_1197_;
goto v___jp_1180_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1171_);
v___y_1181_ = v_mkDocString_x3f_1172_;
goto v___jp_1180_;
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_r_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1182_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1179_);
lean_ctor_set(v___x_1182_, 1, v_location_x3f_1170_);
lean_ctor_set(v___x_1182_, 2, v___y_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3, v_explicit_1173_);
v___x_1183_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1174_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v_r_1187_ = lean_box(1);
v___x_1188_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1186_, v_r_1187_);
lean_dec_ref_known(v___x_1186_, 2);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1175_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1200_, lean_object* v_expr_1201_, lean_object* v_lctx_1202_, lean_object* v_location_x3f_1203_, lean_object* v_docString_x3f_1204_, lean_object* v_mkDocString_x3f_1205_, lean_object* v_explicit_1206_){
_start:
{
uint8_t v_explicit_boxed_1207_; lean_object* v_res_1208_; 
v_explicit_boxed_1207_ = lean_unbox(v_explicit_1206_);
v_res_1208_ = l_Lean_MessageData_withExprHover(v_fmt_1200_, v_expr_1201_, v_lctx_1202_, v_location_x3f_1203_, v_docString_x3f_1204_, v_mkDocString_x3f_1205_, v_explicit_boxed_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1209_, lean_object* v_k_1210_, lean_object* v_v_1211_, lean_object* v_t_1212_, lean_object* v_hl_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1210_, v_v_1211_, v_t_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1215_, lean_object* v_as_x27_1216_, lean_object* v_b_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1216_, v_b_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1220_, lean_object* v_as_x27_1221_, lean_object* v_b_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1220_, v_as_x27_1221_, v_b_1222_, v_a_1223_);
lean_dec(v_as_x27_1221_);
lean_dec(v_as_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1225_, lean_object* v_expr_1226_, lean_object* v_location_x3f_1227_, lean_object* v_docString_x3f_1228_, lean_object* v_mkDocString_x3f_1229_, uint8_t v_explicit_1230_, lean_object* v_toPure_1231_, lean_object* v_lctx_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = l_Lean_MessageData_withExprHover(v_fmt_1225_, v_expr_1226_, v_lctx_1232_, v_location_x3f_1227_, v_docString_x3f_1228_, v_mkDocString_x3f_1229_, v_explicit_1230_);
v___x_1234_ = lean_apply_2(v_toPure_1231_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1235_, lean_object* v_expr_1236_, lean_object* v_location_x3f_1237_, lean_object* v_docString_x3f_1238_, lean_object* v_mkDocString_x3f_1239_, lean_object* v_explicit_1240_, lean_object* v_toPure_1241_, lean_object* v_lctx_1242_){
_start:
{
uint8_t v_explicit_boxed_1243_; lean_object* v_res_1244_; 
v_explicit_boxed_1243_ = lean_unbox(v_explicit_1240_);
v_res_1244_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1235_, v_expr_1236_, v_location_x3f_1237_, v_docString_x3f_1238_, v_mkDocString_x3f_1239_, v_explicit_boxed_1243_, v_toPure_1241_, v_lctx_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_fmt_1247_, lean_object* v_expr_1248_, lean_object* v_lctx_x3f_1249_, lean_object* v_location_x3f_1250_, lean_object* v_docString_x3f_1251_, lean_object* v_mkDocString_x3f_1252_, uint8_t v_explicit_1253_){
_start:
{
lean_object* v_toApplicative_1254_; lean_object* v_toBind_1255_; lean_object* v_toPure_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; 
v_toApplicative_1254_ = lean_ctor_get(v_inst_1245_, 0);
lean_inc_ref(v_toApplicative_1254_);
v_toBind_1255_ = lean_ctor_get(v_inst_1245_, 1);
lean_inc(v_toBind_1255_);
lean_dec_ref(v_inst_1245_);
v_toPure_1256_ = lean_ctor_get(v_toApplicative_1254_, 1);
lean_inc_n(v_toPure_1256_, 2);
lean_dec_ref(v_toApplicative_1254_);
v___x_1257_ = lean_box(v_explicit_1253_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1258_, 0, v_fmt_1247_);
lean_closure_set(v___f_1258_, 1, v_expr_1248_);
lean_closure_set(v___f_1258_, 2, v_location_x3f_1250_);
lean_closure_set(v___f_1258_, 3, v_docString_x3f_1251_);
lean_closure_set(v___f_1258_, 4, v_mkDocString_x3f_1252_);
lean_closure_set(v___f_1258_, 5, v___x_1257_);
lean_closure_set(v___f_1258_, 6, v_toPure_1256_);
if (lean_obj_tag(v_lctx_x3f_1249_) == 0)
{
lean_object* v___x_1259_; 
lean_dec(v_toPure_1256_);
v___x_1259_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v_inst_1246_, v___f_1258_);
return v___x_1259_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_inst_1246_);
v_val_1260_ = lean_ctor_get(v_lctx_x3f_1249_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_lctx_x3f_1249_, 1);
v___x_1261_ = lean_apply_2(v_toPure_1256_, lean_box(0), v_val_1260_);
v___x_1262_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1261_, v___f_1258_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_fmt_1265_, lean_object* v_expr_1266_, lean_object* v_lctx_x3f_1267_, lean_object* v_location_x3f_1268_, lean_object* v_docString_x3f_1269_, lean_object* v_mkDocString_x3f_1270_, lean_object* v_explicit_1271_){
_start:
{
uint8_t v_explicit_boxed_1272_; lean_object* v_res_1273_; 
v_explicit_boxed_1272_ = lean_unbox(v_explicit_1271_);
v_res_1273_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1263_, v_inst_1264_, v_fmt_1265_, v_expr_1266_, v_lctx_x3f_1267_, v_location_x3f_1268_, v_docString_x3f_1269_, v_mkDocString_x3f_1270_, v_explicit_boxed_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_fmt_1277_, lean_object* v_expr_1278_, lean_object* v_lctx_x3f_1279_, lean_object* v_location_x3f_1280_, lean_object* v_docString_x3f_1281_, lean_object* v_mkDocString_x3f_1282_, uint8_t v_explicit_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1275_, v_inst_1276_, v_fmt_1277_, v_expr_1278_, v_lctx_x3f_1279_, v_location_x3f_1280_, v_docString_x3f_1281_, v_mkDocString_x3f_1282_, v_explicit_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_fmt_1288_, lean_object* v_expr_1289_, lean_object* v_lctx_x3f_1290_, lean_object* v_location_x3f_1291_, lean_object* v_docString_x3f_1292_, lean_object* v_mkDocString_x3f_1293_, lean_object* v_explicit_1294_){
_start:
{
uint8_t v_explicit_boxed_1295_; lean_object* v_res_1296_; 
v_explicit_boxed_1295_ = lean_unbox(v_explicit_1294_);
v_res_1296_ = l_Lean_MessageData_withExprHoverM(v_m_1285_, v_inst_1286_, v_inst_1287_, v_fmt_1288_, v_expr_1289_, v_lctx_x3f_1290_, v_location_x3f_1291_, v_docString_x3f_1292_, v_mkDocString_x3f_1293_, v_explicit_boxed_1295_);
return v_res_1296_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
lean_ctor_set(v___x_1302_, 4, v___x_1300_);
lean_ctor_set(v___x_1302_, 5, v___x_1300_);
lean_ctor_set(v___x_1302_, 6, v___x_1300_);
lean_ctor_set(v___x_1302_, 7, v___x_1300_);
lean_ctor_set(v___x_1302_, 8, v___x_1300_);
lean_ctor_set(v___x_1302_, 9, v___x_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1303_, lean_object* v_a_1304_){
_start:
{
switch(lean_obj_tag(v_a_1304_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1303_) == 0)
{
lean_object* v_hasSyntheticSorry_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_hasSyntheticSorry_1305_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_hasSyntheticSorry_1305_);
lean_dec_ref_known(v_a_1304_, 2);
v___x_1306_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1307_ = lean_apply_1(v_hasSyntheticSorry_1305_, v___x_1306_);
v___x_1308_ = lean_unbox(v___x_1307_);
return v___x_1308_;
}
else
{
lean_object* v_hasSyntheticSorry_1309_; lean_object* v_val_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_hasSyntheticSorry_1309_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_hasSyntheticSorry_1309_);
lean_dec_ref_known(v_a_1304_, 2);
v_val_1310_ = lean_ctor_get(v_mctx_x3f_1303_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_mctx_x3f_1303_, 1);
v___x_1311_ = lean_apply_1(v_hasSyntheticSorry_1309_, v_val_1310_);
v___x_1312_ = lean_unbox(v___x_1311_);
return v___x_1312_;
}
}
case 3:
{
lean_object* v_a_1313_; lean_object* v_a_1314_; lean_object* v_mctx_1315_; lean_object* v___x_1316_; 
lean_dec(v_mctx_x3f_1303_);
v_a_1313_ = lean_ctor_get(v_a_1304_, 0);
lean_inc_ref(v_a_1313_);
v_a_1314_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_a_1314_);
lean_dec_ref_known(v_a_1304_, 2);
v_mctx_1315_ = lean_ctor_get(v_a_1313_, 1);
lean_inc_ref(v_mctx_1315_);
lean_dec_ref(v_a_1313_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_mctx_1315_);
v_mctx_x3f_1303_ = v___x_1316_;
v_a_1304_ = v_a_1314_;
goto _start;
}
case 4:
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_a_1318_);
lean_dec_ref_known(v_a_1304_, 2);
v_a_1304_ = v_a_1318_;
goto _start;
}
case 5:
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_a_1320_);
lean_dec_ref_known(v_a_1304_, 2);
v_a_1304_ = v_a_1320_;
goto _start;
}
case 6:
{
lean_object* v_a_1322_; 
v_a_1322_ = lean_ctor_get(v_a_1304_, 0);
lean_inc_ref(v_a_1322_);
lean_dec_ref_known(v_a_1304_, 1);
v_a_1304_ = v_a_1322_;
goto _start;
}
case 7:
{
lean_object* v_a_1324_; lean_object* v_a_1325_; uint8_t v___x_1326_; 
v_a_1324_ = lean_ctor_get(v_a_1304_, 0);
lean_inc_ref(v_a_1324_);
v_a_1325_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_a_1325_);
lean_dec_ref_known(v_a_1304_, 2);
lean_inc(v_mctx_x3f_1303_);
v___x_1326_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1303_, v_a_1324_);
if (v___x_1326_ == 0)
{
v_a_1304_ = v_a_1325_;
goto _start;
}
else
{
lean_dec_ref(v_a_1325_);
lean_dec(v_mctx_x3f_1303_);
return v___x_1326_;
}
}
case 8:
{
lean_object* v_a_1328_; 
v_a_1328_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_a_1328_);
lean_dec_ref_known(v_a_1304_, 2);
v_a_1304_ = v_a_1328_;
goto _start;
}
case 9:
{
lean_object* v_msg_1330_; lean_object* v_children_1331_; uint8_t v___x_1332_; 
v_msg_1330_ = lean_ctor_get(v_a_1304_, 1);
lean_inc_ref(v_msg_1330_);
v_children_1331_ = lean_ctor_get(v_a_1304_, 2);
lean_inc_ref(v_children_1331_);
lean_dec_ref_known(v_a_1304_, 3);
lean_inc(v_mctx_x3f_1303_);
v___x_1332_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1303_, v_msg_1330_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_array_get_size(v_children_1331_);
v___x_1335_ = lean_nat_dec_lt(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_children_1331_);
lean_dec(v_mctx_x3f_1303_);
return v___x_1332_;
}
else
{
if (v___x_1335_ == 0)
{
lean_dec_ref(v_children_1331_);
lean_dec(v_mctx_x3f_1303_);
return v___x_1332_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1334_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1303_, v_children_1331_, v___x_1336_, v___x_1337_);
lean_dec_ref(v_children_1331_);
return v___x_1338_;
}
}
}
else
{
lean_dec_ref(v_children_1331_);
lean_dec(v_mctx_x3f_1303_);
return v___x_1332_;
}
}
default: 
{
uint8_t v___x_1339_; 
lean_dec_ref(v_a_1304_);
lean_dec(v_mctx_x3f_1303_);
v___x_1339_ = 0;
return v___x_1339_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1340_, lean_object* v_as_1341_, size_t v_i_1342_, size_t v_stop_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_eq(v_i_1342_, v_stop_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_array_uget_borrowed(v_as_1341_, v_i_1342_);
lean_inc(v___x_1345_);
lean_inc(v_mctx_x3f_1340_);
v___x_1346_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1340_, v___x_1345_);
if (v___x_1346_ == 0)
{
size_t v___x_1347_; size_t v___x_1348_; 
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1342_, v___x_1347_);
v_i_1342_ = v___x_1348_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1340_);
return v___x_1346_;
}
}
else
{
uint8_t v___x_1350_; 
lean_dec(v_mctx_x3f_1340_);
v___x_1350_ = 0;
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1351_, lean_object* v_as_1352_, lean_object* v_i_1353_, lean_object* v_stop_1354_){
_start:
{
size_t v_i_boxed_1355_; size_t v_stop_boxed_1356_; uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_i_boxed_1355_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_stop_boxed_1356_ = lean_unbox_usize(v_stop_1354_);
lean_dec(v_stop_1354_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1351_, v_as_1352_, v_i_boxed_1355_, v_stop_boxed_1356_);
lean_dec_ref(v_as_1352_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1359_, lean_object* v_a_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1359_, v_a_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1363_){
_start:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1364_, v_msg_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1366_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_1369_, lean_object* v_decl_1370_, lean_object* v_ref_1371_){
_start:
{
lean_object* v_defValue_1373_; lean_object* v_descr_1374_; lean_object* v_deprecation_x3f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_defValue_1373_ = lean_ctor_get(v_decl_1370_, 0);
v_descr_1374_ = lean_ctor_get(v_decl_1370_, 1);
v_deprecation_x3f_1375_ = lean_ctor_get(v_decl_1370_, 2);
lean_inc(v_defValue_1373_);
v___x_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_defValue_1373_);
lean_inc(v_deprecation_x3f_1375_);
lean_inc_ref(v_descr_1374_);
lean_inc_n(v_name_1369_, 2);
v___x_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1377_, 0, v_name_1369_);
lean_ctor_set(v___x_1377_, 1, v_ref_1371_);
lean_ctor_set(v___x_1377_, 2, v___x_1376_);
lean_ctor_set(v___x_1377_, 3, v_descr_1374_);
lean_ctor_set(v___x_1377_, 4, v_deprecation_x3f_1375_);
v___x_1378_ = lean_register_option(v_name_1369_, v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1378_, 0);
lean_dec(v_unused_1387_);
v___x_1380_ = v___x_1378_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v___x_1378_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_inc(v_defValue_1373_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_name_1369_);
lean_ctor_set(v___x_1382_, 1, v_defValue_1373_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_name_1369_);
v_a_1388_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1378_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1378_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1396_, lean_object* v_decl_1397_, lean_object* v_ref_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_1396_, v_decl_1397_, v_ref_1398_);
lean_dec_ref(v_decl_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1415_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1416_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1417_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_1414_, v___x_1415_, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_nat_to_int(v_a_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_instMonadBaseIO;
v___x_1424_ = l_instInhabitedOfMonad___redArg(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_2071__overap_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2071__overap_1428_ = lean_panic_fn_borrowed(v___x_1427_, v_msg_1425_);
v___x_1429_ = lean_apply_1(v___x_2071__overap_1428_, lean_box(0));
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_dec(v_x_1433_);
return v_x_1434_;
}
else
{
lean_object* v_head_1436_; lean_object* v_tail_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_head_1436_ = lean_ctor_get(v_x_1435_, 0);
v_tail_1437_ = lean_ctor_get(v_x_1435_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v_x_1435_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_tail_1437_);
lean_inc(v_head_1436_);
lean_dec(v_x_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
lean_inc(v_x_1433_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 5);
lean_ctor_set(v___x_1439_, 1, v_x_1433_);
lean_ctor_set(v___x_1439_, 0, v_x_1434_);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_x_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_x_1433_);
v___x_1442_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_head_1436_);
v_x_1434_ = v___x_1443_;
v_x_1435_ = v_tail_1437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_x_1448_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v_tail_1450_; 
v_tail_1450_ = lean_ctor_get(v_x_1447_, 1);
if (lean_obj_tag(v_tail_1450_) == 0)
{
lean_object* v_head_1451_; 
lean_dec(v_x_1448_);
v_head_1451_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_head_1451_);
lean_dec_ref_known(v_x_1447_, 2);
return v_head_1451_;
}
else
{
lean_object* v_head_1452_; lean_object* v___x_1453_; 
lean_inc(v_tail_1450_);
v_head_1452_ = lean_ctor_get(v_x_1447_, 0);
lean_inc(v_head_1452_);
lean_dec_ref_known(v_x_1447_, 2);
v___x_1453_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1448_, v_head_1452_, v_tail_1450_);
return v___x_1453_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1468_; double v___x_1469_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_float_of_nat(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
switch(lean_obj_tag(v_x_1475_))
{
case 0:
{
lean_object* v_a_1477_; lean_object* v_fmt_1478_; 
lean_dec(v_x_1474_);
lean_dec_ref(v_x_1473_);
v_a_1477_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_a_1477_);
lean_dec_ref_known(v_x_1475_, 1);
v_fmt_1478_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_fmt_1478_);
lean_dec_ref(v_a_1477_);
return v_fmt_1478_;
}
case 1:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v_x_1473_);
v_a_1479_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v_x_1475_, 1);
v___x_1480_ = l_Lean_formatRawGoal(v_a_1479_);
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v_val_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1481_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v_x_1475_, 1);
v_val_1482_ = lean_ctor_get(v_x_1474_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v_x_1474_, 1);
v___x_1483_ = l_Lean_MessageData_mkPPContext(v_x_1473_, v_val_1482_);
lean_dec(v_val_1482_);
lean_dec_ref(v_x_1473_);
v___x_1484_ = l_Lean_ppGoal(v___x_1483_, v_a_1481_);
return v___x_1484_;
}
}
case 3:
{
lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___x_1487_; 
lean_dec(v_x_1474_);
v_a_1485_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_a_1485_);
v_a_1486_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_a_1486_);
lean_dec_ref_known(v_x_1475_, 2);
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_a_1485_);
v_x_1474_ = v___x_1487_;
v_x_1475_ = v_a_1486_;
goto _start;
}
case 4:
{
lean_object* v_a_1489_; lean_object* v_a_1490_; 
lean_dec_ref(v_x_1473_);
v_a_1489_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_a_1489_);
v_a_1490_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_a_1490_);
lean_dec_ref_known(v_x_1475_, 2);
v_x_1473_ = v_a_1489_;
v_x_1475_ = v_a_1490_;
goto _start;
}
case 5:
{
lean_object* v_a_1492_; lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1502_; 
v_a_1492_ = lean_ctor_get(v_x_1475_, 0);
v_a_1493_ = lean_ctor_get(v_x_1475_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1495_ = v_x_1475_;
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_inc(v_a_1492_);
lean_dec(v_x_1475_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = l_Lean_MessageData_formatAux(v_x_1473_, v_x_1474_, v_a_1493_);
v___x_1498_ = lean_nat_to_int(v_a_1492_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 4);
lean_ctor_set(v___x_1495_, 1, v___x_1497_);
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1497_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
case 6:
{
lean_object* v_a_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; 
v_a_1503_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_a_1503_);
lean_dec_ref_known(v_x_1475_, 1);
v___x_1504_ = l_Lean_MessageData_formatAux(v_x_1473_, v_x_1474_, v_a_1503_);
v___x_1505_ = 0;
v___x_1506_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set_uint8(v___x_1506_, sizeof(void*)*1, v___x_1505_);
return v___x_1506_;
}
case 7:
{
lean_object* v_a_1507_; lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
v_a_1507_ = lean_ctor_get(v_x_1475_, 0);
v_a_1508_ = lean_ctor_get(v_x_1475_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1475_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1510_ = v_x_1475_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_inc(v_a_1507_);
lean_dec(v_x_1475_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_inc(v_x_1474_);
lean_inc_ref(v_x_1473_);
v___x_1512_ = l_Lean_MessageData_formatAux(v_x_1473_, v_x_1474_, v_a_1507_);
v___x_1513_ = l_Lean_MessageData_formatAux(v_x_1473_, v_x_1474_, v_a_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 5);
lean_ctor_set(v___x_1510_, 1, v___x_1513_);
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
case 9:
{
lean_object* v_data_1518_; lean_object* v_msg_1519_; lean_object* v_children_1520_; size_t v_sz_1521_; size_t v___x_1522_; lean_object* v___x_1523_; lean_object* v_msg_1525_; lean_object* v_cls_1537_; double v_startTime_1538_; double v_stopTime_1539_; uint8_t v___x_1540_; 
v_data_1518_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_data_1518_);
v_msg_1519_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_msg_1519_);
v_children_1520_ = lean_ctor_get(v_x_1475_, 2);
lean_inc_ref(v_children_1520_);
lean_dec_ref_known(v_x_1475_, 3);
v_sz_1521_ = lean_array_size(v_children_1520_);
v___x_1522_ = ((size_t)0ULL);
lean_inc(v_x_1474_);
lean_inc_ref(v_x_1473_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1473_, v_x_1474_, v_sz_1521_, v___x_1522_, v_children_1520_);
v_cls_1537_ = lean_ctor_get(v_data_1518_, 0);
lean_inc(v_cls_1537_);
v_startTime_1538_ = lean_ctor_get_float(v_data_1518_, sizeof(void*)*3);
v_stopTime_1539_ = lean_ctor_get_float(v_data_1518_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1518_);
v___x_1540_ = l_Lean_Name_isAnonymous(v_cls_1537_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; double v___x_1556_; uint8_t v___x_1557_; 
v___x_1541_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1542_ = 1;
v___x_1543_ = l_Lean_Name_toString(v_cls_1537_, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1541_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1556_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1557_ = lean_float_beq(v_startTime_1538_, v___x_1556_);
if (v___x_1557_ == 0)
{
goto v___jp_1548_;
}
else
{
if (v___x_1540_ == 0)
{
v_msg_1525_ = v___x_1547_;
goto v___jp_1524_;
}
else
{
goto v___jp_1548_;
}
}
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; double v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1549_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_float_sub(v_stopTime_1539_, v_startTime_1538_);
v___x_1552_ = lean_float_to_string(v___x_1551_);
v___x_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1550_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1546_);
v_msg_1525_ = v___x_1555_;
goto v___jp_1524_;
}
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_cls_1537_);
lean_dec_ref(v_msg_1519_);
lean_dec(v_x_1474_);
lean_dec_ref(v_x_1473_);
v___x_1558_ = lean_array_to_list(v___x_1523_);
v___x_1559_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1560_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1558_, v___x_1559_);
return v___x_1560_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1526_ = l_Lean_MessageData_formatAux(v_x_1473_, v_x_1474_, v_msg_1519_);
v___x_1527_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_msg_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1528_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_array_to_list(v___x_1523_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1535_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1533_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1529_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
}
case 10:
{
lean_object* v_f_1561_; lean_object* v___x_1562_; lean_object* v___y_1564_; 
v_f_1561_ = lean_ctor_get(v_x_1475_, 0);
lean_inc_ref(v_f_1561_);
lean_dec_ref_known(v_x_1475_, 2);
v___x_1562_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
v___y_1564_ = v___x_1580_;
goto v___jp_1563_;
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_val_1581_ = lean_ctor_get(v_x_1474_, 0);
v___x_1582_ = l_Lean_MessageData_mkPPContext(v_x_1473_, v_val_1581_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___y_1564_ = v___x_1583_;
goto v___jp_1563_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_apply_2(v_f_1561_, v___y_1564_, lean_box(0));
v___x_1566_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1565_, v___x_1562_);
if (lean_obj_tag(v___x_1566_) == 1)
{
lean_object* v_val_1567_; 
lean_dec(v___x_1565_);
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v_x_1475_ = v_val_1567_;
goto _start;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v___x_1566_);
lean_dec(v_x_1474_);
lean_dec_ref(v_x_1473_);
v___x_1569_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1570_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1571_ = lean_unsigned_to_nat(372u);
v___x_1572_ = lean_unsigned_to_nat(8u);
v___x_1573_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1574_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1565_);
lean_dec(v___x_1565_);
v___x_1575_ = 1;
v___x_1576_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1574_, v___x_1575_);
v___x_1577_ = lean_string_append(v___x_1573_, v___x_1576_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = l_mkPanicMessageWithDecl(v___x_1569_, v___x_1570_, v___x_1571_, v___x_1572_, v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1578_);
return v___x_1579_;
}
}
}
default: 
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v_x_1475_, 1);
lean_inc_ref(v_a_1584_);
lean_dec_ref(v_x_1475_);
v_x_1475_ = v_a_1584_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1586_, lean_object* v_x_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_bs_1590_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1592_ == 0)
{
lean_dec(v_x_1587_);
lean_dec_ref(v_x_1586_);
return v_bs_1590_;
}
else
{
lean_object* v_v_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_bs_x27_1596_; size_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v_v_1593_ = lean_array_uget_borrowed(v_bs_1590_, v_i_1589_);
lean_inc(v_v_1593_);
lean_inc(v_x_1587_);
lean_inc_ref(v_x_1586_);
v___x_1594_ = l_Lean_MessageData_formatAux(v_x_1586_, v_x_1587_, v_v_1593_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v_bs_x27_1596_ = lean_array_uset(v_bs_1590_, v_i_1589_, v___x_1595_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_add(v_i_1589_, v___x_1597_);
v___x_1599_ = lean_array_uset(v_bs_x27_1596_, v_i_1589_, v___x_1594_);
v_i_1589_ = v___x_1598_;
v_bs_1590_ = v___x_1599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_bs_1605_, lean_object* v___y_1606_){
_start:
{
size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; lean_object* v_res_1609_; 
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1601_, v_x_1602_, v_sz_boxed_1607_, v_i_boxed_1608_, v_bs_1605_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_MessageData_formatAux(v_x_1610_, v_x_1611_, v_x_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1618_, lean_object* v_ctx_x3f_1619_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1622_ = l_Lean_MessageData_formatAux(v___x_1621_, v_ctx_x3f_1619_, v_msgData_1618_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1623_, lean_object* v_ctx_x3f_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_MessageData_format(v_msgData_1623_, v_ctx_x3f_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = l_Lean_MessageData_format(v_msgData_1627_, v___x_1629_);
v___x_1631_ = l_Std_Format_defWidth;
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = l_Std_Format_pretty(v___x_1630_, v___x_1631_, v___x_1632_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_MessageData_toString(v_msgData_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1637_);
lean_ctor_set(v___x_1639_, 1, v_a_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_s_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_a_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1667_ = l_Lean_MessageData_ofFormat(v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1668_){
_start:
{
if (lean_obj_tag(v_o_1668_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1669_;
}
else
{
lean_object* v_val_1670_; lean_object* v___x_1671_; 
v_val_1670_ = lean_ctor_get(v_o_1668_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v_o_1668_, 1);
v___x_1671_ = l_Lean_MessageData_ofExpr(v_val_1670_);
return v___x_1671_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1675_ = l_Lean_MessageData_ofFormat(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1680_ = l_Lean_MessageData_ofFormat(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1681_, lean_object* v_i_1682_, lean_object* v_acc_1683_){
_start:
{
lean_object* v___y_1685_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = lean_array_get_size(v_es_1681_);
v___x_1690_ = lean_nat_dec_lt(v_i_1682_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_i_1682_);
v___x_1691_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_acc_1683_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v_e_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_e_1693_ = lean_array_fget_borrowed(v_es_1681_, v_i_1682_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = lean_nat_dec_eq(v_i_1682_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_acc_1683_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_inc(v_e_1693_);
v___x_1698_ = l_Lean_MessageData_ofExpr(v_e_1693_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___y_1685_ = v___x_1699_;
goto v___jp_1684_;
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_inc(v_e_1693_);
v___x_1700_ = l_Lean_MessageData_ofExpr(v_e_1693_);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_acc_1683_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___y_1685_ = v___x_1701_;
goto v___jp_1684_;
}
}
v___jp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v_i_1682_, v___x_1686_);
lean_dec(v_i_1682_);
v_i_1682_ = v___x_1687_;
v_acc_1683_ = v___y_1685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1702_, lean_object* v_i_1703_, lean_object* v_acc_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1702_, v_i_1703_, v_acc_1704_);
lean_dec_ref(v_es_1702_);
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1710_ = l_Lean_MessageData_ofFormat(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1714_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1711_, v___x_1712_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1715_);
lean_dec_ref(v_es_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1719_, lean_object* v_f_1720_, lean_object* v_r_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1722_ = lean_string_length(v_l_1719_);
v___x_1723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_l_1719_);
v___x_1724_ = l_Lean_MessageData_ofFormat(v___x_1723_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v_f_1720_);
v___x_1726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_r_1721_);
v___x_1727_ = l_Lean_MessageData_ofFormat(v___x_1726_);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1722_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1731_){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1733_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1734_ = l_Lean_MessageData_bracket(v___x_1732_, v_f_1731_, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1737_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1738_ = l_Lean_MessageData_bracket(v___x_1736_, v_f_1735_, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v_x_1740_);
v___x_1741_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1741_;
}
else
{
lean_object* v_tail_1742_; 
v_tail_1742_ = lean_ctor_get(v_x_1739_, 1);
if (lean_obj_tag(v_tail_1742_) == 0)
{
lean_object* v_head_1743_; 
lean_dec_ref(v_x_1740_);
v_head_1743_ = lean_ctor_get(v_x_1739_, 0);
lean_inc(v_head_1743_);
lean_dec_ref_known(v_x_1739_, 2);
return v_head_1743_;
}
else
{
lean_object* v_head_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1753_; 
lean_inc(v_tail_1742_);
v_head_1744_ = lean_ctor_get(v_x_1739_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1739_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v_x_1739_, 1);
lean_dec(v_unused_1754_);
v___x_1746_ = v_x_1739_;
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_head_1744_);
lean_dec(v_x_1739_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
lean_inc_ref(v_x_1740_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 7);
lean_ctor_set(v___x_1746_, 1, v_x_1740_);
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_head_1744_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_x_1740_);
v___x_1749_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l_Lean_MessageData_joinSep(v_tail_1742_, v_x_1740_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
return v___x_1751_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1759_ = l_Lean_MessageData_ofFormat(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1764_ = l_Lean_MessageData_ofFormat(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_box(1);
v___x_1766_ = l_Lean_MessageData_ofFormat(v___x_1765_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1768_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1773_ = l_Lean_MessageData_joinSep(v_x_1770_, v___x_1772_);
v___x_1774_ = l_Lean_MessageData_sbracket(v___x_1773_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_array_to_list(v_msgs_1775_);
v___x_1777_ = l_Lean_MessageData_ofList(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1782_ = l_Lean_MessageData_ofFormat(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1787_ = l_Lean_MessageData_ofFormat(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1792_ = l_Lean_MessageData_ofFormat(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1793_){
_start:
{
if (lean_obj_tag(v_xs_1793_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1794_;
}
else
{
lean_object* v_tail_1795_; 
v_tail_1795_ = lean_ctor_get(v_xs_1793_, 1);
lean_inc(v_tail_1795_);
if (lean_obj_tag(v_tail_1795_) == 0)
{
lean_object* v_head_1796_; 
v_head_1796_ = lean_ctor_get(v_xs_1793_, 0);
lean_inc(v_head_1796_);
lean_dec_ref_known(v_xs_1793_, 2);
return v_head_1796_;
}
else
{
lean_object* v_tail_1797_; 
v_tail_1797_ = lean_ctor_get(v_tail_1795_, 1);
if (lean_obj_tag(v_tail_1797_) == 0)
{
lean_object* v_head_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1815_; 
v_head_1798_ = lean_ctor_get(v_xs_1793_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_xs_1793_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_xs_1793_, 1);
lean_dec(v_unused_1816_);
v___x_1800_ = v_xs_1793_;
v_isShared_1801_ = v_isSharedCheck_1815_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_head_1798_);
lean_dec(v_xs_1793_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1815_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_head_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1813_; 
v_head_1802_ = lean_ctor_get(v_tail_1795_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_tail_1795_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v_tail_1795_, 1);
lean_dec(v_unused_1814_);
v___x_1804_ = v_tail_1795_;
v_isShared_1805_ = v_isSharedCheck_1813_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_head_1802_);
lean_dec(v_tail_1795_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1813_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 7);
lean_ctor_set(v___x_1804_, 1, v___x_1806_);
lean_ctor_set(v___x_1804_, 0, v_head_1798_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_head_1798_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 7);
lean_ctor_set(v___x_1800_, 1, v_head_1802_);
lean_ctor_set(v___x_1800_, 0, v___x_1808_);
v___x_1810_ = v___x_1800_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_head_1802_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
else
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1840_; 
v_isSharedCheck_1840_ = !lean_is_exclusive(v_tail_1795_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1841_ = lean_ctor_get(v_tail_1795_, 1);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_tail_1795_, 0);
lean_dec(v_unused_1842_);
v___x_1818_ = v_tail_1795_;
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_tail_1795_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1820_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1793_);
v___x_1821_ = lean_array_mk(v_xs_1793_);
v___x_1822_ = lean_array_pop(v___x_1821_);
v___x_1823_ = lean_array_to_list(v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1825_ = l_Lean_MessageData_joinSep(v___x_1823_, v___x_1824_);
v___x_1826_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 7);
lean_ctor_set(v___x_1818_, 1, v___x_1826_);
lean_ctor_set(v___x_1818_, 0, v___x_1825_);
v___x_1828_ = v___x_1818_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v___x_1829_ = l_List_getLast_x21___redArg(v___x_1820_, v_xs_1793_);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_xs_1793_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1837_ = lean_ctor_get(v_xs_1793_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_xs_1793_, 0);
lean_dec(v_unused_1838_);
v___x_1831_ = v_xs_1793_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_xs_1793_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 7);
lean_ctor_set(v___x_1831_, 1, v___x_1829_);
lean_ctor_set(v___x_1831_, 0, v___x_1828_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
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
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1852_ = l_Lean_MessageData_ofFormat(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1853_){
_start:
{
if (lean_obj_tag(v_xs_1853_) == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1854_;
}
else
{
lean_object* v_tail_1855_; 
v_tail_1855_ = lean_ctor_get(v_xs_1853_, 1);
lean_inc(v_tail_1855_);
if (lean_obj_tag(v_tail_1855_) == 0)
{
lean_object* v_head_1856_; 
v_head_1856_ = lean_ctor_get(v_xs_1853_, 0);
lean_inc(v_head_1856_);
lean_dec_ref_known(v_xs_1853_, 2);
return v_head_1856_;
}
else
{
lean_object* v_tail_1857_; 
v_tail_1857_ = lean_ctor_get(v_tail_1855_, 1);
if (lean_obj_tag(v_tail_1857_) == 0)
{
lean_object* v_head_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1875_; 
v_head_1858_ = lean_ctor_get(v_xs_1853_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_xs_1853_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_xs_1853_, 1);
lean_dec(v_unused_1876_);
v___x_1860_ = v_xs_1853_;
v_isShared_1861_ = v_isSharedCheck_1875_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_head_1858_);
lean_dec(v_xs_1853_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1875_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_head_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1873_; 
v_head_1862_ = lean_ctor_get(v_tail_1855_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_tail_1855_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_tail_1855_, 1);
lean_dec(v_unused_1874_);
v___x_1864_ = v_tail_1855_;
v_isShared_1865_ = v_isSharedCheck_1873_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_head_1862_);
lean_dec(v_tail_1855_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1873_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 7);
lean_ctor_set(v___x_1864_, 1, v___x_1866_);
lean_ctor_set(v___x_1864_, 0, v_head_1858_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_head_1858_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 7);
lean_ctor_set(v___x_1860_, 1, v_head_1862_);
lean_ctor_set(v___x_1860_, 0, v___x_1868_);
v___x_1870_ = v___x_1860_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_head_1862_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
else
{
lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1900_; 
v_isSharedCheck_1900_ = !lean_is_exclusive(v_tail_1855_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1901_ = lean_ctor_get(v_tail_1855_, 1);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_tail_1855_, 0);
lean_dec(v_unused_1902_);
v___x_1878_ = v_tail_1855_;
v_isShared_1879_ = v_isSharedCheck_1900_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_tail_1855_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1900_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1880_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1853_);
v___x_1881_ = lean_array_mk(v_xs_1853_);
v___x_1882_ = lean_array_pop(v___x_1881_);
v___x_1883_ = lean_array_to_list(v___x_1882_);
v___x_1884_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1885_ = l_Lean_MessageData_joinSep(v___x_1883_, v___x_1884_);
v___x_1886_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 7);
lean_ctor_set(v___x_1878_, 1, v___x_1886_);
lean_ctor_set(v___x_1878_, 0, v___x_1885_);
v___x_1888_ = v___x_1878_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v___x_1889_ = l_List_getLast_x21___redArg(v___x_1880_, v_xs_1853_);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_xs_1853_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; lean_object* v_unused_1898_; 
v_unused_1897_ = lean_ctor_get(v_xs_1853_, 1);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_xs_1853_, 0);
lean_dec(v_unused_1898_);
v___x_1891_ = v_xs_1853_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v_xs_1853_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 7);
lean_ctor_set(v___x_1891_, 1, v___x_1889_);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
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
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_1909_ = l_Lean_MessageData_ofFormat(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_1911_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___x_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_note_1913_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_1920_ = l_Lean_MessageData_ofFormat(v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_1922_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v_hint_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1930_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_1931_ = lean_box(0);
v___x_1932_ = l_List_mapTR_loop___redArg(v___x_1930_, v_es_1929_, v___x_1931_);
v___x_1933_ = l_Lean_MessageData_ofList(v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1937_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_1938_ = l_Lean_instInhabitedPosition_default;
v___x_1939_ = lean_box(0);
v___x_1940_ = 0;
v___x_1941_ = 2;
v___x_1942_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1942_, 0, v___x_1937_);
lean_ctor_set(v___x_1942_, 1, v___x_1938_);
lean_ctor_set(v___x_1942_, 2, v___x_1939_);
lean_ctor_set(v___x_1942_, 3, v___x_1937_);
lean_ctor_set(v___x_1942_, 4, v_inst_1936_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*5, v___x_1940_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*5 + 1, v___x_1941_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*5 + 2, v___x_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_1948_, lean_object* v_inst_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v_fileName_1965_; lean_object* v_pos_1966_; lean_object* v_endPos_1967_; uint8_t v_keepFullRange_1968_; uint8_t v_severity_1969_; uint8_t v_isSilent_1970_; lean_object* v_caption_1971_; lean_object* v_data_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_fileName_1965_ = lean_ctor_get(v_x_1964_, 0);
lean_inc_ref(v_fileName_1965_);
v_pos_1966_ = lean_ctor_get(v_x_1964_, 1);
lean_inc_ref(v_pos_1966_);
v_endPos_1967_ = lean_ctor_get(v_x_1964_, 2);
lean_inc(v_endPos_1967_);
v_keepFullRange_1968_ = lean_ctor_get_uint8(v_x_1964_, sizeof(void*)*5);
v_severity_1969_ = lean_ctor_get_uint8(v_x_1964_, sizeof(void*)*5 + 1);
v_isSilent_1970_ = lean_ctor_get_uint8(v_x_1964_, sizeof(void*)*5 + 2);
v_caption_1971_ = lean_ctor_get(v_x_1964_, 3);
lean_inc_ref(v_caption_1971_);
v_data_1972_ = lean_ctor_get(v_x_1964_, 4);
lean_inc(v_data_1972_);
lean_dec_ref(v_x_1964_);
v___x_1973_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_1974_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_fileName_1965_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1980_ = l_Lean_instToJsonPosition_toJson(v_pos_1966_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1977_);
v___x_1983_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1984_ = l_Option_toJson___redArg(v___x_1973_, v_endPos_1967_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set(v___x_1986_, 1, v___x_1977_);
v___x_1987_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1988_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1988_, 0, v_keepFullRange_1968_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1977_);
v___x_1991_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1992_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1969_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1977_);
v___x_1995_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1996_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1996_, 0, v_isSilent_1970_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___x_1977_);
v___x_1999_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_caption_1971_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_1977_);
v___x_2003_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2004_ = lean_apply_1(v_inst_1963_, v_data_1972_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_1977_);
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_1977_);
v___x_2008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2002_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_1998_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_1994_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_1990_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_1986_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_1982_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_1978_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2016_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2017_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2015_, v___x_2014_, v___x_2016_);
v___x_2018_ = l_Lean_Json_mkObj(v___x_2017_);
lean_dec(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2019_, lean_object* v_inst_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2020_, v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2024_, 0, lean_box(0));
lean_closure_set(v___x_2024_, 1, v_inst_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2025_, lean_object* v_inst_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2027_, 0, lean_box(0));
lean_closure_set(v___x_2027_, 1, v_inst_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = 1;
v___x_2034_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2034_, v___x_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2038_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2039_ = lean_string_append(v___x_2038_, v___x_2037_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = 1;
v___x_2043_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2043_, v___x_2042_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2046_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2047_ = lean_string_append(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2050_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2051_ = lean_string_append(v___x_2050_, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = 1;
v___x_2058_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2059_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2058_, v___x_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2061_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2062_ = lean_string_append(v___x_2061_, v___x_2060_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2064_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2065_ = lean_string_append(v___x_2064_, v___x_2063_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = 1;
v___x_2069_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2070_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2072_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2073_ = lean_string_append(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2075_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2076_ = lean_string_append(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = 1;
v___x_2081_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2082_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2084_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2085_ = lean_string_append(v___x_2084_, v___x_2083_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2087_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2088_ = lean_string_append(v___x_2087_, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = 1;
v___x_2092_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2095_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2096_ = lean_string_append(v___x_2095_, v___x_2094_);
return v___x_2096_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2098_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2099_ = lean_string_append(v___x_2098_, v___x_2097_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = 1;
v___x_2103_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2104_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2103_, v___x_2102_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2106_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2107_ = lean_string_append(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2109_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2110_ = lean_string_append(v___x_2109_, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = 1;
v___x_2114_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2114_, v___x_2113_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2117_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2118_ = lean_string_append(v___x_2117_, v___x_2116_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2120_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2121_ = lean_string_append(v___x_2120_, v___x_2119_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = 1;
v___x_2125_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2125_, v___x_2124_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2128_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2129_ = lean_string_append(v___x_2128_, v___x_2127_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2131_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2132_ = lean_string_append(v___x_2131_, v___x_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2133_, lean_object* v_json_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2136_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2134_);
v___x_2137_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2135_, v___x_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2142_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2143_ = lean_string_append(v___x_2142_, v_a_2138_);
lean_dec(v_a_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2143_);
v___x_2145_ = v___x_2140_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2148_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2137_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2137_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 0);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2156_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2157_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2158_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2159_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2134_);
v___x_2160_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2157_, v___x_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
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
v___x_2165_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
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
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
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
lean_dec_ref_known(v___x_2160_, 1);
v___x_2180_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2134_);
v___x_2181_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2158_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
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
v___x_2186_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
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
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
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
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2201_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2202_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2134_);
v___x_2203_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2201_, v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2208_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2209_ = lean_string_append(v___x_2208_, v_a_2204_);
lean_dec(v_a_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2209_);
v___x_2211_ = v___x_2206_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2214_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2203_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2203_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 0);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2223_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2224_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2134_);
v___x_2225_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2223_, v___x_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2231_ = lean_string_append(v___x_2230_, v_a_2226_);
lean_dec(v_a_2226_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2236_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2225_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2225_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 0);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2245_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2134_);
v___x_2246_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2201_, v___x_2245_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2251_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2252_ = lean_string_append(v___x_2251_, v_a_2247_);
lean_dec(v_a_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2252_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2257_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2246_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2246_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 0);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_a_2265_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2266_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2134_);
v___x_2267_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v___x_2135_, v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2265_);
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2277_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2277_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2272_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2273_ = lean_string_append(v___x_2272_, v_a_2268_);
lean_dec(v_a_2268_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2273_);
v___x_2275_ = v___x_2270_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2265_);
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
lean_dec(v_json_2134_);
lean_dec_ref(v_inst_2133_);
v_a_2278_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2267_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2267_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 0);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2287_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2288_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2134_, v_inst_2133_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2265_);
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2293_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2294_ = lean_string_append(v___x_2293_, v_a_2289_);
lean_dec(v_a_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2265_);
lean_dec(v_a_2244_);
lean_dec(v_a_2222_);
lean_dec(v_a_2200_);
lean_dec(v_a_2179_);
lean_dec(v_a_2156_);
v_a_2299_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2288_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2288_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 0);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2318_; 
v_a_2307_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2309_ = v___x_2288_;
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2288_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; uint8_t v___x_2312_; uint8_t v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2316_; 
v___x_2311_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2311_, 0, v_a_2156_);
lean_ctor_set(v___x_2311_, 1, v_a_2179_);
lean_ctor_set(v___x_2311_, 2, v_a_2200_);
lean_ctor_set(v___x_2311_, 3, v_a_2286_);
lean_ctor_set(v___x_2311_, 4, v_a_2307_);
v___x_2312_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*5, v___x_2312_);
v___x_2313_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*5 + 1, v___x_2313_);
v___x_2314_ = lean_unbox(v_a_2265_);
lean_dec(v_a_2265_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*5 + 2, v___x_2314_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2316_ = v___x_2309_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2319_, lean_object* v_inst_2320_, lean_object* v_json_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2320_, v_json_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2324_, 0, lean_box(0));
lean_closure_set(v___x_2324_, 1, v_inst_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2325_, lean_object* v_inst_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2327_, 0, lean_box(0));
lean_closure_set(v___x_2327_, 1, v_inst_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2328_){
_start:
{
if (lean_obj_tag(v_x_2328_) == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_box(0);
return v___x_2329_;
}
else
{
lean_object* v_val_2330_; lean_object* v___x_2331_; 
v_val_2330_ = lean_ctor_get(v_x_2328_, 0);
lean_inc(v_val_2330_);
lean_dec_ref_known(v_x_2328_, 1);
v___x_2331_ = l_Lean_instToJsonPosition_toJson(v_val_2330_);
return v___x_2331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
if (lean_obj_tag(v_a_2332_) == 0)
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_array_to_list(v_a_2333_);
return v___x_2334_;
}
else
{
lean_object* v_head_2335_; lean_object* v_tail_2336_; lean_object* v___x_2337_; 
v_head_2335_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_head_2335_);
v_tail_2336_ = lean_ctor_get(v_a_2332_, 1);
lean_inc(v_tail_2336_);
lean_dec_ref_known(v_a_2332_, 2);
v___x_2337_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2333_, v_head_2335_);
v_a_2332_ = v_tail_2336_;
v_a_2333_ = v___x_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2340_){
_start:
{
lean_object* v_toBaseMessage_2341_; lean_object* v_kind_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2407_; 
v_toBaseMessage_2341_ = lean_ctor_get(v_x_2340_, 0);
v_kind_2342_ = lean_ctor_get(v_x_2340_, 1);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_x_2340_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2344_ = v_x_2340_;
v_isShared_2345_ = v_isSharedCheck_2407_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_kind_2342_);
lean_inc(v_toBaseMessage_2341_);
lean_dec(v_x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2407_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_fileName_2346_; lean_object* v_pos_2347_; lean_object* v_endPos_2348_; uint8_t v_keepFullRange_2349_; uint8_t v_severity_2350_; uint8_t v_isSilent_2351_; lean_object* v_caption_2352_; lean_object* v_data_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v_fileName_2346_ = lean_ctor_get(v_toBaseMessage_2341_, 0);
lean_inc_ref(v_fileName_2346_);
v_pos_2347_ = lean_ctor_get(v_toBaseMessage_2341_, 1);
lean_inc_ref(v_pos_2347_);
v_endPos_2348_ = lean_ctor_get(v_toBaseMessage_2341_, 2);
lean_inc(v_endPos_2348_);
v_keepFullRange_2349_ = lean_ctor_get_uint8(v_toBaseMessage_2341_, sizeof(void*)*5);
v_severity_2350_ = lean_ctor_get_uint8(v_toBaseMessage_2341_, sizeof(void*)*5 + 1);
v_isSilent_2351_ = lean_ctor_get_uint8(v_toBaseMessage_2341_, sizeof(void*)*5 + 2);
v_caption_2352_ = lean_ctor_get(v_toBaseMessage_2341_, 3);
lean_inc_ref(v_caption_2352_);
v_data_2353_ = lean_ctor_get(v_toBaseMessage_2341_, 4);
lean_inc(v_data_2353_);
lean_dec_ref(v_toBaseMessage_2341_);
v___x_2354_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_fileName_2346_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___x_2355_);
lean_ctor_set(v___x_2344_, 0, v___x_2354_);
v___x_2357_ = v___x_2344_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2361_ = l_Lean_instToJsonPosition_toJson(v_pos_2347_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2358_);
v___x_2364_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2365_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2348_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v___x_2358_);
v___x_2368_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2369_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2369_, 0, v_keepFullRange_2349_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2358_);
v___x_2372_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2373_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2350_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2358_);
v___x_2376_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2377_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2377_, 0, v_isSilent_2351_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___x_2358_);
v___x_2380_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_caption_2352_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2358_);
v___x_2384_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_data_2353_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2358_);
v___x_2388_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2389_ = 1;
v___x_2390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2342_, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2388_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v___x_2358_);
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___x_2358_);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2387_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2383_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2379_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2375_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2371_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2367_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2363_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2359_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2404_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2402_, v___x_2403_);
v___x_2405_ = l_Lean_Json_mkObj(v___x_2404_);
lean_dec(v___x_2404_);
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2410_, lean_object* v_k_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = l_Lean_Json_getObjValD(v_j_2410_, v_k_2411_);
v___x_2413_ = l_Lean_Json_getStr_x3f(v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2414_, lean_object* v_k_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2414_, v_k_2415_);
lean_dec_ref(v_k_2415_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2417_, lean_object* v_k_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = l_Lean_Json_getObjValD(v_j_2417_, v_k_2418_);
v___x_2420_ = l_Lean_instFromJsonPosition_fromJson(v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2421_, lean_object* v_k_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2421_, v_k_2422_);
lean_dec_ref(v_k_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2424_, lean_object* v_k_2425_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = l_Lean_Json_getObjValD(v_j_2424_, v_k_2425_);
v___x_2427_ = l_Lean_Json_getBool_x3f(v___x_2426_);
lean_dec(v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2428_, lean_object* v_k_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2428_, v_k_2429_);
lean_dec_ref(v_k_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2431_, lean_object* v_k_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = l_Lean_Json_getObjValD(v_j_2431_, v_k_2432_);
v___x_2434_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2435_, lean_object* v_k_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2435_, v_k_2436_);
lean_dec_ref(v_k_2436_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2438_, lean_object* v_k_2439_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = l_Lean_Json_getObjValD(v_j_2438_, v_k_2439_);
v___x_2441_ = l_Lean_Name_fromJson_x3f(v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2442_, lean_object* v_k_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2442_, v_k_2443_);
lean_dec_ref(v_k_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2447_) == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_instFromJsonPosition_fromJson(v_x_2447_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_a_2458_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = l_Lean_Json_getObjValD(v_j_2467_, v_k_2468_);
v___x_2470_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2471_, lean_object* v_k_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2471_, v_k_2472_);
lean_dec_ref(v_k_2472_);
return v_res_2473_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = 1;
v___x_2479_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2479_, v___x_2478_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2482_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2483_ = lean_string_append(v___x_2482_, v___x_2481_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2485_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2486_ = lean_string_append(v___x_2485_, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2488_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2489_ = lean_string_append(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2491_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2492_ = lean_string_append(v___x_2491_, v___x_2490_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2494_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2495_ = lean_string_append(v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2497_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2498_ = lean_string_append(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2500_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2501_ = lean_string_append(v___x_2500_, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2503_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2504_ = lean_string_append(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2506_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2507_ = lean_string_append(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2509_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2510_ = lean_string_append(v___x_2509_, v___x_2508_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2512_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2513_ = lean_string_append(v___x_2512_, v___x_2511_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2515_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2516_ = lean_string_append(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2518_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2519_ = lean_string_append(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2521_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2522_ = lean_string_append(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2524_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2525_ = lean_string_append(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2527_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2528_ = lean_string_append(v___x_2527_, v___x_2526_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2530_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2531_ = lean_string_append(v___x_2530_, v___x_2529_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = 1;
v___x_2535_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2538_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2539_ = lean_string_append(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2541_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2542_ = lean_string_append(v___x_2541_, v___x_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2543_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2543_);
v___x_2545_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2543_, v___x_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_json_2543_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2550_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2551_ = lean_string_append(v___x_2550_, v_a_2546_);
lean_dec(v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_json_2543_);
v_a_2556_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2545_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2545_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 0);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_a_2564_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2565_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2543_);
v___x_2566_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2543_, v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2576_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2576_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2571_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2572_ = lean_string_append(v___x_2571_, v_a_2567_);
lean_dec(v_a_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2572_);
v___x_2574_ = v___x_2569_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2577_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2566_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2566_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 0);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_a_2585_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2586_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2543_);
v___x_2587_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2543_, v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2592_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2593_ = lean_string_append(v___x_2592_, v_a_2588_);
lean_dec(v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2593_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2598_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2587_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2587_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 0);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2606_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2607_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2543_);
v___x_2608_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2543_, v___x_2607_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2613_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2614_ = lean_string_append(v___x_2613_, v_a_2609_);
lean_dec(v_a_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2614_);
v___x_2616_ = v___x_2611_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2619_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2608_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2608_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 0);
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_a_2627_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2628_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2543_);
v___x_2629_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2543_, v___x_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2634_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2635_ = lean_string_append(v___x_2634_, v_a_2630_);
lean_dec(v_a_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___x_2635_);
v___x_2637_ = v___x_2632_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
else
{
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2640_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2629_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2629_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 0);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2649_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2543_);
v___x_2650_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2543_, v___x_2649_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2655_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2656_ = lean_string_append(v___x_2655_, v_a_2651_);
lean_dec(v_a_2651_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2656_);
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2661_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2650_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2650_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
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
v_a_2669_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2670_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2543_);
v___x_2671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2543_, v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
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
v___x_2676_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
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
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2682_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2671_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2671_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 0);
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2690_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2691_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2543_);
v___x_2692_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2543_, v___x_2691_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2690_);
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2702_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2702_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2697_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2698_ = lean_string_append(v___x_2697_, v_a_2693_);
lean_dec(v_a_2693_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2698_);
v___x_2700_ = v___x_2695_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2690_);
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
lean_dec(v_json_2543_);
v_a_2703_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2692_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2692_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 0);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_a_2711_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2712_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2713_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2543_, v___x_2712_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2690_);
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2723_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2723_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2718_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2719_ = lean_string_append(v___x_2718_, v_a_2714_);
lean_dec(v_a_2714_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2719_);
v___x_2721_ = v___x_2716_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
else
{
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2690_);
lean_dec(v_a_2669_);
lean_dec(v_a_2648_);
lean_dec(v_a_2627_);
lean_dec(v_a_2606_);
lean_dec(v_a_2585_);
lean_dec(v_a_2564_);
v_a_2724_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2713_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2713_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 0);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2744_; 
v_a_2732_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2734_ = v___x_2713_;
v_isShared_2735_ = v_isSharedCheck_2744_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2713_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2744_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; uint8_t v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2736_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2736_, 0, v_a_2564_);
lean_ctor_set(v___x_2736_, 1, v_a_2585_);
lean_ctor_set(v___x_2736_, 2, v_a_2606_);
lean_ctor_set(v___x_2736_, 3, v_a_2690_);
lean_ctor_set(v___x_2736_, 4, v_a_2711_);
v___x_2737_ = lean_unbox(v_a_2627_);
lean_dec(v_a_2627_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*5, v___x_2737_);
v___x_2738_ = lean_unbox(v_a_2648_);
lean_dec(v_a_2648_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*5 + 1, v___x_2738_);
v___x_2739_ = lean_unbox(v_a_2669_);
lean_dec(v_a_2669_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*5 + 2, v___x_2739_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2736_);
lean_ctor_set(v___x_2740_, 1, v_a_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2740_);
v___x_2742_ = v___x_2734_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2751_ = l_Lean_Name_str___override(v_errorName_2749_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2752_, lean_object* v_name_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = l_Lean_kindOfErrorName(v_name_2753_);
v___x_2755_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_msg_2752_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2757_){
_start:
{
switch(lean_obj_tag(v_a_2757_))
{
case 0:
{
return v_a_2757_;
}
case 1:
{
lean_object* v_pre_2758_; lean_object* v_str_2759_; lean_object* v_p_x27_2760_; uint8_t v___y_2762_; uint8_t v___x_2765_; 
v_pre_2758_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_pre_2758_);
v_str_2759_ = lean_ctor_get(v_a_2757_, 1);
lean_inc_ref(v_str_2759_);
lean_dec_ref_known(v_a_2757_, 2);
v_p_x27_2760_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2758_);
v___x_2765_ = l_Lean_Name_isAnonymous(v_p_x27_2760_);
if (v___x_2765_ == 0)
{
v___y_2762_ = v___x_2765_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2767_ = lean_string_dec_eq(v_str_2759_, v___x_2766_);
v___y_2762_ = v___x_2767_;
goto v___jp_2761_;
}
v___jp_2761_:
{
if (v___y_2762_ == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Name_str___override(v_p_x27_2760_, v_str_2759_);
return v___x_2763_;
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_p_x27_2760_);
lean_dec_ref(v_str_2759_);
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
}
}
default: 
{
lean_object* v_pre_2768_; lean_object* v_i_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_pre_2768_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_pre_2768_);
v_i_2769_ = lean_ctor_get(v_a_2757_, 1);
lean_inc(v_i_2769_);
lean_dec_ref_known(v_a_2757_, 2);
v___x_2770_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2768_);
v___x_2771_ = l_Lean_Name_num___override(v___x_2770_, v_i_2769_);
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2772_){
_start:
{
switch(lean_obj_tag(v_x_2772_))
{
case 3:
{
lean_object* v_a_2773_; lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2782_; 
v_a_2773_ = lean_ctor_get(v_x_2772_, 0);
v_a_2774_ = lean_ctor_get(v_x_2772_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_x_2772_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2776_ = v_x_2772_;
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_inc(v_a_2773_);
lean_dec(v_x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2778_ = l_Lean_MessageData_stripNestedTags(v_a_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2778_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2773_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
case 4:
{
lean_object* v_a_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2792_; 
v_a_2783_ = lean_ctor_get(v_x_2772_, 0);
v_a_2784_ = lean_ctor_get(v_x_2772_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_x_2772_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2786_ = v_x_2772_;
v_isShared_2787_ = v_isSharedCheck_2792_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_inc(v_a_2783_);
lean_dec(v_x_2772_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2792_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = l_Lean_MessageData_stripNestedTags(v_a_2784_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 1, v___x_2788_);
v___x_2790_ = v___x_2786_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
case 8:
{
lean_object* v_a_2793_; lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2802_; 
v_a_2793_ = lean_ctor_get(v_x_2772_, 0);
v_a_2794_ = lean_ctor_get(v_x_2772_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_x_2772_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2796_ = v_x_2772_;
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_inc(v_a_2793_);
lean_dec(v_x_2772_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2793_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2798_);
v___x_2800_ = v___x_2796_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_a_2794_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
default: 
{
return v_x_2772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 1)
{
lean_object* v_pre_2804_; lean_object* v_str_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_pre_2804_ = lean_ctor_get(v_x_2803_, 0);
v_str_2805_ = lean_ctor_get(v_x_2803_, 1);
v___x_2806_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2807_ = lean_string_dec_eq(v_str_2805_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_box(0);
return v___x_2808_;
}
else
{
lean_object* v___x_2809_; 
lean_inc(v_pre_2804_);
v___x_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_pre_2804_);
return v___x_2809_;
}
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_box(0);
return v___x_2810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_errorNameOfKind_x3f(v_x_2811_);
lean_dec(v_x_2811_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = l_Lean_MessageData_kind(v_msg_2813_);
v___x_2815_ = l_Lean_errorNameOfKind_x3f(v___x_2814_);
lean_dec(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_MessageData_errorName_x3f(v_msg_2816_);
lean_dec_ref(v_msg_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2818_){
_start:
{
lean_object* v_data_2819_; lean_object* v___x_2820_; 
v_data_2819_ = lean_ctor_get(v_msg_2818_, 4);
v___x_2820_ = l_Lean_MessageData_errorName_x3f(v_data_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Message_errorName_x3f(v_msg_2821_);
lean_dec_ref(v_msg_2821_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2823_){
_start:
{
lean_object* v_toBaseMessage_2824_; lean_object* v_fileName_2825_; lean_object* v_pos_2826_; lean_object* v_endPos_2827_; uint8_t v_keepFullRange_2828_; uint8_t v_severity_2829_; uint8_t v_isSilent_2830_; lean_object* v_caption_2831_; lean_object* v_data_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2841_; 
v_toBaseMessage_2824_ = lean_ctor_get(v_msg_2823_, 0);
lean_inc_ref(v_toBaseMessage_2824_);
lean_dec_ref(v_msg_2823_);
v_fileName_2825_ = lean_ctor_get(v_toBaseMessage_2824_, 0);
v_pos_2826_ = lean_ctor_get(v_toBaseMessage_2824_, 1);
v_endPos_2827_ = lean_ctor_get(v_toBaseMessage_2824_, 2);
v_keepFullRange_2828_ = lean_ctor_get_uint8(v_toBaseMessage_2824_, sizeof(void*)*5);
v_severity_2829_ = lean_ctor_get_uint8(v_toBaseMessage_2824_, sizeof(void*)*5 + 1);
v_isSilent_2830_ = lean_ctor_get_uint8(v_toBaseMessage_2824_, sizeof(void*)*5 + 2);
v_caption_2831_ = lean_ctor_get(v_toBaseMessage_2824_, 3);
v_data_2832_ = lean_ctor_get(v_toBaseMessage_2824_, 4);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_toBaseMessage_2824_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2834_ = v_toBaseMessage_2824_;
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_data_2832_);
lean_inc(v_caption_2831_);
lean_inc(v_endPos_2827_);
lean_inc(v_pos_2826_);
lean_inc(v_fileName_2825_);
lean_dec(v_toBaseMessage_2824_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2841_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_data_2832_);
v___x_2837_ = l_Lean_MessageData_ofFormat(v___x_2836_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 4, v___x_2837_);
v___x_2839_ = v___x_2834_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_fileName_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_pos_2826_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_endPos_2827_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_caption_2831_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___x_2837_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*5, v_keepFullRange_2828_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*5 + 1, v_severity_2829_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*5 + 2, v_isSilent_2830_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2847_, uint8_t v_includeEndPos_2848_){
_start:
{
lean_object* v___y_2850_; lean_object* v___y_2854_; uint8_t v___y_2855_; uint32_t v___y_2856_; lean_object* v_str_2860_; lean_object* v_toBaseMessage_2872_; lean_object* v_kind_2873_; lean_object* v_fileName_2874_; lean_object* v_pos_2875_; lean_object* v_endPos_2876_; uint8_t v_severity_2877_; lean_object* v_caption_2878_; lean_object* v_data_2879_; lean_object* v___y_2881_; lean_object* v_str_2882_; lean_object* v___y_2890_; 
v_toBaseMessage_2872_ = lean_ctor_get(v_msg_2847_, 0);
lean_inc_ref(v_toBaseMessage_2872_);
v_kind_2873_ = lean_ctor_get(v_msg_2847_, 1);
lean_inc(v_kind_2873_);
lean_dec_ref(v_msg_2847_);
v_fileName_2874_ = lean_ctor_get(v_toBaseMessage_2872_, 0);
lean_inc_ref(v_fileName_2874_);
v_pos_2875_ = lean_ctor_get(v_toBaseMessage_2872_, 1);
lean_inc_ref(v_pos_2875_);
v_endPos_2876_ = lean_ctor_get(v_toBaseMessage_2872_, 2);
lean_inc(v_endPos_2876_);
v_severity_2877_ = lean_ctor_get_uint8(v_toBaseMessage_2872_, sizeof(void*)*5 + 1);
v_caption_2878_ = lean_ctor_get(v_toBaseMessage_2872_, 3);
lean_inc_ref(v_caption_2878_);
v_data_2879_ = lean_ctor_get(v_toBaseMessage_2872_, 4);
lean_inc(v_data_2879_);
lean_dec_ref(v_toBaseMessage_2872_);
if (v_includeEndPos_2848_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_endPos_2876_);
v___x_2896_ = lean_box(0);
v___y_2890_ = v___x_2896_;
goto v___jp_2889_;
}
else
{
v___y_2890_ = v_endPos_2876_;
goto v___jp_2889_;
}
v___jp_2849_:
{
lean_object* v___x_2851_; lean_object* v_str_2852_; 
v___x_2851_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2852_ = lean_string_append(v___y_2850_, v___x_2851_);
return v_str_2852_;
}
v___jp_2853_:
{
uint32_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = 10;
v___x_2858_ = lean_uint32_dec_eq(v___y_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
v___y_2850_ = v___y_2854_;
goto v___jp_2849_;
}
else
{
if (v___y_2855_ == 0)
{
return v___y_2854_;
}
else
{
v___y_2850_ = v___y_2854_;
goto v___jp_2849_;
}
}
}
v___jp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = lean_string_utf8_byte_size(v_str_2860_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_nat_dec_eq(v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_inc_ref(v_str_2860_);
v___x_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2864_, 0, v_str_2860_);
lean_ctor_set(v___x_2864_, 1, v___x_2862_);
lean_ctor_set(v___x_2864_, 2, v___x_2861_);
v___x_2865_ = l_String_Slice_Pos_prev_x3f(v___x_2864_, v___x_2861_);
if (lean_obj_tag(v___x_2865_) == 0)
{
uint32_t v___x_2866_; 
lean_dec_ref_known(v___x_2864_, 3);
v___x_2866_ = 65;
v___y_2854_ = v_str_2860_;
v___y_2855_ = v___x_2863_;
v___y_2856_ = v___x_2866_;
goto v___jp_2853_;
}
else
{
lean_object* v_val_2867_; lean_object* v___x_2868_; 
v_val_2867_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2868_ = l_String_Slice_Pos_get_x3f(v___x_2864_, v_val_2867_);
lean_dec(v_val_2867_);
lean_dec_ref_known(v___x_2864_, 3);
if (lean_obj_tag(v___x_2868_) == 0)
{
uint32_t v___x_2869_; 
v___x_2869_ = 65;
v___y_2854_ = v_str_2860_;
v___y_2855_ = v___x_2863_;
v___y_2856_ = v___x_2869_;
goto v___jp_2853_;
}
else
{
lean_object* v_val_2870_; uint32_t v___x_2871_; 
v_val_2870_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_val_2870_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2871_ = lean_unbox_uint32(v_val_2870_);
lean_dec(v_val_2870_);
v___y_2854_ = v_str_2860_;
v___y_2855_ = v___x_2863_;
v___y_2856_ = v___x_2871_;
goto v___jp_2853_;
}
}
}
else
{
v___y_2850_ = v_str_2860_;
goto v___jp_2849_;
}
}
v___jp_2880_:
{
switch(v_severity_2877_)
{
case 0:
{
lean_dec(v___y_2881_);
lean_dec_ref(v_pos_2875_);
lean_dec_ref(v_fileName_2874_);
lean_dec(v_kind_2873_);
v_str_2860_ = v_str_2882_;
goto v___jp_2859_;
}
case 1:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v_str_2885_; 
v___x_2883_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2884_ = l_Lean_errorNameOfKind_x3f(v_kind_2873_);
lean_dec(v_kind_2873_);
v_str_2885_ = l_Lean_mkErrorStringWithPos(v_fileName_2874_, v_pos_2875_, v_str_2882_, v___y_2881_, v___x_2883_, v___x_2884_);
lean_dec_ref(v_str_2882_);
v_str_2860_ = v_str_2885_;
goto v___jp_2859_;
}
default: 
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v_str_2888_; 
v___x_2886_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2887_ = l_Lean_errorNameOfKind_x3f(v_kind_2873_);
lean_dec(v_kind_2873_);
v_str_2888_ = l_Lean_mkErrorStringWithPos(v_fileName_2874_, v_pos_2875_, v_str_2882_, v___y_2881_, v___x_2886_, v___x_2887_);
lean_dec_ref(v_str_2882_);
v_str_2860_ = v_str_2888_;
goto v___jp_2859_;
}
}
}
v___jp_2889_:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2892_ = lean_string_dec_eq(v_caption_2878_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v_str_2895_; 
v___x_2893_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2894_ = lean_string_append(v_caption_2878_, v___x_2893_);
v_str_2895_ = lean_string_append(v___x_2894_, v_data_2879_);
lean_dec(v_data_2879_);
v___y_2881_ = v___y_2890_;
v_str_2882_ = v_str_2895_;
goto v___jp_2880_;
}
else
{
lean_dec_ref(v_caption_2878_);
v___y_2881_ = v___y_2890_;
v_str_2882_ = v_data_2879_;
goto v___jp_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2897_, lean_object* v_includeEndPos_2898_){
_start:
{
uint8_t v_includeEndPos_boxed_2899_; lean_object* v_res_2900_; 
v_includeEndPos_boxed_2899_ = lean_unbox(v_includeEndPos_2898_);
v_res_2900_ = l_Lean_SerialMessage_toString(v_msg_2897_, v_includeEndPos_boxed_2899_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2901_){
_start:
{
uint8_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = 0;
v___x_2903_ = l_Lean_SerialMessage_toString(v_msg_2901_, v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2906_){
_start:
{
lean_object* v_data_2907_; lean_object* v___x_2908_; 
v_data_2907_ = lean_ctor_get(v_msg_2906_, 4);
v___x_2908_ = l_Lean_MessageData_kind(v_data_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_Message_kind(v_msg_2909_);
lean_dec_ref(v_msg_2909_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2911_){
_start:
{
lean_object* v_data_2912_; uint8_t v___x_2913_; 
v_data_2912_ = lean_ctor_get(v_msg_2911_, 4);
v___x_2913_ = l_Lean_MessageData_isTrace(v_data_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2914_){
_start:
{
uint8_t v_res_2915_; lean_object* v_r_2916_; 
v_res_2915_ = l_Lean_Message_isTrace(v_msg_2914_);
lean_dec_ref(v_msg_2914_);
v_r_2916_ = lean_box(v_res_2915_);
return v_r_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2917_){
_start:
{
lean_object* v_fileName_2919_; lean_object* v_pos_2920_; lean_object* v_endPos_2921_; uint8_t v_keepFullRange_2922_; uint8_t v_severity_2923_; uint8_t v_isSilent_2924_; lean_object* v_caption_2925_; lean_object* v_data_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2936_; 
v_fileName_2919_ = lean_ctor_get(v_msg_2917_, 0);
v_pos_2920_ = lean_ctor_get(v_msg_2917_, 1);
v_endPos_2921_ = lean_ctor_get(v_msg_2917_, 2);
v_keepFullRange_2922_ = lean_ctor_get_uint8(v_msg_2917_, sizeof(void*)*5);
v_severity_2923_ = lean_ctor_get_uint8(v_msg_2917_, sizeof(void*)*5 + 1);
v_isSilent_2924_ = lean_ctor_get_uint8(v_msg_2917_, sizeof(void*)*5 + 2);
v_caption_2925_ = lean_ctor_get(v_msg_2917_, 3);
v_data_2926_ = lean_ctor_get(v_msg_2917_, 4);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_msg_2917_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2928_ = v_msg_2917_;
v_isShared_2929_ = v_isSharedCheck_2936_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_data_2926_);
lean_inc(v_caption_2925_);
lean_inc(v_endPos_2921_);
lean_inc(v_pos_2920_);
lean_inc(v_fileName_2919_);
lean_dec(v_msg_2917_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2936_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
lean_inc(v_data_2926_);
v___x_2930_ = l_Lean_MessageData_toString(v_data_2926_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 4, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_fileName_2919_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_pos_2920_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_endPos_2921_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_caption_2925_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v___x_2930_);
lean_ctor_set_uint8(v_reuseFailAlloc_2935_, sizeof(void*)*5, v_keepFullRange_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_2935_, sizeof(void*)*5 + 1, v_severity_2923_);
lean_ctor_set_uint8(v_reuseFailAlloc_2935_, sizeof(void*)*5 + 2, v_isSilent_2924_);
v___x_2932_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = l_Lean_MessageData_kind(v_data_2926_);
lean_dec(v_data_2926_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Message_serialize(v_msg_2937_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2940_, uint8_t v_includeEndPos_2941_){
_start:
{
lean_object* v_fileName_2943_; lean_object* v_pos_2944_; lean_object* v_endPos_2945_; uint8_t v_severity_2946_; lean_object* v_caption_2947_; lean_object* v_data_2948_; lean_object* v___x_2949_; lean_object* v___y_2951_; uint8_t v___y_2955_; lean_object* v___y_2956_; uint32_t v___y_2957_; lean_object* v_str_2961_; lean_object* v___x_2973_; lean_object* v___y_2975_; lean_object* v_str_2976_; lean_object* v___y_2984_; 
v_fileName_2943_ = lean_ctor_get(v_msg_2940_, 0);
lean_inc_ref(v_fileName_2943_);
v_pos_2944_ = lean_ctor_get(v_msg_2940_, 1);
lean_inc_ref(v_pos_2944_);
v_endPos_2945_ = lean_ctor_get(v_msg_2940_, 2);
lean_inc(v_endPos_2945_);
v_severity_2946_ = lean_ctor_get_uint8(v_msg_2940_, sizeof(void*)*5 + 1);
v_caption_2947_ = lean_ctor_get(v_msg_2940_, 3);
lean_inc_ref(v_caption_2947_);
v_data_2948_ = lean_ctor_get(v_msg_2940_, 4);
lean_inc_n(v_data_2948_, 2);
lean_dec_ref(v_msg_2940_);
v___x_2949_ = l_Lean_MessageData_toString(v_data_2948_);
v___x_2973_ = l_Lean_MessageData_kind(v_data_2948_);
lean_dec(v_data_2948_);
if (v_includeEndPos_2941_ == 0)
{
lean_object* v___x_2990_; 
lean_dec(v_endPos_2945_);
v___x_2990_ = lean_box(0);
v___y_2984_ = v___x_2990_;
goto v___jp_2983_;
}
else
{
v___y_2984_ = v_endPos_2945_;
goto v___jp_2983_;
}
v___jp_2950_:
{
lean_object* v___x_2952_; lean_object* v_str_2953_; 
v___x_2952_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2953_ = lean_string_append(v___y_2951_, v___x_2952_);
return v_str_2953_;
}
v___jp_2954_:
{
uint32_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = 10;
v___x_2959_ = lean_uint32_dec_eq(v___y_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
v___y_2951_ = v___y_2956_;
goto v___jp_2950_;
}
else
{
if (v___y_2955_ == 0)
{
return v___y_2956_;
}
else
{
v___y_2951_ = v___y_2956_;
goto v___jp_2950_;
}
}
}
v___jp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2962_ = lean_string_utf8_byte_size(v_str_2961_);
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = lean_nat_dec_eq(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_inc_ref(v_str_2961_);
v___x_2965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2965_, 0, v_str_2961_);
lean_ctor_set(v___x_2965_, 1, v___x_2963_);
lean_ctor_set(v___x_2965_, 2, v___x_2962_);
v___x_2966_ = l_String_Slice_Pos_prev_x3f(v___x_2965_, v___x_2962_);
if (lean_obj_tag(v___x_2966_) == 0)
{
uint32_t v___x_2967_; 
lean_dec_ref_known(v___x_2965_, 3);
v___x_2967_ = 65;
v___y_2955_ = v___x_2964_;
v___y_2956_ = v_str_2961_;
v___y_2957_ = v___x_2967_;
goto v___jp_2954_;
}
else
{
lean_object* v_val_2968_; lean_object* v___x_2969_; 
v_val_2968_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_val_2968_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2969_ = l_String_Slice_Pos_get_x3f(v___x_2965_, v_val_2968_);
lean_dec(v_val_2968_);
lean_dec_ref_known(v___x_2965_, 3);
if (lean_obj_tag(v___x_2969_) == 0)
{
uint32_t v___x_2970_; 
v___x_2970_ = 65;
v___y_2955_ = v___x_2964_;
v___y_2956_ = v_str_2961_;
v___y_2957_ = v___x_2970_;
goto v___jp_2954_;
}
else
{
lean_object* v_val_2971_; uint32_t v___x_2972_; 
v_val_2971_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2972_ = lean_unbox_uint32(v_val_2971_);
lean_dec(v_val_2971_);
v___y_2955_ = v___x_2964_;
v___y_2956_ = v_str_2961_;
v___y_2957_ = v___x_2972_;
goto v___jp_2954_;
}
}
}
else
{
v___y_2951_ = v_str_2961_;
goto v___jp_2950_;
}
}
v___jp_2974_:
{
switch(v_severity_2946_)
{
case 0:
{
lean_dec(v___y_2975_);
lean_dec(v___x_2973_);
lean_dec_ref(v_pos_2944_);
lean_dec_ref(v_fileName_2943_);
v_str_2961_ = v_str_2976_;
goto v___jp_2960_;
}
case 1:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_str_2979_; 
v___x_2977_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2978_ = l_Lean_errorNameOfKind_x3f(v___x_2973_);
lean_dec(v___x_2973_);
v_str_2979_ = l_Lean_mkErrorStringWithPos(v_fileName_2943_, v_pos_2944_, v_str_2976_, v___y_2975_, v___x_2977_, v___x_2978_);
lean_dec_ref(v_str_2976_);
v_str_2961_ = v_str_2979_;
goto v___jp_2960_;
}
default: 
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_str_2982_; 
v___x_2980_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2981_ = l_Lean_errorNameOfKind_x3f(v___x_2973_);
lean_dec(v___x_2973_);
v_str_2982_ = l_Lean_mkErrorStringWithPos(v_fileName_2943_, v_pos_2944_, v_str_2976_, v___y_2975_, v___x_2980_, v___x_2981_);
lean_dec_ref(v_str_2976_);
v_str_2961_ = v_str_2982_;
goto v___jp_2960_;
}
}
}
v___jp_2983_:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2986_ = lean_string_dec_eq(v_caption_2947_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v_str_2989_; 
v___x_2987_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2988_ = lean_string_append(v_caption_2947_, v___x_2987_);
v_str_2989_ = lean_string_append(v___x_2988_, v___x_2949_);
lean_dec_ref(v___x_2949_);
v___y_2975_ = v___y_2984_;
v_str_2976_ = v_str_2989_;
goto v___jp_2974_;
}
else
{
lean_dec_ref(v_caption_2947_);
v___y_2975_ = v___y_2984_;
v_str_2976_ = v___x_2949_;
goto v___jp_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2991_, lean_object* v_includeEndPos_2992_, lean_object* v_a_2993_){
_start:
{
uint8_t v_includeEndPos_boxed_2994_; lean_object* v_res_2995_; 
v_includeEndPos_boxed_2994_ = lean_unbox(v_includeEndPos_2992_);
v_res_2995_ = l_Lean_Message_toString(v_msg_2991_, v_includeEndPos_boxed_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2996_){
_start:
{
lean_object* v_fileName_2998_; lean_object* v_pos_2999_; lean_object* v_endPos_3000_; uint8_t v_keepFullRange_3001_; uint8_t v_severity_3002_; uint8_t v_isSilent_3003_; lean_object* v_caption_3004_; lean_object* v_data_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_fileName_2998_ = lean_ctor_get(v_msg_2996_, 0);
lean_inc_ref(v_fileName_2998_);
v_pos_2999_ = lean_ctor_get(v_msg_2996_, 1);
lean_inc_ref(v_pos_2999_);
v_endPos_3000_ = lean_ctor_get(v_msg_2996_, 2);
lean_inc(v_endPos_3000_);
v_keepFullRange_3001_ = lean_ctor_get_uint8(v_msg_2996_, sizeof(void*)*5);
v_severity_3002_ = lean_ctor_get_uint8(v_msg_2996_, sizeof(void*)*5 + 1);
v_isSilent_3003_ = lean_ctor_get_uint8(v_msg_2996_, sizeof(void*)*5 + 2);
v_caption_3004_ = lean_ctor_get(v_msg_2996_, 3);
lean_inc_ref(v_caption_3004_);
v_data_3005_ = lean_ctor_get(v_msg_2996_, 4);
lean_inc_n(v_data_3005_, 2);
lean_dec_ref(v_msg_2996_);
v___x_3006_ = l_Lean_MessageData_toString(v_data_3005_);
v___x_3007_ = l_Lean_MessageData_kind(v_data_3005_);
lean_dec(v_data_3005_);
v___x_3008_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_fileName_2998_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3014_ = l_Lean_instToJsonPosition_toJson(v_pos_2999_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___x_3011_);
v___x_3017_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3018_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3000_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3011_);
v___x_3021_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3022_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3022_, 0, v_keepFullRange_3001_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3011_);
v___x_3025_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3026_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3002_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3011_);
v___x_3029_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3030_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3030_, 0, v_isSilent_3003_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3011_);
v___x_3033_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_caption_3004_);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3011_);
v___x_3037_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3006_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3011_);
v___x_3041_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3042_ = 1;
v___x_3043_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3007_, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3041_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3011_);
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3011_);
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3040_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3036_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3032_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3028_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3024_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3020_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3016_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3012_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3057_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3055_, v___x_3056_);
v___x_3058_ = l_Lean_Json_mkObj(v___x_3057_);
lean_dec(v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Message_toJson(v_msg_3059_);
return v_res_3061_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_unsigned_to_nat(32u);
v___x_3063_ = lean_mk_empty_array_with_capacity(v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3065_ = ((size_t)5ULL);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = lean_unsigned_to_nat(32u);
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_3067_);
v___x_3069_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3070_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
lean_ctor_set(v___x_3070_, 2, v___x_3066_);
lean_ctor_set(v___x_3070_, 3, v___x_3066_);
lean_ctor_set_usize(v___x_3070_, 4, v___x_3065_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = l_Lean_NameSet_empty;
v___x_3072_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
lean_ctor_set(v___x_3073_, 2, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3075_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_unsigned_to_nat(32u);
v___x_3077_ = lean_mk_empty_array_with_capacity(v___x_3076_);
lean_dec_ref(v___x_3077_);
v___x_3078_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3079_){
_start:
{
lean_object* v_unreported_3080_; 
v_unreported_3080_ = lean_ctor_get(v_self_3079_, 1);
lean_inc_ref(v_unreported_3080_);
return v_unreported_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_MessageLog_msgs(v_self_3081_);
lean_dec_ref(v_self_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3083_){
_start:
{
lean_object* v_reported_3084_; lean_object* v_unreported_3085_; lean_object* v___x_3086_; 
v_reported_3084_ = lean_ctor_get(v_x_3083_, 0);
lean_inc_ref(v_reported_3084_);
v_unreported_3085_ = lean_ctor_get(v_x_3083_, 1);
lean_inc_ref(v_unreported_3085_);
lean_dec_ref(v_x_3083_);
v___x_3086_ = l_Lean_PersistentArray_append___redArg(v_reported_3084_, v_unreported_3085_);
lean_dec_ref(v_unreported_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3087_){
_start:
{
lean_object* v_unreported_3088_; uint8_t v___x_3089_; 
v_unreported_3088_ = lean_ctor_get(v_log_3087_, 1);
v___x_3089_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3088_);
if (v___x_3089_ == 0)
{
uint8_t v___x_3090_; 
v___x_3090_ = 1;
return v___x_3090_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = 0;
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3092_){
_start:
{
uint8_t v_res_3093_; lean_object* v_r_3094_; 
v_res_3093_ = l_Lean_MessageLog_hasUnreported(v_log_3092_);
lean_dec_ref(v_log_3092_);
v_r_3094_ = lean_box(v_res_3093_);
return v_r_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3095_, lean_object* v_log_3096_){
_start:
{
lean_object* v_reported_3097_; lean_object* v_unreported_3098_; lean_object* v_loggedKinds_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3107_; 
v_reported_3097_ = lean_ctor_get(v_log_3096_, 0);
v_unreported_3098_ = lean_ctor_get(v_log_3096_, 1);
v_loggedKinds_3099_ = lean_ctor_get(v_log_3096_, 2);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_log_3096_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3101_ = v_log_3096_;
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_loggedKinds_3099_);
lean_inc(v_unreported_3098_);
lean_inc(v_reported_3097_);
lean_dec(v_log_3096_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = l_Lean_PersistentArray_push___redArg(v_unreported_3098_, v_msg_3095_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_reported_3097_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_loggedKinds_3099_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3110_, lean_object* v_x_3111_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_b_u2082_3110_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; 
v___x_3113_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3114_, lean_object* v_x_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3114_, v_x_3115_);
lean_dec(v_x_3115_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3117_, lean_object* v_k_3118_, lean_object* v_t_3119_){
_start:
{
if (lean_obj_tag(v_t_3119_) == 0)
{
lean_object* v_size_3120_; lean_object* v_k_3121_; lean_object* v_v_3122_; lean_object* v_l_3123_; lean_object* v_r_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3139_; 
v_size_3120_ = lean_ctor_get(v_t_3119_, 0);
v_k_3121_ = lean_ctor_get(v_t_3119_, 1);
v_v_3122_ = lean_ctor_get(v_t_3119_, 2);
v_l_3123_ = lean_ctor_get(v_t_3119_, 3);
v_r_3124_ = lean_ctor_get(v_t_3119_, 4);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_t_3119_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3126_ = v_t_3119_;
v_isShared_3127_ = v_isSharedCheck_3139_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_r_3124_);
lean_inc(v_l_3123_);
lean_inc(v_v_3122_);
lean_inc(v_k_3121_);
lean_inc(v_size_3120_);
lean_dec(v_t_3119_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3139_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
uint8_t v___x_3128_; 
v___x_3128_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3118_, v_k_3121_);
switch(v___x_3128_)
{
case 0:
{
lean_object* v_impl_3129_; lean_object* v___x_3130_; 
lean_del_object(v___x_3126_);
lean_dec(v_size_3120_);
v_impl_3129_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3117_, v_k_3118_, v_l_3123_);
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3121_, v_v_3122_, v_impl_3129_, v_r_3124_);
return v___x_3130_;
}
case 1:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_val_3133_; lean_object* v___x_3135_; 
lean_dec(v_k_3121_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_v_3122_);
v___x_3132_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3117_, v___x_3131_);
lean_dec_ref_known(v___x_3131_, 1);
v_val_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_val_3133_);
lean_dec(v___x_3132_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 2, v_val_3133_);
lean_ctor_set(v___x_3126_, 1, v_k_3118_);
v___x_3135_ = v___x_3126_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_size_3120_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_k_3118_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_val_3133_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_l_3123_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_r_3124_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
default: 
{
lean_object* v_impl_3137_; lean_object* v___x_3138_; 
lean_del_object(v___x_3126_);
lean_dec(v_size_3120_);
v_impl_3137_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3117_, v_k_3118_, v_r_3124_);
v___x_3138_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3121_, v_v_3122_, v_l_3123_, v_impl_3137_);
return v___x_3138_;
}
}
}
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_val_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3140_ = lean_box(0);
v___x_3141_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3117_, v___x_3140_);
v_val_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_val_3142_);
lean_dec(v___x_3141_);
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v_k_3118_);
lean_ctor_set(v___x_3144_, 2, v_val_3142_);
lean_ctor_set(v___x_3144_, 3, v_t_3119_);
lean_ctor_set(v___x_3144_, 4, v_t_3119_);
return v___x_3144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3145_, lean_object* v_x_3146_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
lean_object* v_k_3147_; lean_object* v_v_3148_; lean_object* v_l_3149_; lean_object* v_r_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_k_3147_ = lean_ctor_get(v_x_3146_, 1);
lean_inc(v_k_3147_);
v_v_3148_ = lean_ctor_get(v_x_3146_, 2);
lean_inc(v_v_3148_);
v_l_3149_ = lean_ctor_get(v_x_3146_, 3);
lean_inc(v_l_3149_);
v_r_3150_ = lean_ctor_get(v_x_3146_, 4);
lean_inc(v_r_3150_);
lean_dec_ref_known(v_x_3146_, 5);
v___x_3151_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3145_, v_l_3149_);
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3148_, v_k_3147_, v___x_3151_);
v_init_3145_ = v___x_3152_;
v_x_3146_ = v_r_3150_;
goto _start;
}
else
{
return v_init_3145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3154_, lean_object* v_l_u2082_3155_){
_start:
{
lean_object* v_reported_3156_; lean_object* v_unreported_3157_; lean_object* v_loggedKinds_3158_; lean_object* v_reported_3159_; lean_object* v_unreported_3160_; lean_object* v_loggedKinds_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3171_; 
v_reported_3156_ = lean_ctor_get(v_l_u2081_3154_, 0);
lean_inc_ref(v_reported_3156_);
v_unreported_3157_ = lean_ctor_get(v_l_u2081_3154_, 1);
lean_inc_ref(v_unreported_3157_);
v_loggedKinds_3158_ = lean_ctor_get(v_l_u2081_3154_, 2);
lean_inc(v_loggedKinds_3158_);
lean_dec_ref(v_l_u2081_3154_);
v_reported_3159_ = lean_ctor_get(v_l_u2082_3155_, 0);
v_unreported_3160_ = lean_ctor_get(v_l_u2082_3155_, 1);
v_loggedKinds_3161_ = lean_ctor_get(v_l_u2082_3155_, 2);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_l_u2082_3155_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3163_ = v_l_u2082_3155_;
v_isShared_3164_ = v_isSharedCheck_3171_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_loggedKinds_3161_);
lean_inc(v_unreported_3160_);
lean_inc(v_reported_3159_);
lean_dec(v_l_u2082_3155_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3171_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3165_ = l_Lean_PersistentArray_append___redArg(v_reported_3156_, v_reported_3159_);
lean_dec_ref(v_reported_3159_);
v___x_3166_ = l_Lean_PersistentArray_append___redArg(v_unreported_3157_, v_unreported_3160_);
lean_dec_ref(v_unreported_3160_);
v___x_3167_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3158_, v_loggedKinds_3161_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 2, v___x_3167_);
lean_ctor_set(v___x_3163_, 1, v___x_3166_);
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3169_ = v___x_3163_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3172_, lean_object* v_k_3173_, lean_object* v_t_3174_, lean_object* v_hl_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3172_, v_k_3173_, v_t_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3177_, lean_object* v_t_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3177_, v_t_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3182_, size_t v_i_3183_, size_t v_stop_3184_){
_start:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_usize_dec_eq(v_i_3183_, v_stop_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; uint8_t v_severity_3187_; uint8_t v___x_3188_; 
v___x_3186_ = lean_array_uget_borrowed(v_as_3182_, v_i_3183_);
v_severity_3187_ = lean_ctor_get_uint8(v___x_3186_, sizeof(void*)*5 + 1);
v___x_3188_ = 1;
if (v_severity_3187_ == 2)
{
return v___x_3188_;
}
else
{
if (v___x_3185_ == 0)
{
size_t v___x_3189_; size_t v___x_3190_; 
v___x_3189_ = ((size_t)1ULL);
v___x_3190_ = lean_usize_add(v_i_3183_, v___x_3189_);
v_i_3183_ = v___x_3190_;
goto _start;
}
else
{
return v___x_3188_;
}
}
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3193_, lean_object* v_i_3194_, lean_object* v_stop_3195_){
_start:
{
size_t v_i_boxed_3196_; size_t v_stop_boxed_3197_; uint8_t v_res_3198_; lean_object* v_r_3199_; 
v_i_boxed_3196_ = lean_unbox_usize(v_i_3194_);
lean_dec(v_i_3194_);
v_stop_boxed_3197_ = lean_unbox_usize(v_stop_3195_);
lean_dec(v_stop_3195_);
v_res_3198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3193_, v_i_boxed_3196_, v_stop_boxed_3197_);
lean_dec_ref(v_as_3193_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_object* v_cs_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v_cs_3201_ = lean_ctor_get(v_x_3200_, 0);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_array_get_size(v_cs_3201_);
v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
if (v___x_3204_ == 0)
{
return v___x_3204_;
}
else
{
if (v___x_3204_ == 0)
{
return v___x_3204_;
}
else
{
size_t v___x_3205_; size_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = lean_usize_of_nat(v___x_3203_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3201_, v___x_3205_, v___x_3206_);
return v___x_3207_;
}
}
}
else
{
lean_object* v_vs_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_vs_3208_ = lean_ctor_get(v_x_3200_, 0);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_array_get_size(v_vs_3208_);
v___x_3211_ = lean_nat_dec_lt(v___x_3209_, v___x_3210_);
if (v___x_3211_ == 0)
{
return v___x_3211_;
}
else
{
if (v___x_3211_ == 0)
{
return v___x_3211_;
}
else
{
size_t v___x_3212_; size_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3212_ = ((size_t)0ULL);
v___x_3213_ = lean_usize_of_nat(v___x_3210_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3208_, v___x_3212_, v___x_3213_);
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3215_, size_t v_i_3216_, size_t v_stop_3217_){
_start:
{
uint8_t v___x_3218_; 
v___x_3218_ = lean_usize_dec_eq(v_i_3216_, v_stop_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = lean_array_uget_borrowed(v_as_3215_, v_i_3216_);
v___x_3220_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3219_);
if (v___x_3220_ == 0)
{
size_t v___x_3221_; size_t v___x_3222_; 
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3216_, v___x_3221_);
v_i_3216_ = v___x_3222_;
goto _start;
}
else
{
return v___x_3220_;
}
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = 0;
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3225_, lean_object* v_i_3226_, lean_object* v_stop_3227_){
_start:
{
size_t v_i_boxed_3228_; size_t v_stop_boxed_3229_; uint8_t v_res_3230_; lean_object* v_r_3231_; 
v_i_boxed_3228_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_stop_boxed_3229_ = lean_unbox_usize(v_stop_3227_);
lean_dec(v_stop_3227_);
v_res_3230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3225_, v_i_boxed_3228_, v_stop_boxed_3229_);
lean_dec_ref(v_as_3225_);
v_r_3231_ = lean_box(v_res_3230_);
return v_r_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3232_);
lean_dec_ref(v_x_3232_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3235_){
_start:
{
lean_object* v_root_3236_; lean_object* v_tail_3237_; uint8_t v___x_3238_; 
v_root_3236_ = lean_ctor_get(v_t_3235_, 0);
v_tail_3237_ = lean_ctor_get(v_t_3235_, 1);
v___x_3238_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3236_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3239_ = lean_unsigned_to_nat(0u);
v___x_3240_ = lean_array_get_size(v_tail_3237_);
v___x_3241_ = lean_nat_dec_lt(v___x_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
return v___x_3238_;
}
else
{
if (v___x_3241_ == 0)
{
return v___x_3238_;
}
else
{
size_t v___x_3242_; size_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_usize_of_nat(v___x_3240_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3237_, v___x_3242_, v___x_3243_);
return v___x_3244_;
}
}
}
else
{
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3245_){
_start:
{
uint8_t v_res_3246_; lean_object* v_r_3247_; 
v_res_3246_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3245_);
lean_dec_ref(v_t_3245_);
v_r_3247_ = lean_box(v_res_3246_);
return v_r_3247_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3248_, lean_object* v_as_3249_, size_t v_i_3250_, size_t v_stop_3251_){
_start:
{
uint8_t v___x_3252_; 
v___x_3252_ = lean_usize_dec_eq(v_i_3250_, v_stop_3251_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; uint8_t v_severity_3254_; uint8_t v___x_3255_; 
v___x_3253_ = lean_array_uget_borrowed(v_as_3249_, v_i_3250_);
v_severity_3254_ = lean_ctor_get_uint8(v___x_3253_, sizeof(void*)*5 + 1);
v___x_3255_ = 1;
if (v_severity_3254_ == 2)
{
return v___x_3255_;
}
else
{
if (v___x_3248_ == 0)
{
size_t v___x_3256_; size_t v___x_3257_; 
v___x_3256_ = ((size_t)1ULL);
v___x_3257_ = lean_usize_add(v_i_3250_, v___x_3256_);
v_i_3250_ = v___x_3257_;
goto _start;
}
else
{
return v___x_3255_;
}
}
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = 0;
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3260_, lean_object* v_as_3261_, lean_object* v_i_3262_, lean_object* v_stop_3263_){
_start:
{
uint8_t v___x_1884__boxed_3264_; size_t v_i_boxed_3265_; size_t v_stop_boxed_3266_; uint8_t v_res_3267_; lean_object* v_r_3268_; 
v___x_1884__boxed_3264_ = lean_unbox(v___x_3260_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3262_);
lean_dec(v_i_3262_);
v_stop_boxed_3266_ = lean_unbox_usize(v_stop_3263_);
lean_dec(v_stop_3263_);
v_res_3267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_3264_, v_as_3261_, v_i_boxed_3265_, v_stop_boxed_3266_);
lean_dec_ref(v_as_3261_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3269_, lean_object* v_x_3270_){
_start:
{
if (lean_obj_tag(v_x_3270_) == 0)
{
lean_object* v_cs_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_cs_3271_ = lean_ctor_get(v_x_3270_, 0);
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = lean_array_get_size(v_cs_3271_);
v___x_3274_ = lean_nat_dec_lt(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
return v___x_3274_;
}
else
{
if (v___x_3274_ == 0)
{
return v___x_3274_;
}
else
{
size_t v___x_3275_; size_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = ((size_t)0ULL);
v___x_3276_ = lean_usize_of_nat(v___x_3273_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3269_, v_cs_3271_, v___x_3275_, v___x_3276_);
return v___x_3277_;
}
}
}
else
{
lean_object* v_vs_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
v_vs_3278_ = lean_ctor_get(v_x_3270_, 0);
v___x_3279_ = lean_unsigned_to_nat(0u);
v___x_3280_ = lean_array_get_size(v_vs_3278_);
v___x_3281_ = lean_nat_dec_lt(v___x_3279_, v___x_3280_);
if (v___x_3281_ == 0)
{
return v___x_3281_;
}
else
{
if (v___x_3281_ == 0)
{
return v___x_3281_;
}
else
{
size_t v___x_3282_; size_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = lean_usize_of_nat(v___x_3280_);
v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3269_, v_vs_3278_, v___x_3282_, v___x_3283_);
return v___x_3284_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3285_, lean_object* v_as_3286_, size_t v_i_3287_, size_t v_stop_3288_){
_start:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_usize_dec_eq(v_i_3287_, v_stop_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = lean_array_uget_borrowed(v_as_3286_, v_i_3287_);
v___x_3291_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3285_, v___x_3290_);
if (v___x_3291_ == 0)
{
size_t v___x_3292_; size_t v___x_3293_; 
v___x_3292_ = ((size_t)1ULL);
v___x_3293_ = lean_usize_add(v_i_3287_, v___x_3292_);
v_i_3287_ = v___x_3293_;
goto _start;
}
else
{
return v___x_3291_;
}
}
else
{
uint8_t v___x_3295_; 
v___x_3295_ = 0;
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3296_, lean_object* v_as_3297_, lean_object* v_i_3298_, lean_object* v_stop_3299_){
_start:
{
uint8_t v___x_1901__boxed_3300_; size_t v_i_boxed_3301_; size_t v_stop_boxed_3302_; uint8_t v_res_3303_; lean_object* v_r_3304_; 
v___x_1901__boxed_3300_ = lean_unbox(v___x_3296_);
v_i_boxed_3301_ = lean_unbox_usize(v_i_3298_);
lean_dec(v_i_3298_);
v_stop_boxed_3302_ = lean_unbox_usize(v_stop_3299_);
lean_dec(v_stop_3299_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_3300_, v_as_3297_, v_i_boxed_3301_, v_stop_boxed_3302_);
lean_dec_ref(v_as_3297_);
v_r_3304_ = lean_box(v_res_3303_);
return v_r_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3305_, lean_object* v_x_3306_){
_start:
{
uint8_t v___x_1909__boxed_3307_; uint8_t v_res_3308_; lean_object* v_r_3309_; 
v___x_1909__boxed_3307_ = lean_unbox(v___x_3305_);
v_res_3308_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_3307_, v_x_3306_);
lean_dec_ref(v_x_3306_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3310_, lean_object* v_t_3311_){
_start:
{
lean_object* v_root_3312_; lean_object* v_tail_3313_; uint8_t v___x_3314_; 
v_root_3312_ = lean_ctor_get(v_t_3311_, 0);
v_tail_3313_ = lean_ctor_get(v_t_3311_, 1);
v___x_3314_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3310_, v_root_3312_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_array_get_size(v_tail_3313_);
v___x_3317_ = lean_nat_dec_lt(v___x_3315_, v___x_3316_);
if (v___x_3317_ == 0)
{
return v___x_3314_;
}
else
{
if (v___x_3317_ == 0)
{
return v___x_3314_;
}
else
{
size_t v___x_3318_; size_t v___x_3319_; uint8_t v___x_3320_; 
v___x_3318_ = ((size_t)0ULL);
v___x_3319_ = lean_usize_of_nat(v___x_3316_);
v___x_3320_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3310_, v_tail_3313_, v___x_3318_, v___x_3319_);
return v___x_3320_;
}
}
}
else
{
return v___x_3314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3321_, lean_object* v_t_3322_){
_start:
{
uint8_t v___x_1952__boxed_3323_; uint8_t v_res_3324_; lean_object* v_r_3325_; 
v___x_1952__boxed_3323_ = lean_unbox(v___x_3321_);
v_res_3324_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_3323_, v_t_3322_);
lean_dec_ref(v_t_3322_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3326_){
_start:
{
lean_object* v_reported_3327_; lean_object* v_unreported_3328_; uint8_t v___x_3329_; 
v_reported_3327_ = lean_ctor_get(v_log_3326_, 0);
v_unreported_3328_ = lean_ctor_get(v_log_3326_, 1);
v___x_3329_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3327_);
if (v___x_3329_ == 0)
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3329_, v_unreported_3328_);
return v___x_3330_;
}
else
{
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3331_){
_start:
{
uint8_t v_res_3332_; lean_object* v_r_3333_; 
v_res_3332_ = l_Lean_MessageLog_hasErrors(v_log_3331_);
lean_dec_ref(v_log_3331_);
v_r_3333_ = lean_box(v_res_3332_);
return v_r_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3334_){
_start:
{
lean_object* v_reported_3335_; lean_object* v_unreported_3336_; lean_object* v_loggedKinds_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3348_; 
v_reported_3335_ = lean_ctor_get(v_log_3334_, 0);
v_unreported_3336_ = lean_ctor_get(v_log_3334_, 1);
v_loggedKinds_3337_ = lean_ctor_get(v_log_3334_, 2);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_log_3334_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3339_ = v_log_3334_;
v_isShared_3340_ = v_isSharedCheck_3348_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_loggedKinds_3337_);
lean_inc(v_unreported_3336_);
lean_inc(v_reported_3335_);
lean_dec(v_log_3334_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3348_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3341_ = l_Lean_PersistentArray_append___redArg(v_reported_3335_, v_unreported_3336_);
lean_dec_ref(v_unreported_3336_);
v___x_3342_ = lean_unsigned_to_nat(32u);
v___x_3343_ = lean_mk_empty_array_with_capacity(v___x_3342_);
lean_dec_ref(v___x_3343_);
v___x_3344_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v___x_3344_);
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3346_ = v___x_3339_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_loggedKinds_3337_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3349_, size_t v_i_3350_, lean_object* v_bs_3351_){
_start:
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_usize_dec_lt(v_i_3350_, v_sz_3349_);
if (v___x_3352_ == 0)
{
return v_bs_3351_;
}
else
{
lean_object* v_v_3353_; lean_object* v_fileName_3354_; lean_object* v_pos_3355_; lean_object* v_endPos_3356_; uint8_t v_keepFullRange_3357_; uint8_t v_severity_3358_; uint8_t v_isSilent_3359_; lean_object* v_caption_3360_; lean_object* v_data_3361_; lean_object* v___x_3362_; lean_object* v_bs_x27_3363_; lean_object* v___y_3365_; 
v_v_3353_ = lean_array_uget(v_bs_3351_, v_i_3350_);
v_fileName_3354_ = lean_ctor_get(v_v_3353_, 0);
v_pos_3355_ = lean_ctor_get(v_v_3353_, 1);
v_endPos_3356_ = lean_ctor_get(v_v_3353_, 2);
v_keepFullRange_3357_ = lean_ctor_get_uint8(v_v_3353_, sizeof(void*)*5);
v_severity_3358_ = lean_ctor_get_uint8(v_v_3353_, sizeof(void*)*5 + 1);
v_isSilent_3359_ = lean_ctor_get_uint8(v_v_3353_, sizeof(void*)*5 + 2);
v_caption_3360_ = lean_ctor_get(v_v_3353_, 3);
v_data_3361_ = lean_ctor_get(v_v_3353_, 4);
v___x_3362_ = lean_unsigned_to_nat(0u);
v_bs_x27_3363_ = lean_array_uset(v_bs_3351_, v_i_3350_, v___x_3362_);
if (v_severity_3358_ == 2)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
lean_inc(v_data_3361_);
lean_inc_ref(v_caption_3360_);
lean_inc(v_endPos_3356_);
lean_inc_ref(v_pos_3355_);
lean_inc_ref(v_fileName_3354_);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_v_3353_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; lean_object* v_unused_3381_; lean_object* v_unused_3382_; 
v_unused_3378_ = lean_ctor_get(v_v_3353_, 4);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_v_3353_, 3);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_v_3353_, 2);
lean_dec(v_unused_3380_);
v_unused_3381_ = lean_ctor_get(v_v_3353_, 1);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_v_3353_, 0);
lean_dec(v_unused_3382_);
v___x_3371_ = v_v_3353_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v_v_3353_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = 1;
if (v_isShared_3372_ == 0)
{
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_fileName_3354_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_pos_3355_);
lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_endPos_3356_);
lean_ctor_set(v_reuseFailAlloc_3376_, 3, v_caption_3360_);
lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_data_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, sizeof(void*)*5, v_keepFullRange_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, sizeof(void*)*5 + 2, v_isSilent_3359_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*5 + 1, v___x_3373_);
v___y_3365_ = v___x_3375_;
goto v___jp_3364_;
}
}
}
else
{
v___y_3365_ = v_v_3353_;
goto v___jp_3364_;
}
v___jp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3350_, v___x_3366_);
v___x_3368_ = lean_array_uset(v_bs_x27_3363_, v_i_3350_, v___y_3365_);
v_i_3350_ = v___x_3367_;
v_bs_3351_ = v___x_3368_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3383_, lean_object* v_i_3384_, lean_object* v_bs_3385_){
_start:
{
size_t v_sz_boxed_3386_; size_t v_i_boxed_3387_; lean_object* v_res_3388_; 
v_sz_boxed_3386_ = lean_unbox_usize(v_sz_3383_);
lean_dec(v_sz_3383_);
v_i_boxed_3387_ = lean_unbox_usize(v_i_3384_);
lean_dec(v_i_3384_);
v_res_3388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3386_, v_i_boxed_3387_, v_bs_3385_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3389_, size_t v_i_3390_, lean_object* v_bs_3391_){
_start:
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_usize_dec_lt(v_i_3390_, v_sz_3389_);
if (v___x_3392_ == 0)
{
return v_bs_3391_;
}
else
{
lean_object* v_v_3393_; lean_object* v___x_3394_; lean_object* v_bs_x27_3395_; lean_object* v___x_3396_; size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v_v_3393_ = lean_array_uget(v_bs_3391_, v_i_3390_);
v___x_3394_ = lean_unsigned_to_nat(0u);
v_bs_x27_3395_ = lean_array_uset(v_bs_3391_, v_i_3390_, v___x_3394_);
v___x_3396_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3393_);
v___x_3397_ = ((size_t)1ULL);
v___x_3398_ = lean_usize_add(v_i_3390_, v___x_3397_);
v___x_3399_ = lean_array_uset(v_bs_x27_3395_, v_i_3390_, v___x_3396_);
v_i_3390_ = v___x_3398_;
v_bs_3391_ = v___x_3399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3401_){
_start:
{
if (lean_obj_tag(v_x_3401_) == 0)
{
lean_object* v_cs_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3412_; 
v_cs_3402_ = lean_ctor_get(v_x_3401_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_x_3401_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3404_ = v_x_3401_;
v_isShared_3405_ = v_isSharedCheck_3412_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_cs_3402_);
lean_dec(v_x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3412_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
size_t v_sz_3406_; size_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v_sz_3406_ = lean_array_size(v_cs_3402_);
v___x_3407_ = ((size_t)0ULL);
v___x_3408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3406_, v___x_3407_, v_cs_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3408_);
v___x_3410_ = v___x_3404_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
lean_object* v_vs_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3423_; 
v_vs_3413_ = lean_ctor_get(v_x_3401_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_x_3401_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3415_ = v_x_3401_;
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_vs_3413_);
lean_dec(v_x_3401_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
size_t v_sz_3417_; size_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v_sz_3417_ = lean_array_size(v_vs_3413_);
v___x_3418_ = ((size_t)0ULL);
v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3417_, v___x_3418_, v_vs_3413_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3419_);
v___x_3421_ = v___x_3415_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3424_, lean_object* v_i_3425_, lean_object* v_bs_3426_){
_start:
{
size_t v_sz_boxed_3427_; size_t v_i_boxed_3428_; lean_object* v_res_3429_; 
v_sz_boxed_3427_ = lean_unbox_usize(v_sz_3424_);
lean_dec(v_sz_3424_);
v_i_boxed_3428_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3427_, v_i_boxed_3428_, v_bs_3426_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3430_){
_start:
{
lean_object* v_root_3431_; lean_object* v_tail_3432_; lean_object* v_size_3433_; size_t v_shift_3434_; lean_object* v_tailOff_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3446_; 
v_root_3431_ = lean_ctor_get(v_t_3430_, 0);
v_tail_3432_ = lean_ctor_get(v_t_3430_, 1);
v_size_3433_ = lean_ctor_get(v_t_3430_, 2);
v_shift_3434_ = lean_ctor_get_usize(v_t_3430_, 4);
v_tailOff_3435_ = lean_ctor_get(v_t_3430_, 3);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_t_3430_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3437_ = v_t_3430_;
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_tailOff_3435_);
lean_inc(v_size_3433_);
lean_inc(v_tail_3432_);
lean_inc(v_root_3431_);
lean_dec(v_t_3430_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; size_t v_sz_3440_; size_t v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3439_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3431_);
v_sz_3440_ = lean_array_size(v_tail_3432_);
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3440_, v___x_3441_, v_tail_3432_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3442_);
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3444_ = v___x_3437_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_size_3433_);
lean_ctor_set(v_reuseFailAlloc_3445_, 3, v_tailOff_3435_);
lean_ctor_set_usize(v_reuseFailAlloc_3445_, 4, v_shift_3434_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v_unreported_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3460_; 
v___x_3448_ = lean_unsigned_to_nat(32u);
v___x_3449_ = lean_mk_empty_array_with_capacity(v___x_3448_);
lean_dec_ref(v___x_3449_);
v___x_3450_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3451_ = lean_ctor_get(v_log_3447_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_log_3447_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; lean_object* v_unused_3462_; 
v_unused_3461_ = lean_ctor_get(v_log_3447_, 2);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_log_3447_, 0);
lean_dec(v_unused_3462_);
v___x_3453_ = v_log_3447_;
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_unreported_3451_);
lean_dec(v_log_3447_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3455_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3451_);
v___x_3456_ = l_Lean_NameSet_empty;
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 2, v___x_3456_);
lean_ctor_set(v___x_3453_, 1, v___x_3455_);
lean_ctor_set(v___x_3453_, 0, v___x_3450_);
v___x_3458_ = v___x_3453_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3463_, size_t v_i_3464_, lean_object* v_bs_3465_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3464_, v_sz_3463_);
if (v___x_3466_ == 0)
{
return v_bs_3465_;
}
else
{
lean_object* v_v_3467_; lean_object* v_fileName_3468_; lean_object* v_pos_3469_; lean_object* v_endPos_3470_; uint8_t v_keepFullRange_3471_; uint8_t v_severity_3472_; uint8_t v_isSilent_3473_; lean_object* v_caption_3474_; lean_object* v_data_3475_; lean_object* v___x_3476_; lean_object* v_bs_x27_3477_; lean_object* v___y_3479_; 
v_v_3467_ = lean_array_uget(v_bs_3465_, v_i_3464_);
v_fileName_3468_ = lean_ctor_get(v_v_3467_, 0);
v_pos_3469_ = lean_ctor_get(v_v_3467_, 1);
v_endPos_3470_ = lean_ctor_get(v_v_3467_, 2);
v_keepFullRange_3471_ = lean_ctor_get_uint8(v_v_3467_, sizeof(void*)*5);
v_severity_3472_ = lean_ctor_get_uint8(v_v_3467_, sizeof(void*)*5 + 1);
v_isSilent_3473_ = lean_ctor_get_uint8(v_v_3467_, sizeof(void*)*5 + 2);
v_caption_3474_ = lean_ctor_get(v_v_3467_, 3);
v_data_3475_ = lean_ctor_get(v_v_3467_, 4);
v___x_3476_ = lean_unsigned_to_nat(0u);
v_bs_x27_3477_ = lean_array_uset(v_bs_3465_, v_i_3464_, v___x_3476_);
if (v_severity_3472_ == 2)
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3491_; 
lean_inc(v_data_3475_);
lean_inc_ref(v_caption_3474_);
lean_inc(v_endPos_3470_);
lean_inc_ref(v_pos_3469_);
lean_inc_ref(v_fileName_3468_);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_v_3467_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; lean_object* v_unused_3493_; lean_object* v_unused_3494_; lean_object* v_unused_3495_; lean_object* v_unused_3496_; 
v_unused_3492_ = lean_ctor_get(v_v_3467_, 4);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_v_3467_, 3);
lean_dec(v_unused_3493_);
v_unused_3494_ = lean_ctor_get(v_v_3467_, 2);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_v_3467_, 1);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_v_3467_, 0);
lean_dec(v_unused_3496_);
v___x_3485_ = v_v_3467_;
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v_v_3467_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
uint8_t v___x_3487_; lean_object* v___x_3489_; 
v___x_3487_ = 0;
if (v_isShared_3486_ == 0)
{
v___x_3489_ = v___x_3485_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fileName_3468_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_pos_3469_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_endPos_3470_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_caption_3474_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_data_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*5, v_keepFullRange_3471_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*5 + 2, v_isSilent_3473_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*5 + 1, v___x_3487_);
v___y_3479_ = v___x_3489_;
goto v___jp_3478_;
}
}
}
else
{
v___y_3479_ = v_v_3467_;
goto v___jp_3478_;
}
v___jp_3478_:
{
size_t v___x_3480_; size_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((size_t)1ULL);
v___x_3481_ = lean_usize_add(v_i_3464_, v___x_3480_);
v___x_3482_ = lean_array_uset(v_bs_x27_3477_, v_i_3464_, v___y_3479_);
v_i_3464_ = v___x_3481_;
v_bs_3465_ = v___x_3482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3497_, lean_object* v_i_3498_, lean_object* v_bs_3499_){
_start:
{
size_t v_sz_boxed_3500_; size_t v_i_boxed_3501_; lean_object* v_res_3502_; 
v_sz_boxed_3500_ = lean_unbox_usize(v_sz_3497_);
lean_dec(v_sz_3497_);
v_i_boxed_3501_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3500_, v_i_boxed_3501_, v_bs_3499_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3503_, size_t v_i_3504_, lean_object* v_bs_3505_){
_start:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_usize_dec_lt(v_i_3504_, v_sz_3503_);
if (v___x_3506_ == 0)
{
return v_bs_3505_;
}
else
{
lean_object* v_v_3507_; lean_object* v___x_3508_; lean_object* v_bs_x27_3509_; lean_object* v___x_3510_; size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v_v_3507_ = lean_array_uget(v_bs_3505_, v_i_3504_);
v___x_3508_ = lean_unsigned_to_nat(0u);
v_bs_x27_3509_ = lean_array_uset(v_bs_3505_, v_i_3504_, v___x_3508_);
v___x_3510_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3507_);
v___x_3511_ = ((size_t)1ULL);
v___x_3512_ = lean_usize_add(v_i_3504_, v___x_3511_);
v___x_3513_ = lean_array_uset(v_bs_x27_3509_, v_i_3504_, v___x_3510_);
v_i_3504_ = v___x_3512_;
v_bs_3505_ = v___x_3513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3515_){
_start:
{
if (lean_obj_tag(v_x_3515_) == 0)
{
lean_object* v_cs_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3526_; 
v_cs_3516_ = lean_ctor_get(v_x_3515_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_x_3515_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3518_ = v_x_3515_;
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_cs_3516_);
lean_dec(v_x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
size_t v_sz_3520_; size_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_sz_3520_ = lean_array_size(v_cs_3516_);
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3520_, v___x_3521_, v_cs_3516_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3522_);
v___x_3524_ = v___x_3518_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
else
{
lean_object* v_vs_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3537_; 
v_vs_3527_ = lean_ctor_get(v_x_3515_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_x_3515_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3529_ = v_x_3515_;
v_isShared_3530_ = v_isSharedCheck_3537_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_vs_3527_);
lean_dec(v_x_3515_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3537_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
size_t v_sz_3531_; size_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v_sz_3531_ = lean_array_size(v_vs_3527_);
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3531_, v___x_3532_, v_vs_3527_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3533_);
v___x_3535_ = v___x_3529_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3538_, lean_object* v_i_3539_, lean_object* v_bs_3540_){
_start:
{
size_t v_sz_boxed_3541_; size_t v_i_boxed_3542_; lean_object* v_res_3543_; 
v_sz_boxed_3541_ = lean_unbox_usize(v_sz_3538_);
lean_dec(v_sz_3538_);
v_i_boxed_3542_ = lean_unbox_usize(v_i_3539_);
lean_dec(v_i_3539_);
v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3541_, v_i_boxed_3542_, v_bs_3540_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3544_){
_start:
{
lean_object* v_root_3545_; lean_object* v_tail_3546_; lean_object* v_size_3547_; size_t v_shift_3548_; lean_object* v_tailOff_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3560_; 
v_root_3545_ = lean_ctor_get(v_t_3544_, 0);
v_tail_3546_ = lean_ctor_get(v_t_3544_, 1);
v_size_3547_ = lean_ctor_get(v_t_3544_, 2);
v_shift_3548_ = lean_ctor_get_usize(v_t_3544_, 4);
v_tailOff_3549_ = lean_ctor_get(v_t_3544_, 3);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_t_3544_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3551_ = v_t_3544_;
v_isShared_3552_ = v_isSharedCheck_3560_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_tailOff_3549_);
lean_inc(v_size_3547_);
lean_inc(v_tail_3546_);
lean_inc(v_root_3545_);
lean_dec(v_t_3544_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3560_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; size_t v_sz_3554_; size_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3553_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3545_);
v_sz_3554_ = lean_array_size(v_tail_3546_);
v___x_3555_ = ((size_t)0ULL);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3554_, v___x_3555_, v_tail_3546_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v___x_3556_);
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3558_ = v___x_3551_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_size_3547_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v_tailOff_3549_);
lean_ctor_set_usize(v_reuseFailAlloc_3559_, 4, v_shift_3548_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3561_){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_unreported_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
v___x_3562_ = lean_unsigned_to_nat(32u);
v___x_3563_ = lean_mk_empty_array_with_capacity(v___x_3562_);
lean_dec_ref(v___x_3563_);
v___x_3564_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3565_ = lean_ctor_get(v_log_3561_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_log_3561_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; lean_object* v_unused_3576_; 
v_unused_3575_ = lean_ctor_get(v_log_3561_, 2);
lean_dec(v_unused_3575_);
v_unused_3576_ = lean_ctor_get(v_log_3561_, 0);
lean_dec(v_unused_3576_);
v___x_3567_ = v_log_3561_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_unreported_3565_);
lean_dec(v_log_3561_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3565_);
v___x_3570_ = l_Lean_NameSet_empty;
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 2, v___x_3570_);
lean_ctor_set(v___x_3567_, 1, v___x_3569_);
lean_ctor_set(v___x_3567_, 0, v___x_3564_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3577_, size_t v_i_3578_, size_t v_stop_3579_, lean_object* v_b_3580_){
_start:
{
lean_object* v___y_3582_; uint8_t v___x_3586_; 
v___x_3586_ = lean_usize_dec_eq(v_i_3578_, v_stop_3579_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; uint8_t v_severity_3588_; 
v___x_3587_ = lean_array_uget_borrowed(v_as_3577_, v_i_3578_);
v_severity_3588_ = lean_ctor_get_uint8(v___x_3587_, sizeof(void*)*5 + 1);
if (v_severity_3588_ == 0)
{
lean_object* v___x_3589_; 
lean_inc(v___x_3587_);
v___x_3589_ = l_Lean_PersistentArray_push___redArg(v_b_3580_, v___x_3587_);
v___y_3582_ = v___x_3589_;
goto v___jp_3581_;
}
else
{
v___y_3582_ = v_b_3580_;
goto v___jp_3581_;
}
}
else
{
return v_b_3580_;
}
v___jp_3581_:
{
size_t v___x_3583_; size_t v___x_3584_; 
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_add(v_i_3578_, v___x_3583_);
v_i_3578_ = v___x_3584_;
v_b_3580_ = v___y_3582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3590_, lean_object* v_i_3591_, lean_object* v_stop_3592_, lean_object* v_b_3593_){
_start:
{
size_t v_i_boxed_3594_; size_t v_stop_boxed_3595_; lean_object* v_res_3596_; 
v_i_boxed_3594_ = lean_unbox_usize(v_i_3591_);
lean_dec(v_i_3591_);
v_stop_boxed_3595_ = lean_unbox_usize(v_stop_3592_);
lean_dec(v_stop_3592_);
v_res_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3590_, v_i_boxed_3594_, v_stop_boxed_3595_, v_b_3593_);
lean_dec_ref(v_as_3590_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
if (lean_obj_tag(v_x_3597_) == 0)
{
lean_object* v_cs_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_cs_3599_ = lean_ctor_get(v_x_3597_, 0);
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = lean_array_get_size(v_cs_3599_);
v___x_3602_ = lean_nat_dec_lt(v___x_3600_, v___x_3601_);
if (v___x_3602_ == 0)
{
return v_x_3598_;
}
else
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_nat_dec_le(v___x_3601_, v___x_3601_);
if (v___x_3603_ == 0)
{
if (v___x_3602_ == 0)
{
return v_x_3598_;
}
else
{
size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = ((size_t)0ULL);
v___x_3605_ = lean_usize_of_nat(v___x_3601_);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3599_, v___x_3604_, v___x_3605_, v_x_3598_);
return v___x_3606_;
}
}
else
{
size_t v___x_3607_; size_t v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = ((size_t)0ULL);
v___x_3608_ = lean_usize_of_nat(v___x_3601_);
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3599_, v___x_3607_, v___x_3608_, v_x_3598_);
return v___x_3609_;
}
}
}
else
{
lean_object* v_vs_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_vs_3610_ = lean_ctor_get(v_x_3597_, 0);
v___x_3611_ = lean_unsigned_to_nat(0u);
v___x_3612_ = lean_array_get_size(v_vs_3610_);
v___x_3613_ = lean_nat_dec_lt(v___x_3611_, v___x_3612_);
if (v___x_3613_ == 0)
{
return v_x_3598_;
}
else
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_nat_dec_le(v___x_3612_, v___x_3612_);
if (v___x_3614_ == 0)
{
if (v___x_3613_ == 0)
{
return v_x_3598_;
}
else
{
size_t v___x_3615_; size_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = ((size_t)0ULL);
v___x_3616_ = lean_usize_of_nat(v___x_3612_);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3610_, v___x_3615_, v___x_3616_, v_x_3598_);
return v___x_3617_;
}
}
else
{
size_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = ((size_t)0ULL);
v___x_3619_ = lean_usize_of_nat(v___x_3612_);
v___x_3620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3610_, v___x_3618_, v___x_3619_, v_x_3598_);
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3621_, size_t v_i_3622_, size_t v_stop_3623_, lean_object* v_b_3624_){
_start:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_eq(v_i_3622_, v_stop_3623_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; 
v___x_3626_ = lean_array_uget_borrowed(v_as_3621_, v_i_3622_);
v___x_3627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3626_, v_b_3624_);
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3622_, v___x_3628_);
v_i_3622_ = v___x_3629_;
v_b_3624_ = v___x_3627_;
goto _start;
}
else
{
return v_b_3624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3631_, lean_object* v_i_3632_, lean_object* v_stop_3633_, lean_object* v_b_3634_){
_start:
{
size_t v_i_boxed_3635_; size_t v_stop_boxed_3636_; lean_object* v_res_3637_; 
v_i_boxed_3635_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_stop_boxed_3636_ = lean_unbox_usize(v_stop_3633_);
lean_dec(v_stop_3633_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3631_, v_i_boxed_3635_, v_stop_boxed_3636_, v_b_3634_);
lean_dec_ref(v_as_3631_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3638_, lean_object* v_x_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3638_, v_x_3639_);
lean_dec_ref(v_x_3638_);
return v_res_3640_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3642_, size_t v_x_3643_, size_t v_x_3644_, lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_object* v_cs_3646_; lean_object* v___x_3647_; size_t v___x_3648_; lean_object* v_j_3649_; lean_object* v___x_3650_; size_t v___x_3651_; size_t v___x_3652_; size_t v___x_3653_; size_t v___x_3654_; size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_cs_3646_ = lean_ctor_get(v_x_3642_, 0);
v___x_3647_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3648_ = lean_usize_shift_right(v_x_3643_, v_x_3644_);
v_j_3649_ = lean_usize_to_nat(v___x_3648_);
v___x_3650_ = lean_array_get_borrowed(v___x_3647_, v_cs_3646_, v_j_3649_);
v___x_3651_ = ((size_t)1ULL);
v___x_3652_ = lean_usize_shift_left(v___x_3651_, v_x_3644_);
v___x_3653_ = lean_usize_sub(v___x_3652_, v___x_3651_);
v___x_3654_ = lean_usize_land(v_x_3643_, v___x_3653_);
v___x_3655_ = ((size_t)5ULL);
v___x_3656_ = lean_usize_sub(v_x_3644_, v___x_3655_);
v___x_3657_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3650_, v___x_3654_, v___x_3656_, v_x_3645_);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_j_3649_, v___x_3658_);
lean_dec(v_j_3649_);
v___x_3660_ = lean_array_get_size(v_cs_3646_);
v___x_3661_ = lean_nat_dec_lt(v___x_3659_, v___x_3660_);
if (v___x_3661_ == 0)
{
lean_dec(v___x_3659_);
return v___x_3657_;
}
else
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_nat_dec_le(v___x_3660_, v___x_3660_);
if (v___x_3662_ == 0)
{
if (v___x_3661_ == 0)
{
lean_dec(v___x_3659_);
return v___x_3657_;
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_usize_of_nat(v___x_3659_);
lean_dec(v___x_3659_);
v___x_3664_ = lean_usize_of_nat(v___x_3660_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3646_, v___x_3663_, v___x_3664_, v___x_3657_);
return v___x_3665_;
}
}
else
{
size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_usize_of_nat(v___x_3659_);
lean_dec(v___x_3659_);
v___x_3667_ = lean_usize_of_nat(v___x_3660_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3646_, v___x_3666_, v___x_3667_, v___x_3657_);
return v___x_3668_;
}
}
}
else
{
lean_object* v_vs_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v_vs_3669_ = lean_ctor_get(v_x_3642_, 0);
v___x_3670_ = lean_usize_to_nat(v_x_3643_);
v___x_3671_ = lean_array_get_size(v_vs_3669_);
v___x_3672_ = lean_nat_dec_lt(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_dec(v___x_3670_);
return v_x_3645_;
}
else
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_nat_dec_le(v___x_3671_, v___x_3671_);
if (v___x_3673_ == 0)
{
if (v___x_3672_ == 0)
{
lean_dec(v___x_3670_);
return v_x_3645_;
}
else
{
size_t v___x_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = lean_usize_of_nat(v___x_3670_);
lean_dec(v___x_3670_);
v___x_3675_ = lean_usize_of_nat(v___x_3671_);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3669_, v___x_3674_, v___x_3675_, v_x_3645_);
return v___x_3676_;
}
}
else
{
size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_usize_of_nat(v___x_3670_);
lean_dec(v___x_3670_);
v___x_3678_ = lean_usize_of_nat(v___x_3671_);
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3669_, v___x_3677_, v___x_3678_, v_x_3645_);
return v___x_3679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_){
_start:
{
size_t v_x_1528__boxed_3684_; size_t v_x_1529__boxed_3685_; lean_object* v_res_3686_; 
v_x_1528__boxed_3684_ = lean_unbox_usize(v_x_3681_);
lean_dec(v_x_3681_);
v_x_1529__boxed_3685_ = lean_unbox_usize(v_x_3682_);
lean_dec(v_x_3682_);
v_res_3686_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3680_, v_x_1528__boxed_3684_, v_x_1529__boxed_3685_, v_x_3683_);
lean_dec_ref(v_x_3680_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3687_, lean_object* v_init_3688_, lean_object* v_start_3689_){
_start:
{
lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = lean_nat_dec_eq(v_start_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v_root_3692_; lean_object* v_tail_3693_; size_t v_shift_3694_; lean_object* v_tailOff_3695_; uint8_t v___x_3696_; 
v_root_3692_ = lean_ctor_get(v_t_3687_, 0);
v_tail_3693_ = lean_ctor_get(v_t_3687_, 1);
v_shift_3694_ = lean_ctor_get_usize(v_t_3687_, 4);
v_tailOff_3695_ = lean_ctor_get(v_t_3687_, 3);
v___x_3696_ = lean_nat_dec_le(v_tailOff_3695_, v_start_3689_);
if (v___x_3696_ == 0)
{
size_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3697_ = lean_usize_of_nat(v_start_3689_);
v___x_3698_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3692_, v___x_3697_, v_shift_3694_, v_init_3688_);
v___x_3699_ = lean_array_get_size(v_tail_3693_);
v___x_3700_ = lean_nat_dec_lt(v___x_3690_, v___x_3699_);
if (v___x_3700_ == 0)
{
return v___x_3698_;
}
else
{
uint8_t v___x_3701_; 
v___x_3701_ = lean_nat_dec_le(v___x_3699_, v___x_3699_);
if (v___x_3701_ == 0)
{
if (v___x_3700_ == 0)
{
return v___x_3698_;
}
else
{
size_t v___x_3702_; size_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = ((size_t)0ULL);
v___x_3703_ = lean_usize_of_nat(v___x_3699_);
v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3693_, v___x_3702_, v___x_3703_, v___x_3698_);
return v___x_3704_;
}
}
else
{
size_t v___x_3705_; size_t v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = ((size_t)0ULL);
v___x_3706_ = lean_usize_of_nat(v___x_3699_);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3693_, v___x_3705_, v___x_3706_, v___x_3698_);
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_nat_sub(v_start_3689_, v_tailOff_3695_);
v___x_3709_ = lean_array_get_size(v_tail_3693_);
v___x_3710_ = lean_nat_dec_lt(v___x_3708_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_dec(v___x_3708_);
return v_init_3688_;
}
else
{
uint8_t v___x_3711_; 
v___x_3711_ = lean_nat_dec_le(v___x_3709_, v___x_3709_);
if (v___x_3711_ == 0)
{
if (v___x_3710_ == 0)
{
lean_dec(v___x_3708_);
return v_init_3688_;
}
else
{
size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = lean_usize_of_nat(v___x_3708_);
lean_dec(v___x_3708_);
v___x_3713_ = lean_usize_of_nat(v___x_3709_);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3693_, v___x_3712_, v___x_3713_, v_init_3688_);
return v___x_3714_;
}
}
else
{
size_t v___x_3715_; size_t v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_usize_of_nat(v___x_3708_);
lean_dec(v___x_3708_);
v___x_3716_ = lean_usize_of_nat(v___x_3709_);
v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3693_, v___x_3715_, v___x_3716_, v_init_3688_);
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_root_3718_; lean_object* v_tail_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v_root_3718_ = lean_ctor_get(v_t_3687_, 0);
v_tail_3719_ = lean_ctor_get(v_t_3687_, 1);
v___x_3720_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3718_, v_init_3688_);
v___x_3721_ = lean_array_get_size(v_tail_3719_);
v___x_3722_ = lean_nat_dec_lt(v___x_3690_, v___x_3721_);
if (v___x_3722_ == 0)
{
return v___x_3720_;
}
else
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_nat_dec_le(v___x_3721_, v___x_3721_);
if (v___x_3723_ == 0)
{
if (v___x_3722_ == 0)
{
return v___x_3720_;
}
else
{
size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = ((size_t)0ULL);
v___x_3725_ = lean_usize_of_nat(v___x_3721_);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3719_, v___x_3724_, v___x_3725_, v___x_3720_);
return v___x_3726_;
}
}
else
{
size_t v___x_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((size_t)0ULL);
v___x_3728_ = lean_usize_of_nat(v___x_3721_);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3719_, v___x_3727_, v___x_3728_, v___x_3720_);
return v___x_3729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3730_, lean_object* v_init_3731_, lean_object* v_start_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3730_, v_init_3731_, v_start_3732_);
lean_dec(v_start_3732_);
lean_dec_ref(v_t_3730_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3734_){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v_unreported_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3748_; 
v___x_3735_ = lean_unsigned_to_nat(32u);
v___x_3736_ = lean_mk_empty_array_with_capacity(v___x_3735_);
lean_dec_ref(v___x_3736_);
v___x_3737_ = lean_unsigned_to_nat(0u);
v___x_3738_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3739_ = lean_ctor_get(v_log_3734_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_log_3734_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; lean_object* v_unused_3750_; 
v_unused_3749_ = lean_ctor_get(v_log_3734_, 2);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_log_3734_, 0);
lean_dec(v_unused_3750_);
v___x_3741_ = v_log_3734_;
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_unreported_3739_);
lean_dec(v_log_3734_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3743_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3739_, v___x_3738_, v___x_3737_);
lean_dec_ref(v_unreported_3739_);
v___x_3744_ = l_Lean_NameSet_empty;
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 2, v___x_3744_);
lean_ctor_set(v___x_3741_, 1, v___x_3743_);
lean_ctor_set(v___x_3741_, 0, v___x_3738_);
v___x_3746_ = v___x_3741_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3751_, size_t v_i_3752_, size_t v_stop_3753_, lean_object* v_b_3754_){
_start:
{
lean_object* v___y_3756_; uint8_t v___x_3760_; 
v___x_3760_ = lean_usize_dec_eq(v_i_3752_, v_stop_3753_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; uint8_t v_severity_3762_; 
v___x_3761_ = lean_array_uget_borrowed(v_as_3751_, v_i_3752_);
v_severity_3762_ = lean_ctor_get_uint8(v___x_3761_, sizeof(void*)*5 + 1);
if (v_severity_3762_ == 1)
{
lean_object* v___x_3763_; 
lean_inc(v___x_3761_);
v___x_3763_ = l_Lean_PersistentArray_push___redArg(v_b_3754_, v___x_3761_);
v___y_3756_ = v___x_3763_;
goto v___jp_3755_;
}
else
{
v___y_3756_ = v_b_3754_;
goto v___jp_3755_;
}
}
else
{
return v_b_3754_;
}
v___jp_3755_:
{
size_t v___x_3757_; size_t v___x_3758_; 
v___x_3757_ = ((size_t)1ULL);
v___x_3758_ = lean_usize_add(v_i_3752_, v___x_3757_);
v_i_3752_ = v___x_3758_;
v_b_3754_ = v___y_3756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3764_, lean_object* v_i_3765_, lean_object* v_stop_3766_, lean_object* v_b_3767_){
_start:
{
size_t v_i_boxed_3768_; size_t v_stop_boxed_3769_; lean_object* v_res_3770_; 
v_i_boxed_3768_ = lean_unbox_usize(v_i_3765_);
lean_dec(v_i_3765_);
v_stop_boxed_3769_ = lean_unbox_usize(v_stop_3766_);
lean_dec(v_stop_3766_);
v_res_3770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3764_, v_i_boxed_3768_, v_stop_boxed_3769_, v_b_3767_);
lean_dec_ref(v_as_3764_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
if (lean_obj_tag(v_x_3771_) == 0)
{
lean_object* v_cs_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_cs_3773_ = lean_ctor_get(v_x_3771_, 0);
v___x_3774_ = lean_unsigned_to_nat(0u);
v___x_3775_ = lean_array_get_size(v_cs_3773_);
v___x_3776_ = lean_nat_dec_lt(v___x_3774_, v___x_3775_);
if (v___x_3776_ == 0)
{
return v_x_3772_;
}
else
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_nat_dec_le(v___x_3775_, v___x_3775_);
if (v___x_3777_ == 0)
{
if (v___x_3776_ == 0)
{
return v_x_3772_;
}
else
{
size_t v___x_3778_; size_t v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = ((size_t)0ULL);
v___x_3779_ = lean_usize_of_nat(v___x_3775_);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3773_, v___x_3778_, v___x_3779_, v_x_3772_);
return v___x_3780_;
}
}
else
{
size_t v___x_3781_; size_t v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = ((size_t)0ULL);
v___x_3782_ = lean_usize_of_nat(v___x_3775_);
v___x_3783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3773_, v___x_3781_, v___x_3782_, v_x_3772_);
return v___x_3783_;
}
}
}
else
{
lean_object* v_vs_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_vs_3784_ = lean_ctor_get(v_x_3771_, 0);
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_array_get_size(v_vs_3784_);
v___x_3787_ = lean_nat_dec_lt(v___x_3785_, v___x_3786_);
if (v___x_3787_ == 0)
{
return v_x_3772_;
}
else
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_nat_dec_le(v___x_3786_, v___x_3786_);
if (v___x_3788_ == 0)
{
if (v___x_3787_ == 0)
{
return v_x_3772_;
}
else
{
size_t v___x_3789_; size_t v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = ((size_t)0ULL);
v___x_3790_ = lean_usize_of_nat(v___x_3786_);
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3784_, v___x_3789_, v___x_3790_, v_x_3772_);
return v___x_3791_;
}
}
else
{
size_t v___x_3792_; size_t v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = ((size_t)0ULL);
v___x_3793_ = lean_usize_of_nat(v___x_3786_);
v___x_3794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3784_, v___x_3792_, v___x_3793_, v_x_3772_);
return v___x_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3795_, size_t v_i_3796_, size_t v_stop_3797_, lean_object* v_b_3798_){
_start:
{
uint8_t v___x_3799_; 
v___x_3799_ = lean_usize_dec_eq(v_i_3796_, v_stop_3797_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3801_; size_t v___x_3802_; size_t v___x_3803_; 
v___x_3800_ = lean_array_uget_borrowed(v_as_3795_, v_i_3796_);
v___x_3801_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3800_, v_b_3798_);
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3796_, v___x_3802_);
v_i_3796_ = v___x_3803_;
v_b_3798_ = v___x_3801_;
goto _start;
}
else
{
return v_b_3798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3805_, lean_object* v_i_3806_, lean_object* v_stop_3807_, lean_object* v_b_3808_){
_start:
{
size_t v_i_boxed_3809_; size_t v_stop_boxed_3810_; lean_object* v_res_3811_; 
v_i_boxed_3809_ = lean_unbox_usize(v_i_3806_);
lean_dec(v_i_3806_);
v_stop_boxed_3810_ = lean_unbox_usize(v_stop_3807_);
lean_dec(v_stop_3807_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3805_, v_i_boxed_3809_, v_stop_boxed_3810_, v_b_3808_);
lean_dec_ref(v_as_3805_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3812_, lean_object* v_x_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3812_, v_x_3813_);
lean_dec_ref(v_x_3812_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3815_, size_t v_x_3816_, size_t v_x_3817_, lean_object* v_x_3818_){
_start:
{
if (lean_obj_tag(v_x_3815_) == 0)
{
lean_object* v_cs_3819_; lean_object* v___x_3820_; size_t v___x_3821_; lean_object* v_j_3822_; lean_object* v___x_3823_; size_t v___x_3824_; size_t v___x_3825_; size_t v___x_3826_; size_t v___x_3827_; size_t v___x_3828_; size_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_cs_3819_ = lean_ctor_get(v_x_3815_, 0);
v___x_3820_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3821_ = lean_usize_shift_right(v_x_3816_, v_x_3817_);
v_j_3822_ = lean_usize_to_nat(v___x_3821_);
v___x_3823_ = lean_array_get_borrowed(v___x_3820_, v_cs_3819_, v_j_3822_);
v___x_3824_ = ((size_t)1ULL);
v___x_3825_ = lean_usize_shift_left(v___x_3824_, v_x_3817_);
v___x_3826_ = lean_usize_sub(v___x_3825_, v___x_3824_);
v___x_3827_ = lean_usize_land(v_x_3816_, v___x_3826_);
v___x_3828_ = ((size_t)5ULL);
v___x_3829_ = lean_usize_sub(v_x_3817_, v___x_3828_);
v___x_3830_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3823_, v___x_3827_, v___x_3829_, v_x_3818_);
v___x_3831_ = lean_unsigned_to_nat(1u);
v___x_3832_ = lean_nat_add(v_j_3822_, v___x_3831_);
lean_dec(v_j_3822_);
v___x_3833_ = lean_array_get_size(v_cs_3819_);
v___x_3834_ = lean_nat_dec_lt(v___x_3832_, v___x_3833_);
if (v___x_3834_ == 0)
{
lean_dec(v___x_3832_);
return v___x_3830_;
}
else
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_le(v___x_3833_, v___x_3833_);
if (v___x_3835_ == 0)
{
if (v___x_3834_ == 0)
{
lean_dec(v___x_3832_);
return v___x_3830_;
}
else
{
size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_usize_of_nat(v___x_3832_);
lean_dec(v___x_3832_);
v___x_3837_ = lean_usize_of_nat(v___x_3833_);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3819_, v___x_3836_, v___x_3837_, v___x_3830_);
return v___x_3838_;
}
}
else
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_usize_of_nat(v___x_3832_);
lean_dec(v___x_3832_);
v___x_3840_ = lean_usize_of_nat(v___x_3833_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3819_, v___x_3839_, v___x_3840_, v___x_3830_);
return v___x_3841_;
}
}
}
else
{
lean_object* v_vs_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v_vs_3842_ = lean_ctor_get(v_x_3815_, 0);
v___x_3843_ = lean_usize_to_nat(v_x_3816_);
v___x_3844_ = lean_array_get_size(v_vs_3842_);
v___x_3845_ = lean_nat_dec_lt(v___x_3843_, v___x_3844_);
if (v___x_3845_ == 0)
{
lean_dec(v___x_3843_);
return v_x_3818_;
}
else
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_nat_dec_le(v___x_3844_, v___x_3844_);
if (v___x_3846_ == 0)
{
if (v___x_3845_ == 0)
{
lean_dec(v___x_3843_);
return v_x_3818_;
}
else
{
size_t v___x_3847_; size_t v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = lean_usize_of_nat(v___x_3843_);
lean_dec(v___x_3843_);
v___x_3848_ = lean_usize_of_nat(v___x_3844_);
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3842_, v___x_3847_, v___x_3848_, v_x_3818_);
return v___x_3849_;
}
}
else
{
size_t v___x_3850_; size_t v___x_3851_; lean_object* v___x_3852_; 
v___x_3850_ = lean_usize_of_nat(v___x_3843_);
lean_dec(v___x_3843_);
v___x_3851_ = lean_usize_of_nat(v___x_3844_);
v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3842_, v___x_3850_, v___x_3851_, v_x_3818_);
return v___x_3852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_){
_start:
{
size_t v_x_1527__boxed_3857_; size_t v_x_1528__boxed_3858_; lean_object* v_res_3859_; 
v_x_1527__boxed_3857_ = lean_unbox_usize(v_x_3854_);
lean_dec(v_x_3854_);
v_x_1528__boxed_3858_ = lean_unbox_usize(v_x_3855_);
lean_dec(v_x_3855_);
v_res_3859_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3853_, v_x_1527__boxed_3857_, v_x_1528__boxed_3858_, v_x_3856_);
lean_dec_ref(v_x_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3860_, lean_object* v_init_3861_, lean_object* v_start_3862_){
_start:
{
lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = lean_nat_dec_eq(v_start_3862_, v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v_root_3865_; lean_object* v_tail_3866_; size_t v_shift_3867_; lean_object* v_tailOff_3868_; uint8_t v___x_3869_; 
v_root_3865_ = lean_ctor_get(v_t_3860_, 0);
v_tail_3866_ = lean_ctor_get(v_t_3860_, 1);
v_shift_3867_ = lean_ctor_get_usize(v_t_3860_, 4);
v_tailOff_3868_ = lean_ctor_get(v_t_3860_, 3);
v___x_3869_ = lean_nat_dec_le(v_tailOff_3868_, v_start_3862_);
if (v___x_3869_ == 0)
{
size_t v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3870_ = lean_usize_of_nat(v_start_3862_);
v___x_3871_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3865_, v___x_3870_, v_shift_3867_, v_init_3861_);
v___x_3872_ = lean_array_get_size(v_tail_3866_);
v___x_3873_ = lean_nat_dec_lt(v___x_3863_, v___x_3872_);
if (v___x_3873_ == 0)
{
return v___x_3871_;
}
else
{
uint8_t v___x_3874_; 
v___x_3874_ = lean_nat_dec_le(v___x_3872_, v___x_3872_);
if (v___x_3874_ == 0)
{
if (v___x_3873_ == 0)
{
return v___x_3871_;
}
else
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = ((size_t)0ULL);
v___x_3876_ = lean_usize_of_nat(v___x_3872_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3866_, v___x_3875_, v___x_3876_, v___x_3871_);
return v___x_3877_;
}
}
else
{
size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = ((size_t)0ULL);
v___x_3879_ = lean_usize_of_nat(v___x_3872_);
v___x_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3866_, v___x_3878_, v___x_3879_, v___x_3871_);
return v___x_3880_;
}
}
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3881_ = lean_nat_sub(v_start_3862_, v_tailOff_3868_);
v___x_3882_ = lean_array_get_size(v_tail_3866_);
v___x_3883_ = lean_nat_dec_lt(v___x_3881_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_dec(v___x_3881_);
return v_init_3861_;
}
else
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_nat_dec_le(v___x_3882_, v___x_3882_);
if (v___x_3884_ == 0)
{
if (v___x_3883_ == 0)
{
lean_dec(v___x_3881_);
return v_init_3861_;
}
else
{
size_t v___x_3885_; size_t v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_usize_of_nat(v___x_3881_);
lean_dec(v___x_3881_);
v___x_3886_ = lean_usize_of_nat(v___x_3882_);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3866_, v___x_3885_, v___x_3886_, v_init_3861_);
return v___x_3887_;
}
}
else
{
size_t v___x_3888_; size_t v___x_3889_; lean_object* v___x_3890_; 
v___x_3888_ = lean_usize_of_nat(v___x_3881_);
lean_dec(v___x_3881_);
v___x_3889_ = lean_usize_of_nat(v___x_3882_);
v___x_3890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3866_, v___x_3888_, v___x_3889_, v_init_3861_);
return v___x_3890_;
}
}
}
}
else
{
lean_object* v_root_3891_; lean_object* v_tail_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v_root_3891_ = lean_ctor_get(v_t_3860_, 0);
v_tail_3892_ = lean_ctor_get(v_t_3860_, 1);
v___x_3893_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3891_, v_init_3861_);
v___x_3894_ = lean_array_get_size(v_tail_3892_);
v___x_3895_ = lean_nat_dec_lt(v___x_3863_, v___x_3894_);
if (v___x_3895_ == 0)
{
return v___x_3893_;
}
else
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_le(v___x_3894_, v___x_3894_);
if (v___x_3896_ == 0)
{
if (v___x_3895_ == 0)
{
return v___x_3893_;
}
else
{
size_t v___x_3897_; size_t v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = ((size_t)0ULL);
v___x_3898_ = lean_usize_of_nat(v___x_3894_);
v___x_3899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3892_, v___x_3897_, v___x_3898_, v___x_3893_);
return v___x_3899_;
}
}
else
{
size_t v___x_3900_; size_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3900_ = ((size_t)0ULL);
v___x_3901_ = lean_usize_of_nat(v___x_3894_);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3892_, v___x_3900_, v___x_3901_, v___x_3893_);
return v___x_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3903_, lean_object* v_init_3904_, lean_object* v_start_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3903_, v_init_3904_, v_start_3905_);
lean_dec(v_start_3905_);
lean_dec_ref(v_t_3903_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3907_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v_unreported_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3921_; 
v___x_3908_ = lean_unsigned_to_nat(32u);
v___x_3909_ = lean_mk_empty_array_with_capacity(v___x_3908_);
lean_dec_ref(v___x_3909_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3912_ = lean_ctor_get(v_log_3907_, 1);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_log_3907_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3922_ = lean_ctor_get(v_log_3907_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_log_3907_, 0);
lean_dec(v_unused_3923_);
v___x_3914_ = v_log_3907_;
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_unreported_3912_);
lean_dec(v_log_3907_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3916_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3912_, v___x_3911_, v___x_3910_);
lean_dec_ref(v_unreported_3912_);
v___x_3917_ = l_Lean_NameSet_empty;
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 2, v___x_3917_);
lean_ctor_set(v___x_3914_, 1, v___x_3916_);
lean_ctor_set(v___x_3914_, 0, v___x_3911_);
v___x_3919_ = v___x_3914_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3924_, lean_object* v_log_3925_, lean_object* v_f_3926_){
_start:
{
lean_object* v_unreported_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_unreported_3927_ = lean_ctor_get(v_log_3925_, 1);
lean_inc_ref(v_unreported_3927_);
lean_dec_ref(v_log_3925_);
v___x_3928_ = lean_unsigned_to_nat(0u);
v___x_3929_ = l_Lean_PersistentArray_forM___redArg(v_inst_3924_, v_unreported_3927_, v_f_3926_, v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3930_, lean_object* v_inst_3931_, lean_object* v_log_3932_, lean_object* v_f_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_MessageLog_forM___redArg(v_inst_3931_, v_log_3932_, v_f_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3935_){
_start:
{
lean_object* v_unreported_3936_; lean_object* v___x_3937_; 
v_unreported_3936_ = lean_ctor_get(v_log_3935_, 1);
v___x_3937_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_MessageLog_toList(v_log_3938_);
lean_dec_ref(v_log_3938_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3940_){
_start:
{
lean_object* v_unreported_3941_; lean_object* v___x_3942_; 
v_unreported_3941_ = lean_ctor_get(v_log_3940_, 1);
v___x_3942_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_MessageLog_toArray(v_log_3943_);
lean_dec_ref(v_log_3943_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3945_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_unsigned_to_nat(2u);
v___x_3947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
lean_ctor_set(v___x_3947_, 1, v_msg_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3948_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v_msg_3948_);
v___x_3951_ = l_Lean_MessageData_nestD(v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3952_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = l_Lean_MessageData_ofExpr(v_e_3952_);
v___x_3954_ = l_Lean_indentD(v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3955_, lean_object* v_msg_3956_){
_start:
{
lean_object* v_env_3958_; lean_object* v_mctx_3959_; lean_object* v_lctx_3960_; lean_object* v_opts_3961_; lean_object* v_currNamespace_3962_; lean_object* v_openDecls_3963_; lean_object* v___x_3964_; lean_object* v_msg_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_env_3958_ = lean_ctor_get(v_ctx_3955_, 0);
v_mctx_3959_ = lean_ctor_get(v_ctx_3955_, 1);
v_lctx_3960_ = lean_ctor_get(v_ctx_3955_, 2);
v_opts_3961_ = lean_ctor_get(v_ctx_3955_, 3);
v_currNamespace_3962_ = lean_ctor_get(v_ctx_3955_, 4);
v_openDecls_3963_ = lean_ctor_get(v_ctx_3955_, 5);
lean_inc(v_openDecls_3963_);
lean_inc(v_currNamespace_3962_);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_currNamespace_3962_);
lean_ctor_set(v___x_3964_, 1, v_openDecls_3963_);
v_msg_3965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3965_, 0, v___x_3964_);
lean_ctor_set(v_msg_3965_, 1, v_msg_3956_);
lean_inc_ref(v_opts_3961_);
lean_inc_ref(v_lctx_3960_);
lean_inc_ref(v_mctx_3959_);
lean_inc_ref(v_env_3958_);
v___x_3966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3966_, 0, v_env_3958_);
lean_ctor_set(v___x_3966_, 1, v_mctx_3959_);
lean_ctor_set(v___x_3966_, 2, v_lctx_3960_);
lean_ctor_set(v___x_3966_, 3, v_opts_3961_);
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v___x_3968_ = l_Lean_MessageData_format(v_msg_3965_, v___x_3967_);
v___x_3969_ = l_Std_Format_defWidth;
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = l_Std_Format_pretty(v___x_3968_, v___x_3969_, v___x_3970_, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3972_, lean_object* v_msg_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3972_, v_msg_3973_);
lean_dec_ref(v_ctx_3972_);
return v_res_3975_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_3976_, lean_object* v_a_3977_, uint8_t v_b_3978_){
_start:
{
lean_object* v_str_3979_; lean_object* v_startInclusive_3980_; lean_object* v_endExclusive_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v_str_3979_ = lean_ctor_get(v_s_3976_, 0);
v_startInclusive_3980_ = lean_ctor_get(v_s_3976_, 1);
v_endExclusive_3981_ = lean_ctor_get(v_s_3976_, 2);
v___x_3982_ = lean_nat_sub(v_endExclusive_3981_, v_startInclusive_3980_);
v___x_3983_ = lean_nat_dec_eq(v_a_3977_, v___x_3982_);
lean_dec(v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; uint32_t v___x_3985_; uint32_t v___x_3986_; uint8_t v___x_3987_; 
v___x_3984_ = lean_nat_add(v_startInclusive_3980_, v_a_3977_);
lean_dec(v_a_3977_);
v___x_3985_ = lean_string_utf8_get_fast(v_str_3979_, v___x_3984_);
v___x_3986_ = 10;
v___x_3987_ = lean_uint32_dec_eq(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_string_utf8_next_fast(v_str_3979_, v___x_3984_);
lean_dec(v___x_3984_);
v___x_3989_ = lean_nat_sub(v___x_3988_, v_startInclusive_3980_);
v_a_3977_ = v___x_3989_;
v_b_3978_ = v___x_3987_;
goto _start;
}
else
{
lean_dec(v___x_3984_);
return v___x_3987_;
}
}
else
{
lean_dec(v_a_3977_);
return v_b_3978_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_3991_, lean_object* v_a_3992_, lean_object* v_b_3993_){
_start:
{
uint8_t v_b_boxed_3994_; uint8_t v_res_3995_; lean_object* v_r_3996_; 
v_b_boxed_3994_ = lean_unbox(v_b_3993_);
v_res_3995_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3991_, v_a_3992_, v_b_boxed_3994_);
lean_dec_ref(v_s_3991_);
v_r_3996_ = lean_box(v_res_3995_);
return v_r_3996_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_3997_){
_start:
{
lean_object* v_searcher_3998_; uint8_t v___x_3999_; uint8_t v___x_4000_; 
v_searcher_3998_ = lean_unsigned_to_nat(0u);
v___x_3999_ = 0;
v___x_4000_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3997_, v_searcher_3998_, v___x_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4001_){
_start:
{
uint8_t v_res_4002_; lean_object* v_r_4003_; 
v_res_4002_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4001_);
lean_dec_ref(v_s_4001_);
v_r_4003_ = lean_box(v_res_4002_);
return v_r_4003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4004_, lean_object* v_val_4005_, lean_object* v_a_4006_, lean_object* v_b_4007_){
_start:
{
lean_object* v_startInclusive_4008_; lean_object* v_endExclusive_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v_startInclusive_4008_ = lean_ctor_get(v___x_4004_, 1);
v_endExclusive_4009_ = lean_ctor_get(v___x_4004_, 2);
v___x_4010_ = lean_nat_sub(v_endExclusive_4009_, v_startInclusive_4008_);
v___x_4011_ = lean_nat_dec_eq(v_a_4006_, v___x_4010_);
lean_dec(v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = lean_string_utf8_next_fast(v_val_4005_, v_a_4006_);
lean_dec(v_a_4006_);
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_add(v_b_4007_, v___x_4013_);
lean_dec(v_b_4007_);
v_a_4006_ = v___x_4012_;
v_b_4007_ = v___x_4014_;
goto _start;
}
else
{
lean_dec(v_a_4006_);
return v_b_4007_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4016_, lean_object* v_val_4017_, lean_object* v_a_4018_, lean_object* v_b_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4016_, v_val_4017_, v_a_4018_, v_b_4019_);
lean_dec_ref(v_val_4017_);
lean_dec_ref(v___x_4016_);
return v_res_4020_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_4025_ = l_Lean_MessageData_ofFormat(v___x_4024_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_4030_ = l_Lean_MessageData_ofFormat(v___x_4029_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4032_ = l_Lean_MessageData_ofFormat(v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4033_, lean_object* v_maxInlineLength_4034_, lean_object* v_ctx_4035_){
_start:
{
lean_object* v_msg_4037_; lean_object* v___x_4038_; uint8_t v___y_4040_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v_msg_4037_ = l_Lean_MessageData_ofExpr(v_e_4033_);
lean_inc_ref(v_msg_4037_);
v___x_4038_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4035_, v_msg_4037_);
v___x_4048_ = lean_unsigned_to_nat(0u);
v___x_4049_ = lean_string_utf8_byte_size(v___x_4038_);
lean_inc_ref(v___x_4038_);
v___x_4050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4038_);
lean_ctor_set(v___x_4050_, 1, v___x_4048_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
v___x_4051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4050_, v___x_4038_, v___x_4048_, v___x_4048_);
lean_dec_ref(v___x_4038_);
v___x_4052_ = lean_nat_dec_lt(v_maxInlineLength_4034_, v___x_4051_);
lean_dec(v___x_4051_);
if (v___x_4052_ == 0)
{
uint8_t v___x_4053_; 
v___x_4053_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4050_);
lean_dec_ref_known(v___x_4050_, 3);
v___y_4040_ = v___x_4053_;
goto v___jp_4039_;
}
else
{
lean_dec_ref_known(v___x_4050_, 3);
v___y_4040_ = v___x_4052_;
goto v___jp_4039_;
}
v___jp_4039_:
{
if (v___y_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4041_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
lean_ctor_set(v___x_4042_, 1, v_msg_4037_);
v___x_4043_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
return v___x_4044_;
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = l_Lean_indentD(v_msg_4037_);
v___x_4046_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4045_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
return v___x_4047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4054_, lean_object* v_maxInlineLength_4055_, lean_object* v_ctx_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_inlineExpr___lam__0(v_e_4054_, v_maxInlineLength_4055_, v_ctx_4056_);
lean_dec_ref(v_ctx_4056_);
lean_dec(v_maxInlineLength_4055_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4059_, lean_object* v_x_4060_){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4062_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4063_ = l_Lean_MessageData_ofExpr(v_e_4059_);
v___x_4064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4064_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4067_, lean_object* v_x_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_inlineExpr___lam__2(v_e_4067_, v_x_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4071_, lean_object* v_maxInlineLength_4072_){
_start:
{
lean_object* v___f_4073_; lean_object* v___f_4074_; lean_object* v___f_4075_; lean_object* v___x_4076_; 
lean_inc_ref_n(v_e_4071_, 2);
v___f_4073_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4073_, 0, v_e_4071_);
lean_closure_set(v___f_4073_, 1, v_maxInlineLength_4072_);
v___f_4074_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4074_, 0, v_e_4071_);
v___f_4075_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4075_, 0, v_e_4071_);
v___x_4076_ = l_Lean_MessageData_lazy(v___f_4073_, v___f_4074_, v___f_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4077_, lean_object* v_val_4078_, lean_object* v_inst_4079_, lean_object* v_R_4080_, lean_object* v_a_4081_, lean_object* v_b_4082_, lean_object* v_c_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4077_, v_val_4078_, v_a_4081_, v_b_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4085_, lean_object* v_val_4086_, lean_object* v_inst_4087_, lean_object* v_R_4088_, lean_object* v_a_4089_, lean_object* v_b_4090_, lean_object* v_c_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4085_, v_val_4086_, v_inst_4087_, v_R_4088_, v_a_4089_, v_b_4090_, v_c_4091_);
lean_dec_ref(v_val_4086_);
lean_dec_ref(v___x_4085_);
return v_res_4092_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4093_, lean_object* v_inst_4094_, lean_object* v_R_4095_, lean_object* v_a_4096_, uint8_t v_b_4097_, lean_object* v_c_4098_){
_start:
{
uint8_t v___x_4099_; 
v___x_4099_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4093_, v_a_4096_, v_b_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4100_, lean_object* v_inst_4101_, lean_object* v_R_4102_, lean_object* v_a_4103_, lean_object* v_b_4104_, lean_object* v_c_4105_){
_start:
{
uint8_t v_b_boxed_4106_; uint8_t v_res_4107_; lean_object* v_r_4108_; 
v_b_boxed_4106_ = lean_unbox(v_b_4104_);
v_res_4107_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4100_, v_inst_4101_, v_R_4102_, v_a_4103_, v_b_boxed_4106_, v_c_4105_);
lean_dec_ref(v_s_4100_);
v_r_4108_ = lean_box(v_res_4107_);
return v_r_4108_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4113_ = l_Lean_MessageData_ofFormat(v___x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4114_, lean_object* v_maxInlineLength_4115_, lean_object* v_ctx_4116_){
_start:
{
lean_object* v_msg_4118_; lean_object* v___x_4119_; uint8_t v___y_4121_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v_msg_4118_ = l_Lean_MessageData_ofExpr(v_e_4114_);
lean_inc_ref(v_msg_4118_);
v___x_4119_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4116_, v_msg_4118_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_string_utf8_byte_size(v___x_4119_);
lean_inc_ref(v___x_4119_);
v___x_4129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4119_);
lean_ctor_set(v___x_4129_, 1, v___x_4127_);
lean_ctor_set(v___x_4129_, 2, v___x_4128_);
v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4129_, v___x_4119_, v___x_4127_, v___x_4127_);
lean_dec_ref(v___x_4119_);
v___x_4131_ = lean_nat_dec_lt(v_maxInlineLength_4115_, v___x_4130_);
lean_dec(v___x_4130_);
if (v___x_4131_ == 0)
{
uint8_t v___x_4132_; 
v___x_4132_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4129_);
lean_dec_ref_known(v___x_4129_, 3);
v___y_4121_ = v___x_4132_;
goto v___jp_4120_;
}
else
{
lean_dec_ref_known(v___x_4129_, 3);
v___y_4121_ = v___x_4131_;
goto v___jp_4120_;
}
v___jp_4120_:
{
if (v___y_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4122_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v_msg_4118_);
v___x_4124_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_indentD(v_msg_4118_);
return v___x_4126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4133_, lean_object* v_maxInlineLength_4134_, lean_object* v_ctx_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_inlineExprTrailing___lam__0(v_e_4133_, v_maxInlineLength_4134_, v_ctx_4135_);
lean_dec_ref(v_ctx_4135_);
lean_dec(v_maxInlineLength_4134_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4138_, lean_object* v_x_4139_){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4141_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4142_ = l_Lean_MessageData_ofExpr(v_e_4138_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4146_, lean_object* v_x_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_inlineExprTrailing___lam__2(v_e_4146_, v_x_4147_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4150_, lean_object* v_maxInlineLength_4151_){
_start:
{
lean_object* v___f_4152_; lean_object* v___f_4153_; lean_object* v___f_4154_; lean_object* v___x_4155_; 
lean_inc_ref_n(v_e_4150_, 2);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4152_, 0, v_e_4150_);
lean_closure_set(v___f_4152_, 1, v_maxInlineLength_4151_);
v___f_4153_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4153_, 0, v_e_4150_);
v___f_4154_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4154_, 0, v_e_4150_);
v___x_4155_ = l_Lean_MessageData_lazy(v___f_4152_, v___f_4153_, v___f_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4160_ = l_Lean_MessageData_ofFormat(v___x_4159_);
return v___x_4160_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4164_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4165_ = l_Lean_MessageData_ofFormat(v___x_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4166_){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4167_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v_msg_4166_);
v___x_4169_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4171_, lean_object* v_inst_4172_, lean_object* v_msg_4173_){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_apply_1(v_inst_4171_, v_msg_4173_);
v___x_4175_ = lean_apply_2(v_inst_4172_, lean_box(0), v___x_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4176_, lean_object* v_inst_4177_){
_start:
{
lean_object* v___f_4178_; 
v___f_4178_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4178_, 0, v_inst_4177_);
lean_closure_set(v___f_4178_, 1, v_inst_4176_);
return v___f_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4179_, lean_object* v_n_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_){
_start:
{
lean_object* v___f_4183_; 
v___f_4183_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4183_, 0, v_inst_4182_);
lean_closure_set(v___f_4183_, 1, v_inst_4181_);
return v___f_4183_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = lean_unsigned_to_nat(32u);
v___x_4185_ = lean_mk_empty_array_with_capacity(v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4187_ = ((size_t)5ULL);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_unsigned_to_nat(32u);
v___x_4190_ = lean_mk_empty_array_with_capacity(v___x_4189_);
v___x_4191_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4190_);
lean_ctor_set(v___x_4192_, 2, v___x_4188_);
lean_ctor_set(v___x_4192_, 3, v___x_4188_);
lean_ctor_set_usize(v___x_4192_, 4, v___x_4187_);
return v___x_4192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = lean_box(1);
v___x_4194_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4195_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4194_);
lean_ctor_set(v___x_4196_, 2, v___x_4193_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4197_, lean_object* v_msgData_4198_, lean_object* v_toPure_4199_, lean_object* v_opts_4200_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4201_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4202_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4203_, 0, v_env_4197_);
lean_ctor_set(v___x_4203_, 1, v___x_4201_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
lean_ctor_set(v___x_4203_, 3, v_opts_4200_);
v___x_4204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v_msgData_4198_);
v___x_4205_ = lean_apply_2(v_toPure_4199_, lean_box(0), v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4206_, lean_object* v_toPure_4207_, lean_object* v_toBind_4208_, lean_object* v_inst_4209_, lean_object* v_env_4210_){
_start:
{
lean_object* v___f_4211_; lean_object* v___x_4212_; 
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4211_, 0, v_env_4210_);
lean_closure_set(v___f_4211_, 1, v_msgData_4206_);
lean_closure_set(v___f_4211_, 2, v_toPure_4207_);
v___x_4212_ = lean_apply_4(v_toBind_4208_, lean_box(0), lean_box(0), v_inst_4209_, v___f_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4213_, lean_object* v_inst_4214_, lean_object* v_inst_4215_, lean_object* v_msgData_4216_){
_start:
{
lean_object* v_toApplicative_4217_; lean_object* v_toBind_4218_; lean_object* v_getEnv_4219_; lean_object* v_toPure_4220_; lean_object* v___f_4221_; lean_object* v___x_4222_; 
v_toApplicative_4217_ = lean_ctor_get(v_inst_4213_, 0);
lean_inc_ref(v_toApplicative_4217_);
v_toBind_4218_ = lean_ctor_get(v_inst_4213_, 1);
lean_inc_n(v_toBind_4218_, 2);
lean_dec_ref(v_inst_4213_);
v_getEnv_4219_ = lean_ctor_get(v_inst_4214_, 0);
lean_inc(v_getEnv_4219_);
lean_dec_ref(v_inst_4214_);
v_toPure_4220_ = lean_ctor_get(v_toApplicative_4217_, 1);
lean_inc(v_toPure_4220_);
lean_dec_ref(v_toApplicative_4217_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4221_, 0, v_msgData_4216_);
lean_closure_set(v___f_4221_, 1, v_toPure_4220_);
lean_closure_set(v___f_4221_, 2, v_toBind_4218_);
lean_closure_set(v___f_4221_, 3, v_inst_4215_);
v___x_4222_ = lean_apply_4(v_toBind_4218_, lean_box(0), lean_box(0), v_getEnv_4219_, v___f_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4223_, lean_object* v_inst_4224_, lean_object* v_inst_4225_, lean_object* v_inst_4226_, lean_object* v_msgData_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_addMessageContextPartial___redArg(v_inst_4224_, v_inst_4225_, v_inst_4226_, v_msgData_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4229_, lean_object* v_mctx_4230_, lean_object* v_lctx_4231_, lean_object* v_msgData_4232_, lean_object* v_toPure_4233_, lean_object* v_opts_4234_){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4235_, 0, v_env_4229_);
lean_ctor_set(v___x_4235_, 1, v_mctx_4230_);
lean_ctor_set(v___x_4235_, 2, v_lctx_4231_);
lean_ctor_set(v___x_4235_, 3, v_opts_4234_);
v___x_4236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
lean_ctor_set(v___x_4236_, 1, v_msgData_4232_);
v___x_4237_ = lean_apply_2(v_toPure_4233_, lean_box(0), v___x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4238_, lean_object* v_mctx_4239_, lean_object* v_msgData_4240_, lean_object* v_toPure_4241_, lean_object* v_toBind_4242_, lean_object* v_inst_4243_, lean_object* v_lctx_4244_){
_start:
{
lean_object* v___f_4245_; lean_object* v___x_4246_; 
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4245_, 0, v_env_4238_);
lean_closure_set(v___f_4245_, 1, v_mctx_4239_);
lean_closure_set(v___f_4245_, 2, v_lctx_4244_);
lean_closure_set(v___f_4245_, 3, v_msgData_4240_);
lean_closure_set(v___f_4245_, 4, v_toPure_4241_);
v___x_4246_ = lean_apply_4(v_toBind_4242_, lean_box(0), lean_box(0), v_inst_4243_, v___f_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4247_, lean_object* v_msgData_4248_, lean_object* v_toPure_4249_, lean_object* v_toBind_4250_, lean_object* v_inst_4251_, lean_object* v_inst_4252_, lean_object* v_mctx_4253_){
_start:
{
lean_object* v___f_4254_; lean_object* v___x_4255_; 
lean_inc(v_toBind_4250_);
v___f_4254_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4254_, 0, v_env_4247_);
lean_closure_set(v___f_4254_, 1, v_mctx_4253_);
lean_closure_set(v___f_4254_, 2, v_msgData_4248_);
lean_closure_set(v___f_4254_, 3, v_toPure_4249_);
lean_closure_set(v___f_4254_, 4, v_toBind_4250_);
lean_closure_set(v___f_4254_, 5, v_inst_4251_);
v___x_4255_ = lean_apply_4(v_toBind_4250_, lean_box(0), lean_box(0), v_inst_4252_, v___f_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4256_, lean_object* v_msgData_4257_, lean_object* v_toPure_4258_, lean_object* v_toBind_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_env_4262_){
_start:
{
lean_object* v_getMCtx_4263_; lean_object* v___f_4264_; lean_object* v___x_4265_; 
v_getMCtx_4263_ = lean_ctor_get(v_inst_4256_, 0);
lean_inc(v_getMCtx_4263_);
lean_dec_ref(v_inst_4256_);
lean_inc(v_toBind_4259_);
v___f_4264_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4264_, 0, v_env_4262_);
lean_closure_set(v___f_4264_, 1, v_msgData_4257_);
lean_closure_set(v___f_4264_, 2, v_toPure_4258_);
lean_closure_set(v___f_4264_, 3, v_toBind_4259_);
lean_closure_set(v___f_4264_, 4, v_inst_4260_);
lean_closure_set(v___f_4264_, 5, v_inst_4261_);
v___x_4265_ = lean_apply_4(v_toBind_4259_, lean_box(0), lean_box(0), v_getMCtx_4263_, v___f_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4266_, lean_object* v_inst_4267_, lean_object* v_inst_4268_, lean_object* v_inst_4269_, lean_object* v_inst_4270_, lean_object* v_msgData_4271_){
_start:
{
lean_object* v_toApplicative_4272_; lean_object* v_toBind_4273_; lean_object* v_getEnv_4274_; lean_object* v_toPure_4275_; lean_object* v___f_4276_; lean_object* v___x_4277_; 
v_toApplicative_4272_ = lean_ctor_get(v_inst_4266_, 0);
lean_inc_ref(v_toApplicative_4272_);
v_toBind_4273_ = lean_ctor_get(v_inst_4266_, 1);
lean_inc_n(v_toBind_4273_, 2);
lean_dec_ref(v_inst_4266_);
v_getEnv_4274_ = lean_ctor_get(v_inst_4267_, 0);
lean_inc(v_getEnv_4274_);
lean_dec_ref(v_inst_4267_);
v_toPure_4275_ = lean_ctor_get(v_toApplicative_4272_, 1);
lean_inc(v_toPure_4275_);
lean_dec_ref(v_toApplicative_4272_);
v___f_4276_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4276_, 0, v_inst_4268_);
lean_closure_set(v___f_4276_, 1, v_msgData_4271_);
lean_closure_set(v___f_4276_, 2, v_toPure_4275_);
lean_closure_set(v___f_4276_, 3, v_toBind_4273_);
lean_closure_set(v___f_4276_, 4, v_inst_4270_);
lean_closure_set(v___f_4276_, 5, v_inst_4269_);
v___x_4277_ = lean_apply_4(v_toBind_4273_, lean_box(0), lean_box(0), v_getEnv_4274_, v___f_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4278_, lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_inst_4282_, lean_object* v_inst_4283_, lean_object* v_msgData_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_addMessageContextFull___redArg(v_inst_4279_, v_inst_4280_, v_inst_4281_, v_inst_4282_, v_inst_4283_, v_msgData_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4290_);
lean_dec_ref(v_s_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v_a_4295_, lean_object* v_b_4296_){
_start:
{
lean_object* v_it_4298_; lean_object* v_startInclusive_4299_; lean_object* v_endExclusive_4300_; 
if (lean_obj_tag(v_a_4295_) == 0)
{
lean_object* v_currPos_4306_; lean_object* v_searcher_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4333_; 
v_currPos_4306_ = lean_ctor_get(v_a_4295_, 0);
v_searcher_4307_ = lean_ctor_get(v_a_4295_, 1);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_a_4295_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4309_ = v_a_4295_;
v_isShared_4310_ = v_isSharedCheck_4333_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_searcher_4307_);
lean_inc(v_currPos_4306_);
lean_dec(v_a_4295_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4333_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v_startInclusive_4311_; lean_object* v_endExclusive_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v_startInclusive_4311_ = lean_ctor_get(v___x_4293_, 1);
v_endExclusive_4312_ = lean_ctor_get(v___x_4293_, 2);
v___x_4313_ = lean_nat_sub(v_endExclusive_4312_, v_startInclusive_4311_);
v___x_4314_ = lean_nat_dec_eq(v_searcher_4307_, v___x_4313_);
lean_dec(v___x_4313_);
if (v___x_4314_ == 0)
{
uint32_t v___x_4315_; uint32_t v___x_4316_; uint8_t v___x_4317_; 
v___x_4315_ = 10;
v___x_4316_ = lean_string_utf8_get_fast(v_str_4292_, v_searcher_4307_);
v___x_4317_ = lean_uint32_dec_eq(v___x_4316_, v___x_4315_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4320_; 
v___x_4318_ = lean_string_utf8_next_fast(v_str_4292_, v_searcher_4307_);
lean_dec(v_searcher_4307_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 1, v___x_4318_);
v___x_4320_ = v___x_4309_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_currPos_4306_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
v_a_4295_ = v___x_4320_;
goto _start;
}
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v_slice_4326_; lean_object* v_nextIt_4328_; 
v___x_4323_ = lean_string_utf8_next_fast(v_str_4292_, v_searcher_4307_);
v___x_4324_ = lean_nat_sub(v___x_4323_, v_searcher_4307_);
v___x_4325_ = lean_nat_add(v_searcher_4307_, v___x_4324_);
lean_dec(v___x_4324_);
v_slice_4326_ = l_String_Slice_subslice_x21(v___x_4293_, v_currPos_4306_, v_searcher_4307_);
lean_inc(v___x_4325_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 1, v___x_4325_);
lean_ctor_set(v___x_4309_, 0, v___x_4325_);
v_nextIt_4328_ = v___x_4309_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___x_4325_);
v_nextIt_4328_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v_startInclusive_4329_; lean_object* v_endExclusive_4330_; 
v_startInclusive_4329_ = lean_ctor_get(v_slice_4326_, 0);
lean_inc(v_startInclusive_4329_);
v_endExclusive_4330_ = lean_ctor_get(v_slice_4326_, 1);
lean_inc(v_endExclusive_4330_);
lean_dec_ref(v_slice_4326_);
v_it_4298_ = v_nextIt_4328_;
v_startInclusive_4299_ = v_startInclusive_4329_;
v_endExclusive_4300_ = v_endExclusive_4330_;
goto v___jp_4297_;
}
}
}
else
{
lean_object* v___x_4332_; 
lean_del_object(v___x_4309_);
lean_dec(v_searcher_4307_);
v___x_4332_ = lean_box(1);
lean_inc(v___x_4294_);
v_it_4298_ = v___x_4332_;
v_startInclusive_4299_ = v_currPos_4306_;
v_endExclusive_4300_ = v___x_4294_;
goto v___jp_4297_;
}
}
}
else
{
lean_dec(v___x_4294_);
return v_b_4296_;
}
v___jp_4297_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4301_ = lean_string_utf8_extract(v_str_4292_, v_startInclusive_4299_, v_endExclusive_4300_);
lean_dec(v_endExclusive_4300_);
lean_dec(v_startInclusive_4299_);
v___x_4302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
v___x_4303_ = l_Lean_MessageData_ofFormat(v___x_4302_);
v___x_4304_ = lean_array_push(v_b_4296_, v___x_4303_);
v_a_4295_ = v_it_4298_;
v_b_4296_ = v___x_4304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4334_, lean_object* v___x_4335_, lean_object* v___x_4336_, lean_object* v_a_4337_, lean_object* v_b_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4334_, v___x_4335_, v___x_4336_, v_a_4337_, v_b_4338_);
lean_dec_ref(v___x_4335_);
lean_dec_ref(v_str_4334_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4342_){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v_lines_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_string_utf8_byte_size(v_str_4342_);
lean_inc_ref(v_str_4342_);
v___x_4345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4345_, 0, v_str_4342_);
lean_ctor_set(v___x_4345_, 1, v___x_4343_);
lean_ctor_set(v___x_4345_, 2, v___x_4344_);
v_lines_4346_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4345_);
v___x_4347_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4348_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4342_, v___x_4345_, v___x_4344_, v_lines_4346_, v___x_4347_);
lean_dec_ref_known(v___x_4345_, 3);
lean_dec_ref(v_str_4342_);
v___x_4349_ = lean_array_to_list(v___x_4348_);
v___x_4350_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4351_ = l_Lean_MessageData_joinSep(v___x_4349_, v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4352_, lean_object* v___x_4353_, lean_object* v___x_4354_, lean_object* v_inst_4355_, lean_object* v_R_4356_, lean_object* v_a_4357_, lean_object* v_b_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4352_, v___x_4353_, v___x_4354_, v_a_4357_, v_b_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4360_, lean_object* v___x_4361_, lean_object* v___x_4362_, lean_object* v_inst_4363_, lean_object* v_R_4364_, lean_object* v_a_4365_, lean_object* v_b_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4360_, v___x_4361_, v___x_4362_, v_inst_4363_, v_R_4364_, v_a_4365_, v_b_4366_);
lean_dec_ref(v___x_4361_);
lean_dec_ref(v_str_4360_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4368_){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4370_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4370_, 0, lean_box(0));
lean_closure_set(v___x_4370_, 1, lean_box(0));
lean_closure_set(v___x_4370_, 2, lean_box(0));
lean_closure_set(v___x_4370_, 3, v___x_4369_);
lean_closure_set(v___x_4370_, 4, v_inst_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4371_, lean_object* v_inst_4372_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4380_){
_start:
{
lean_object* v___f_4381_; 
v___f_4381_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_instToMessageDataTSyntax(v_k_4382_);
lean_dec(v_k_4382_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4388_, lean_object* v_as_4389_){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_box(0);
v___x_4391_ = l_List_mapTR_loop___redArg(v_inst_4388_, v_as_4389_, v___x_4390_);
v___x_4392_ = l_Lean_MessageData_ofList(v___x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4393_){
_start:
{
lean_object* v___f_4394_; 
v___f_4394_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4394_, 0, v_inst_4393_);
return v___f_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4395_, lean_object* v_inst_4396_){
_start:
{
lean_object* v___f_4397_; 
v___f_4397_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4397_, 0, v_inst_4396_);
return v___f_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4398_, lean_object* v_as_4399_){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4400_ = lean_array_to_list(v_as_4399_);
v___x_4401_ = lean_box(0);
v___x_4402_ = l_List_mapTR_loop___redArg(v_inst_4398_, v___x_4400_, v___x_4401_);
v___x_4403_ = l_Lean_MessageData_ofList(v___x_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4404_){
_start:
{
lean_object* v___f_4405_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4405_, 0, v_inst_4404_);
return v___f_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4406_, lean_object* v_inst_4407_){
_start:
{
lean_object* v___f_4408_; 
v___f_4408_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4408_, 0, v_inst_4407_);
return v___f_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4409_, lean_object* v_acc_4410_, lean_object* v_recur_4411_){
_start:
{
lean_object* v_array_4412_; lean_object* v_start_4413_; lean_object* v_stop_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4427_; 
v_array_4412_ = lean_ctor_get(v_it_4409_, 0);
v_start_4413_ = lean_ctor_get(v_it_4409_, 1);
v_stop_4414_ = lean_ctor_get(v_it_4409_, 2);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_it_4409_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4416_ = v_it_4409_;
v_isShared_4417_ = v_isSharedCheck_4427_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_stop_4414_);
lean_inc(v_start_4413_);
lean_inc(v_array_4412_);
lean_dec(v_it_4409_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4427_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
uint8_t v___x_4418_; 
v___x_4418_ = lean_nat_dec_lt(v_start_4413_, v_stop_4414_);
if (v___x_4418_ == 0)
{
lean_del_object(v___x_4416_);
lean_dec(v_stop_4414_);
lean_dec(v_start_4413_);
lean_dec_ref(v_array_4412_);
lean_dec_ref(v_recur_4411_);
return v_acc_4410_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4419_ = lean_unsigned_to_nat(1u);
v___x_4420_ = lean_nat_add(v_start_4413_, v___x_4419_);
lean_inc_ref(v_array_4412_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 1, v___x_4420_);
v___x_4422_ = v___x_4416_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_array_4412_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_stop_4414_);
v___x_4422_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = lean_array_fget(v_array_4412_, v_start_4413_);
lean_dec(v_start_4413_);
lean_dec_ref(v_array_4412_);
v___x_4424_ = lean_array_push(v_acc_4410_, v___x_4423_);
v___x_4425_ = lean_apply_3(v_recur_4411_, v___x_4422_, v___x_4424_, lean_box(0));
return v___x_4425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4430_, lean_object* v_inst_4431_, lean_object* v_as_4432_){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4433_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4434_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4430_, v_as_4432_, v___x_4433_);
v___x_4435_ = lean_array_to_list(v___x_4434_);
v___x_4436_ = lean_box(0);
v___x_4437_ = l_List_mapTR_loop___redArg(v_inst_4431_, v___x_4435_, v___x_4436_);
v___x_4438_ = l_Lean_MessageData_ofList(v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4440_){
_start:
{
lean_object* v___f_4441_; lean_object* v___f_4442_; 
v___f_4441_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4442_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4442_, 0, v___f_4441_);
lean_closure_set(v___f_4442_, 1, v_inst_4440_);
return v___f_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4443_, lean_object* v_inst_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4444_);
return v___x_4445_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4450_ = l_Lean_MessageData_ofFormat(v___x_4449_);
return v___x_4450_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4454_ = l_Lean_MessageData_ofFormat(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4455_, lean_object* v_x_4456_){
_start:
{
if (lean_obj_tag(v_x_4456_) == 0)
{
lean_object* v___x_4457_; 
lean_dec_ref(v_inst_4455_);
v___x_4457_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4457_;
}
else
{
lean_object* v_val_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_val_4458_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_val_4458_);
lean_dec_ref_known(v_x_4456_, 1);
v___x_4459_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4460_ = lean_apply_1(v_inst_4455_, v_val_4458_);
v___x_4461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4459_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
return v___x_4463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4464_){
_start:
{
lean_object* v___f_4465_; 
v___f_4465_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4465_, 0, v_inst_4464_);
return v___f_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4466_, lean_object* v_inst_4467_){
_start:
{
lean_object* v___f_4468_; 
v___f_4468_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4468_, 0, v_inst_4467_);
return v___f_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4469_, lean_object* v_inst_4470_, lean_object* v_x_4471_){
_start:
{
lean_object* v_fst_4472_; lean_object* v_snd_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4487_; 
v_fst_4472_ = lean_ctor_get(v_x_4471_, 0);
v_snd_4473_ = lean_ctor_get(v_x_4471_, 1);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_x_4471_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4475_ = v_x_4471_;
v_isShared_4476_ = v_isSharedCheck_4487_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_snd_4473_);
lean_inc(v_fst_4472_);
lean_dec(v_x_4471_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4487_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4477_ = lean_apply_1(v_inst_4469_, v_fst_4472_);
v___x_4478_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4476_ == 0)
{
lean_ctor_set_tag(v___x_4475_, 7);
lean_ctor_set(v___x_4475_, 1, v___x_4478_);
lean_ctor_set(v___x_4475_, 0, v___x_4477_);
v___x_4480_ = v___x_4475_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4481_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_apply_1(v_inst_4470_, v_snd_4473_);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = l_Lean_MessageData_paren(v___x_4484_);
return v___x_4485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4488_, lean_object* v_inst_4489_){
_start:
{
lean_object* v___f_4490_; 
v___f_4490_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4490_, 0, v_inst_4488_);
lean_closure_set(v___f_4490_, 1, v_inst_4489_);
return v___f_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4491_, lean_object* v_00_u03b2_4492_, lean_object* v_inst_4493_, lean_object* v_inst_4494_){
_start:
{
lean_object* v___f_4495_; 
v___f_4495_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4495_, 0, v_inst_4493_);
lean_closure_set(v___f_4495_, 1, v_inst_4494_);
return v___f_4495_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4500_ = l_Lean_MessageData_ofFormat(v___x_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4501_){
_start:
{
if (lean_obj_tag(v_x_4501_) == 0)
{
lean_object* v___x_4502_; 
v___x_4502_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4502_;
}
else
{
lean_object* v_val_4503_; lean_object* v___x_4504_; 
v_val_4503_ = lean_ctor_get(v_x_4501_, 0);
lean_inc(v_val_4503_);
lean_dec_ref_known(v_x_4501_, 1);
v___x_4504_ = l_Lean_MessageData_ofExpr(v_val_4503_);
return v___x_4504_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_127_));
v___x_4539_ = l_String_toRawSubstring_x27(v___x_4538_);
return v___x_4539_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4555_ = l_String_toRawSubstring_x27(v___x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v___x_4572_; uint8_t v___x_4573_; 
v___x_4572_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4569_);
v___x_4573_ = l_Lean_Syntax_isOfKind(v_x_4569_, v___x_4572_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_dec(v_x_4569_);
v___x_4574_ = lean_box(1);
v___x_4575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
lean_ctor_set(v___x_4575_, 1, v_a_4571_);
return v___x_4575_;
}
else
{
lean_object* v_quotContext_4576_; lean_object* v_currMacroScope_4577_; lean_object* v_ref_4578_; lean_object* v___x_4579_; lean_object* v_interpStr_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_quotContext_4576_ = lean_ctor_get(v_a_4570_, 1);
v_currMacroScope_4577_ = lean_ctor_get(v_a_4570_, 2);
v_ref_4578_ = lean_ctor_get(v_a_4570_, 5);
v___x_4579_ = lean_unsigned_to_nat(1u);
v_interpStr_4580_ = l_Lean_Syntax_getArg(v_x_4569_, v___x_4579_);
lean_dec(v_x_4569_);
v___x_4581_ = 0;
v___x_4582_ = l_Lean_SourceInfo_fromRef(v_ref_4578_, v___x_4581_);
v___x_4583_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4584_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4577_, 2);
lean_inc_n(v_quotContext_4576_, 2);
v___x_4585_ = l_Lean_addMacroScope(v_quotContext_4576_, v___x_4584_, v_currMacroScope_4577_);
v___x_4586_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4582_);
v___x_4587_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4582_);
lean_ctor_set(v___x_4587_, 1, v___x_4583_);
lean_ctor_set(v___x_4587_, 2, v___x_4585_);
lean_ctor_set(v___x_4587_, 3, v___x_4586_);
v___x_4588_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4589_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4590_ = l_Lean_addMacroScope(v_quotContext_4576_, v___x_4589_, v_currMacroScope_4577_);
v___x_4591_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4592_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4582_);
lean_ctor_set(v___x_4592_, 1, v___x_4588_);
lean_ctor_set(v___x_4592_, 2, v___x_4590_);
lean_ctor_set(v___x_4592_, 3, v___x_4591_);
lean_inc_ref(v___x_4592_);
v___x_4593_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4580_, v___x_4587_, v___x_4592_, v___x_4592_, v_a_4570_, v_a_4571_);
lean_dec(v_interpStr_4580_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
v_a_4595_ = lean_ctor_get(v___x_4593_, 1);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4593_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_inc(v_a_4594_);
lean_dec(v___x_4593_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4594_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_a_4603_ = lean_ctor_get(v___x_4593_, 0);
v_a_4604_ = lean_ctor_get(v___x_4593_, 1);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4593_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_inc(v_a_4603_);
lean_dec(v___x_4593_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4603_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4612_, v_a_4613_, v_a_4614_);
lean_dec_ref(v_a_4613_);
return v_res_4615_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4618_ = l_Lean_stringToMessageData(v___x_4617_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4619_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4620_ = lean_array_to_list(v_msgs_4619_);
v___x_4621_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4622_ = l_Lean_MessageData_joinSep(v___x_4620_, v___x_4621_);
v___x_4623_ = l_Lean_indentD(v___x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4624_, lean_object* v_lctx_4625_, lean_object* v_opts_4626_, lean_object* v_msg_4627_){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4628_ = lean_elab_environment_of_kernel_env(v_env_4624_);
v___x_4629_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
lean_ctor_set(v___x_4630_, 2, v_lctx_4625_);
lean_ctor_set(v___x_4630_, 3, v_opts_4626_);
v___x_4631_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
lean_ctor_set(v___x_4631_, 1, v_msg_4627_);
return v___x_4631_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4634_ = l_Lean_stringToMessageData(v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4640_ = l_Lean_stringToMessageData(v___x_4639_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4641_, lean_object* v_n_4642_, lean_object* v_expectedType_4643_){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4644_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4645_ = l_Lean_MessageData_ofName(v_n_4642_);
v___x_4646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4644_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
v___x_4647_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = l_Lean_indentExpr(v_givenType_4641_);
v___x_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
v___x_4651_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = l_Lean_indentExpr(v_expectedType_4643_);
v___x_4654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4652_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
return v___x_4654_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4655_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4658_ = lean_box(1);
v___x_4659_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4660_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
lean_ctor_set(v___x_4661_, 1, v___x_4659_);
lean_ctor_set(v___x_4661_, 2, v___x_4658_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4664_ = l_Lean_stringToMessageData(v___x_4663_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4667_ = l_Lean_stringToMessageData(v___x_4666_);
return v___x_4667_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4670_ = l_Lean_stringToMessageData(v___x_4669_);
return v___x_4670_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4675_ = l_Lean_MessageData_ofFormat(v___x_4674_);
return v___x_4675_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4678_ = l_Lean_stringToMessageData(v___x_4677_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4681_ = l_Lean_stringToMessageData(v___x_4680_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4684_ = l_Lean_stringToMessageData(v___x_4683_);
return v___x_4684_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4687_ = l_Lean_stringToMessageData(v___x_4686_);
return v___x_4687_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4690_ = l_Lean_stringToMessageData(v___x_4689_);
return v___x_4690_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4693_ = l_Lean_stringToMessageData(v___x_4692_);
return v___x_4693_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4695_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4696_ = l_Lean_stringToMessageData(v___x_4695_);
return v___x_4696_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4699_ = l_Lean_stringToMessageData(v___x_4698_);
return v___x_4699_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4702_ = l_Lean_stringToMessageData(v___x_4701_);
return v___x_4702_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4705_ = l_Lean_stringToMessageData(v___x_4704_);
return v___x_4705_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4708_ = l_Lean_stringToMessageData(v___x_4707_);
return v___x_4708_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4711_ = l_Lean_stringToMessageData(v___x_4710_);
return v___x_4711_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4714_ = l_Lean_stringToMessageData(v___x_4713_);
return v___x_4714_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4717_ = l_Lean_stringToMessageData(v___x_4716_);
return v___x_4717_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4722_ = l_Lean_MessageData_ofFormat(v___x_4721_);
return v___x_4722_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4727_ = l_Lean_MessageData_ofFormat(v___x_4726_);
return v___x_4727_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4732_ = l_Lean_MessageData_ofFormat(v___x_4731_);
return v___x_4732_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4737_ = l_Lean_MessageData_ofFormat(v___x_4736_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4738_, lean_object* v_opts_4739_){
_start:
{
switch(lean_obj_tag(v_e_4738_))
{
case 0:
{
lean_object* v_env_4740_; lean_object* v_name_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4754_; 
v_env_4740_ = lean_ctor_get(v_e_4738_, 0);
v_name_4741_ = lean_ctor_get(v_e_4738_, 1);
v_isSharedCheck_4754_ = !lean_is_exclusive(v_e_4738_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4743_ = v_e_4738_;
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_name_4741_);
lean_inc(v_env_4740_);
lean_dec(v_e_4738_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4745_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4746_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4747_ = l_Lean_MessageData_ofName(v_name_4741_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set_tag(v___x_4743_, 7);
lean_ctor_set(v___x_4743_, 1, v___x_4747_);
lean_ctor_set(v___x_4743_, 0, v___x_4746_);
v___x_4749_ = v___x_4743_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4740_, v___x_4745_, v_opts_4739_, v___x_4751_);
return v___x_4752_;
}
}
}
case 1:
{
lean_object* v_env_4755_; lean_object* v_name_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4770_; 
v_env_4755_ = lean_ctor_get(v_e_4738_, 0);
v_name_4756_ = lean_ctor_get(v_e_4738_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_e_4738_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4758_ = v_e_4738_;
v_isShared_4759_ = v_isSharedCheck_4770_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_name_4756_);
lean_inc(v_env_4755_);
lean_dec(v_e_4738_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4770_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4765_; 
v___x_4760_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4761_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4762_ = 1;
v___x_4763_ = l_Lean_MessageData_ofConstName(v_name_4756_, v___x_4762_);
if (v_isShared_4759_ == 0)
{
lean_ctor_set_tag(v___x_4758_, 7);
lean_ctor_set(v___x_4758_, 1, v___x_4763_);
lean_ctor_set(v___x_4758_, 0, v___x_4761_);
v___x_4765_ = v___x_4758_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4761_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4763_);
v___x_4765_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4755_, v___x_4760_, v_opts_4739_, v___x_4767_);
return v___x_4768_;
}
}
}
case 2:
{
lean_object* v_env_4771_; lean_object* v_decl_4772_; lean_object* v_givenType_4773_; lean_object* v___x_4774_; 
v_env_4771_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4771_);
v_decl_4772_ = lean_ctor_get(v_e_4738_, 1);
lean_inc(v_decl_4772_);
v_givenType_4773_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_givenType_4773_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4774_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4772_))
{
case 1:
{
lean_object* v_val_4775_; lean_object* v_toConstantVal_4776_; lean_object* v_name_4777_; lean_object* v_type_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v_val_4775_ = lean_ctor_get(v_decl_4772_, 0);
lean_inc_ref(v_val_4775_);
lean_dec_ref_known(v_decl_4772_, 1);
v_toConstantVal_4776_ = lean_ctor_get(v_val_4775_, 0);
lean_inc_ref(v_toConstantVal_4776_);
lean_dec_ref(v_val_4775_);
v_name_4777_ = lean_ctor_get(v_toConstantVal_4776_, 0);
lean_inc(v_name_4777_);
v_type_4778_ = lean_ctor_get(v_toConstantVal_4776_, 2);
lean_inc_ref(v_type_4778_);
lean_dec_ref(v_toConstantVal_4776_);
v___x_4779_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4773_, v_name_4777_, v_type_4778_);
v___x_4780_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4771_, v___x_4774_, v_opts_4739_, v___x_4779_);
return v___x_4780_;
}
case 2:
{
lean_object* v_val_4781_; lean_object* v_toConstantVal_4782_; lean_object* v_name_4783_; lean_object* v_type_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v_val_4781_ = lean_ctor_get(v_decl_4772_, 0);
lean_inc_ref(v_val_4781_);
lean_dec_ref_known(v_decl_4772_, 1);
v_toConstantVal_4782_ = lean_ctor_get(v_val_4781_, 0);
lean_inc_ref(v_toConstantVal_4782_);
lean_dec_ref(v_val_4781_);
v_name_4783_ = lean_ctor_get(v_toConstantVal_4782_, 0);
lean_inc(v_name_4783_);
v_type_4784_ = lean_ctor_get(v_toConstantVal_4782_, 2);
lean_inc_ref(v_type_4784_);
lean_dec_ref(v_toConstantVal_4782_);
v___x_4785_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4773_, v_name_4783_, v_type_4784_);
v___x_4786_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4771_, v___x_4774_, v_opts_4739_, v___x_4785_);
return v___x_4786_;
}
default: 
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
lean_dec_ref(v_givenType_4773_);
lean_dec(v_decl_4772_);
v___x_4787_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4788_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4771_, v___x_4774_, v_opts_4739_, v___x_4787_);
return v___x_4788_;
}
}
}
case 3:
{
lean_object* v_env_4789_; lean_object* v_name_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v_env_4789_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4789_);
v_name_4790_ = lean_ctor_get(v_e_4738_, 1);
lean_inc(v_name_4790_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4791_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4792_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4793_ = 1;
v___x_4794_ = l_Lean_MessageData_ofConstName(v_name_4790_, v___x_4793_);
v___x_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4792_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4795_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4789_, v___x_4791_, v_opts_4739_, v___x_4797_);
return v___x_4798_;
}
case 4:
{
lean_object* v_env_4799_; lean_object* v_name_4800_; lean_object* v_expr_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
v_env_4799_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4799_);
v_name_4800_ = lean_ctor_get(v_e_4738_, 1);
lean_inc(v_name_4800_);
v_expr_4801_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_expr_4801_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4802_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4803_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4804_ = 1;
v___x_4805_ = l_Lean_MessageData_ofConstName(v_name_4800_, v___x_4804_);
v___x_4806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4803_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4806_);
lean_ctor_set(v___x_4808_, 1, v___x_4807_);
v___x_4809_ = l_Lean_indentExpr(v_expr_4801_);
v___x_4810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4808_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
v___x_4811_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4799_, v___x_4802_, v_opts_4739_, v___x_4810_);
return v___x_4811_;
}
case 5:
{
lean_object* v_env_4812_; lean_object* v_lctx_4813_; lean_object* v_expr_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v_env_4812_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4812_);
v_lctx_4813_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4813_);
v_expr_4814_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_expr_4814_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4815_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4816_ = l_Lean_indentExpr(v_expr_4814_);
v___x_4817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4815_);
lean_ctor_set(v___x_4817_, 1, v___x_4816_);
v___x_4818_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4812_, v_lctx_4813_, v_opts_4739_, v___x_4817_);
return v___x_4818_;
}
case 6:
{
lean_object* v_env_4819_; lean_object* v_lctx_4820_; lean_object* v_expr_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v_env_4819_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4819_);
v_lctx_4820_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4820_);
v_expr_4821_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_expr_4821_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4822_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4823_ = l_Lean_indentExpr(v_expr_4821_);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4822_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v___x_4825_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4819_, v_lctx_4820_, v_opts_4739_, v___x_4824_);
return v___x_4825_;
}
case 7:
{
lean_object* v_env_4826_; lean_object* v_lctx_4827_; lean_object* v_name_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v_env_4826_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4826_);
v_lctx_4827_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4827_);
v_name_4828_ = lean_ctor_get(v_e_4738_, 2);
lean_inc(v_name_4828_);
lean_dec_ref_known(v_e_4738_, 5);
v___x_4829_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4830_ = l_Lean_MessageData_ofName(v_name_4828_);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4831_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4826_, v_lctx_4827_, v_opts_4739_, v___x_4833_);
return v___x_4834_;
}
case 8:
{
lean_object* v_env_4835_; lean_object* v_lctx_4836_; lean_object* v_expr_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_env_4835_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4835_);
v_lctx_4836_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4836_);
v_expr_4837_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_expr_4837_);
lean_dec_ref_known(v_e_4738_, 4);
v___x_4838_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4839_ = l_Lean_indentExpr(v_expr_4837_);
v___x_4840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4835_, v_lctx_4836_, v_opts_4739_, v___x_4840_);
return v___x_4841_;
}
case 9:
{
lean_object* v_env_4842_; lean_object* v_lctx_4843_; lean_object* v_app_4844_; lean_object* v_funType_4845_; lean_object* v_argType_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v_env_4842_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4842_);
v_lctx_4843_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4843_);
v_app_4844_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_app_4844_);
v_funType_4845_ = lean_ctor_get(v_e_4738_, 3);
lean_inc_ref(v_funType_4845_);
v_argType_4846_ = lean_ctor_get(v_e_4738_, 4);
lean_inc_ref(v_argType_4846_);
lean_dec_ref_known(v_e_4738_, 5);
v___x_4847_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4848_ = l_Lean_indentExpr(v_app_4844_);
v___x_4849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4847_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
v___x_4850_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4849_);
lean_ctor_set(v___x_4851_, 1, v___x_4850_);
v___x_4852_ = l_Lean_indentExpr(v_argType_4846_);
v___x_4853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4851_);
lean_ctor_set(v___x_4853_, 1, v___x_4852_);
v___x_4854_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4853_);
lean_ctor_set(v___x_4855_, 1, v___x_4854_);
v___x_4856_ = l_Lean_indentExpr(v_funType_4845_);
v___x_4857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4855_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4842_, v_lctx_4843_, v_opts_4739_, v___x_4857_);
return v___x_4858_;
}
case 10:
{
lean_object* v_env_4859_; lean_object* v_lctx_4860_; lean_object* v_proj_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v_env_4859_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4859_);
v_lctx_4860_ = lean_ctor_get(v_e_4738_, 1);
lean_inc_ref(v_lctx_4860_);
v_proj_4861_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_proj_4861_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4862_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4863_ = l_Lean_indentExpr(v_proj_4861_);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4859_, v_lctx_4860_, v_opts_4739_, v___x_4864_);
return v___x_4865_;
}
case 11:
{
lean_object* v_env_4866_; lean_object* v_name_4867_; lean_object* v_type_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v_env_4866_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_env_4866_);
v_name_4867_ = lean_ctor_get(v_e_4738_, 1);
lean_inc(v_name_4867_);
v_type_4868_ = lean_ctor_get(v_e_4738_, 2);
lean_inc_ref(v_type_4868_);
lean_dec_ref_known(v_e_4738_, 3);
v___x_4869_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4870_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4871_ = 1;
v___x_4872_ = l_Lean_MessageData_ofConstName(v_name_4867_, v___x_4871_);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4870_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4873_);
lean_ctor_set(v___x_4875_, 1, v___x_4874_);
v___x_4876_ = l_Lean_indentExpr(v_type_4868_);
v___x_4877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4866_, v___x_4869_, v_opts_4739_, v___x_4877_);
return v___x_4878_;
}
case 12:
{
lean_object* v_msg_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v_opts_4739_);
v_msg_4879_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_msg_4879_);
lean_dec_ref_known(v_e_4738_, 1);
v___x_4880_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4881_ = l_Lean_stringToMessageData(v_msg_4879_);
v___x_4882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4880_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
return v___x_4882_;
}
case 13:
{
lean_object* v___x_4883_; 
lean_dec_ref(v_opts_4739_);
v___x_4883_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4883_;
}
case 14:
{
lean_object* v___x_4884_; 
lean_dec_ref(v_opts_4739_);
v___x_4884_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4884_;
}
case 15:
{
lean_object* v___x_4885_; 
lean_dec_ref(v_opts_4739_);
v___x_4885_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4885_;
}
default: 
{
lean_object* v___x_4886_; 
lean_dec_ref(v_opts_4739_);
v___x_4886_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4887_, lean_object* v_e_4888_, lean_object* v_cls_4889_){
_start:
{
lean_object* v___x_4890_; double v___x_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4890_ = lean_box(0);
v___x_4891_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4892_ = 1;
v___x_4893_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4894_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4894_, 0, v_cls_4889_);
lean_ctor_set(v___x_4894_, 1, v___x_4890_);
lean_ctor_set(v___x_4894_, 2, v___x_4893_);
lean_ctor_set_float(v___x_4894_, sizeof(void*)*3, v___x_4891_);
lean_ctor_set_float(v___x_4894_, sizeof(void*)*3 + 8, v___x_4891_);
lean_ctor_set_uint8(v___x_4894_, sizeof(void*)*3 + 16, v___x_4892_);
v___x_4895_ = lean_apply_1(v_inst_4887_, v_e_4888_);
v___x_4896_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4897_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4894_);
lean_ctor_set(v___x_4897_, 1, v___x_4895_);
lean_ctor_set(v___x_4897_, 2, v___x_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4898_, lean_object* v_inst_4899_, lean_object* v_e_4900_, lean_object* v_cls_4901_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Lean_toTraceElem___redArg(v_inst_4899_, v_e_4900_, v_cls_4901_);
return v___x_4902_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Length(builtin);
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
