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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
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
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "(kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit"};
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
lean_inc_ref(v___y_39_);
v___x_43_ = lean_string_append(v___y_39_, v___y_42_);
if (lean_obj_tag(v___y_41_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___x_43_;
v___y_33_ = v___y_40_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_41_, 1);
v___y_32_ = v___x_43_;
v___y_33_ = v___y_40_;
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
v___y_39_ = v___x_49_;
v___y_40_ = v___y_47_;
v___y_41_ = v___y_48_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___x_49_;
v___y_40_ = v___y_47_;
v___y_41_ = v___y_48_;
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* v_k_97_){
_start:
{
lean_inc(v_k_97_);
return v_k_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* v_k_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MessageSeverity_ctorElim___redArg(v_k_98_);
lean_dec(v_k_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_100_, lean_object* v_ctorIdx_101_, uint8_t v_t_102_, lean_object* v_h_103_, lean_object* v_k_104_){
_start:
{
lean_inc(v_k_104_);
return v_k_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_105_, lean_object* v_ctorIdx_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = l_Lean_MessageSeverity_ctorElim(v_motive_105_, v_ctorIdx_106_, v_t_boxed_110_, v_h_108_, v_k_109_);
lean_dec(v_k_109_);
lean_dec(v_ctorIdx_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_112_){
_start:
{
lean_inc(v_information_112_);
return v_information_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_113_);
lean_dec(v_information_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_115_, uint8_t v_t_116_, lean_object* v_h_117_, lean_object* v_information_118_){
_start:
{
lean_inc(v_information_118_);
return v_information_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_information_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l_Lean_MessageSeverity_information_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_information_122_);
lean_dec(v_information_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_125_){
_start:
{
lean_inc(v_warning_125_);
return v_warning_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_126_);
lean_dec(v_warning_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_warning_131_){
_start:
{
lean_inc(v_warning_131_);
return v_warning_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_warning_135_){
_start:
{
uint8_t v_t_boxed_136_; lean_object* v_res_137_; 
v_t_boxed_136_ = lean_unbox(v_t_133_);
v_res_137_ = l_Lean_MessageSeverity_warning_elim(v_motive_132_, v_t_boxed_136_, v_h_134_, v_warning_135_);
lean_dec(v_warning_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* v_error_138_){
_start:
{
lean_inc(v_error_138_);
return v_error_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* v_error_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_MessageSeverity_error_elim___redArg(v_error_139_);
lean_dec(v_error_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_141_, uint8_t v_t_142_, lean_object* v_h_143_, lean_object* v_error_144_){
_start:
{
lean_inc(v_error_144_);
return v_error_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_error_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = l_Lean_MessageSeverity_error_elim(v_motive_145_, v_t_boxed_149_, v_h_147_, v_error_148_);
lean_dec(v_error_148_);
return v_res_150_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_153_, uint8_t v_y_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_MessageSeverity_ctorIdx(v_x_153_);
v___x_156_ = l_Lean_MessageSeverity_ctorIdx(v_y_154_);
v___x_157_ = lean_nat_dec_eq(v___x_155_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v___x_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_158_, lean_object* v_y_159_){
_start:
{
uint8_t v_x_17__boxed_160_; uint8_t v_y_18__boxed_161_; uint8_t v_res_162_; lean_object* v_r_163_; 
v_x_17__boxed_160_ = lean_unbox(v_x_158_);
v_y_18__boxed_161_ = lean_unbox(v_y_159_);
v_res_162_ = l_Lean_instBEqMessageSeverity_beq(v_x_17__boxed_160_, v_y_18__boxed_161_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_175_){
_start:
{
switch(v_x_175_)
{
case 0:
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_176_;
}
case 1:
{
lean_object* v___x_177_; 
v___x_177_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_177_;
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_x_67__boxed_180_; lean_object* v_res_181_; 
v_x_67__boxed_180_ = lean_unbox(v_x_179_);
v_res_181_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Json_getTag_x3f(v_json_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_200_, 1);
v___x_203_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_204_ = lean_string_dec_eq(v_val_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_206_ = lean_string_dec_eq(v_val_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_208_ = lean_string_dec_eq(v_val_202_, v___x_207_);
lean_dec(v_val_202_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_val_202_);
v___x_211_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_211_;
}
}
else
{
lean_object* v___x_212_; 
lean_dec(v_val_202_);
v___x_212_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_215_){
_start:
{
switch(v_x_215_)
{
case 0:
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_216_;
}
case 1:
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_217_;
}
default: 
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_219_){
_start:
{
uint8_t v_x_28__boxed_220_; lean_object* v_res_221_; 
v_x_28__boxed_220_ = lean_unbox(v_x_219_);
v_res_221_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx(uint8_t v_x_224_){
_start:
{
switch(v_x_224_)
{
case 0:
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(0u);
return v___x_225_;
}
case 1:
{
lean_object* v___x_226_; 
v___x_226_ = lean_unsigned_to_nat(1u);
return v___x_226_;
}
default: 
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(2u);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___boxed(lean_object* v_x_228_){
_start:
{
uint8_t v_x_boxed_229_; lean_object* v_res_230_; 
v_x_boxed_229_ = lean_unbox(v_x_228_);
v_res_230_ = l_Lean_TraceResult_ctorIdx(v_x_boxed_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg(lean_object* v_k_231_){
_start:
{
lean_inc(v_k_231_);
return v_k_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg___boxed(lean_object* v_k_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_TraceResult_ctorElim___redArg(v_k_232_);
lean_dec(v_k_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim(lean_object* v_motive_234_, lean_object* v_ctorIdx_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_k_238_){
_start:
{
lean_inc(v_k_238_);
return v_k_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___boxed(lean_object* v_motive_239_, lean_object* v_ctorIdx_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_k_243_){
_start:
{
uint8_t v_t_boxed_244_; lean_object* v_res_245_; 
v_t_boxed_244_ = lean_unbox(v_t_241_);
v_res_245_ = l_Lean_TraceResult_ctorElim(v_motive_239_, v_ctorIdx_240_, v_t_boxed_244_, v_h_242_, v_k_243_);
lean_dec(v_k_243_);
lean_dec(v_ctorIdx_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg(lean_object* v_success_246_){
_start:
{
lean_inc(v_success_246_);
return v_success_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg___boxed(lean_object* v_success_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_TraceResult_success_elim___redArg(v_success_247_);
lean_dec(v_success_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim(lean_object* v_motive_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_success_252_){
_start:
{
lean_inc(v_success_252_);
return v_success_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_success_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lean_TraceResult_success_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_success_256_);
lean_dec(v_success_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg(lean_object* v_failure_259_){
_start:
{
lean_inc(v_failure_259_);
return v_failure_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg___boxed(lean_object* v_failure_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_TraceResult_failure_elim___redArg(v_failure_260_);
lean_dec(v_failure_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_failure_265_){
_start:
{
lean_inc(v_failure_265_);
return v_failure_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_failure_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_TraceResult_failure_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_failure_269_);
lean_dec(v_failure_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg(lean_object* v_error_272_){
_start:
{
lean_inc(v_error_272_);
return v_error_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg___boxed(lean_object* v_error_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_TraceResult_error_elim___redArg(v_error_273_);
lean_dec(v_error_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_error_278_){
_start:
{
lean_inc(v_error_278_);
return v_error_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_error_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_TraceResult_error_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_error_282_);
lean_dec(v_error_282_);
return v_res_284_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult_default(void){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult(void){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTraceResult_beq(uint8_t v_x_287_, uint8_t v_y_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Lean_TraceResult_ctorIdx(v_x_287_);
v___x_290_ = l_Lean_TraceResult_ctorIdx(v_y_288_);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
lean_dec(v___x_290_);
lean_dec(v___x_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_292_, lean_object* v_y_293_){
_start:
{
uint8_t v_x_17__boxed_294_; uint8_t v_y_18__boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v_x_17__boxed_294_ = lean_unbox(v_x_292_);
v_y_18__boxed_295_ = lean_unbox(v_y_293_);
v_res_296_ = l_Lean_instBEqTraceResult_beq(v_x_17__boxed_294_, v_y_18__boxed_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_nat_to_int(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_313_, lean_object* v_prec_314_){
_start:
{
lean_object* v___y_316_; lean_object* v___y_323_; lean_object* v___y_330_; 
switch(v_x_313_)
{
case 0:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(1024u);
v___x_337_ = lean_nat_dec_le(v___x_336_, v_prec_314_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_316_ = v___x_338_;
goto v___jp_315_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_316_ = v___x_339_;
goto v___jp_315_;
}
}
case 1:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v_prec_314_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_323_ = v___x_342_;
goto v___jp_322_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_323_ = v___x_343_;
goto v___jp_322_;
}
}
default: 
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_314_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_330_ = v___x_346_;
goto v___jp_329_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_330_ = v___x_347_;
goto v___jp_329_;
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_316_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___y_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = 0;
v___x_320_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_319_);
v___x_321_ = l_Repr_addAppParen(v___x_320_, v_prec_314_);
return v___x_321_;
}
v___jp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_323_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_326_);
v___x_328_ = l_Repr_addAppParen(v___x_327_, v_prec_314_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_314_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_348_, lean_object* v_prec_349_){
_start:
{
uint8_t v_x_177__boxed_350_; lean_object* v_res_351_; 
v_x_177__boxed_350_ = lean_unbox(v_x_348_);
v_res_351_ = l_Lean_instReprTraceResult_repr(v_x_177__boxed_350_, v_prec_349_);
lean_dec(v_prec_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_357_){
_start:
{
switch(v_x_357_)
{
case 0:
{
lean_object* v___x_358_; 
v___x_358_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_358_;
}
case 1:
{
lean_object* v___x_359_; 
v___x_359_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_359_;
}
default: 
{
lean_object* v___x_360_; 
v___x_360_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_361_){
_start:
{
uint8_t v_x_31__boxed_362_; lean_object* v_res_363_; 
v_x_31__boxed_362_ = lean_unbox(v_x_361_);
v_res_363_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_362_);
return v_res_363_;
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
case 10:
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(10u);
return v___x_375_;
}
default: 
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(11u);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_MessageData_ctorIdx(v_x_377_);
lean_dec_ref(v_x_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_379_, lean_object* v_k_380_){
_start:
{
switch(lean_obj_tag(v_t_379_))
{
case 0:
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v_t_379_, 0);
lean_inc_ref(v_a_381_);
lean_dec_ref_known(v_t_379_, 1);
v___x_382_ = lean_apply_1(v_k_380_, v_a_381_);
return v___x_382_;
}
case 1:
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v_t_379_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v_t_379_, 1);
v___x_384_ = lean_apply_1(v_k_380_, v_a_383_);
return v___x_384_;
}
case 5:
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v_t_379_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v_t_379_, 1);
lean_inc_ref(v_a_386_);
lean_dec_ref_known(v_t_379_, 2);
v___x_387_ = lean_apply_2(v_k_380_, v_a_385_, v_a_386_);
return v___x_387_;
}
case 6:
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v_t_379_, 0);
lean_inc_ref(v_a_388_);
lean_dec_ref_known(v_t_379_, 1);
v___x_389_ = lean_apply_1(v_k_380_, v_a_388_);
return v___x_389_;
}
case 8:
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_390_ = lean_ctor_get(v_t_379_, 0);
lean_inc(v_a_390_);
v_a_391_ = lean_ctor_get(v_t_379_, 1);
lean_inc_ref(v_a_391_);
lean_dec_ref_known(v_t_379_, 2);
v___x_392_ = lean_apply_2(v_k_380_, v_a_390_, v_a_391_);
return v___x_392_;
}
case 9:
{
lean_object* v_data_393_; lean_object* v_msg_394_; lean_object* v_children_395_; lean_object* v___x_396_; 
v_data_393_ = lean_ctor_get(v_t_379_, 0);
lean_inc_ref(v_data_393_);
v_msg_394_ = lean_ctor_get(v_t_379_, 1);
lean_inc_ref(v_msg_394_);
v_children_395_ = lean_ctor_get(v_t_379_, 2);
lean_inc_ref(v_children_395_);
lean_dec_ref_known(v_t_379_, 3);
v___x_396_ = lean_apply_3(v_k_380_, v_data_393_, v_msg_394_, v_children_395_);
return v___x_396_;
}
case 11:
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_397_ = lean_ctor_get(v_t_379_, 0);
lean_inc(v_a_397_);
v_a_398_ = lean_ctor_get(v_t_379_, 1);
lean_inc_ref(v_a_398_);
lean_dec_ref_known(v_t_379_, 2);
v___x_399_ = lean_apply_2(v_k_380_, v_a_397_, v_a_398_);
return v___x_399_;
}
default: 
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v_t_379_, 0);
lean_inc_ref(v_a_400_);
v_a_401_ = lean_ctor_get(v_t_379_, 1);
lean_inc_ref(v_a_401_);
lean_dec_ref(v_t_379_);
v___x_402_ = lean_apply_2(v_k_380_, v_a_400_, v_a_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_403_, lean_object* v_ctorIdx_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_k_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_MessageData_ctorElim___redArg(v_t_405_, v_k_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_409_, lean_object* v_ctorIdx_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_k_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_MessageData_ctorElim(v_motive__1_409_, v_ctorIdx_410_, v_t_411_, v_h_412_, v_k_413_);
lean_dec(v_ctorIdx_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_415_, lean_object* v_ofFormatWithInfos_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_MessageData_ctorElim___redArg(v_t_415_, v_ofFormatWithInfos_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_ofFormatWithInfos_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_MessageData_ctorElim___redArg(v_t_419_, v_ofFormatWithInfos_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_423_, lean_object* v_ofGoal_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_MessageData_ctorElim___redArg(v_t_423_, v_ofGoal_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_ofGoal_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_MessageData_ctorElim___redArg(v_t_427_, v_ofGoal_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_431_, lean_object* v_ofWidget_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_MessageData_ctorElim___redArg(v_t_431_, v_ofWidget_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_ofWidget_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_MessageData_ctorElim___redArg(v_t_435_, v_ofWidget_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_439_, lean_object* v_withContext_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_MessageData_ctorElim___redArg(v_t_439_, v_withContext_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_withContext_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_MessageData_ctorElim___redArg(v_t_443_, v_withContext_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_447_, lean_object* v_withNamingContext_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_MessageData_ctorElim___redArg(v_t_447_, v_withNamingContext_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_withNamingContext_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_MessageData_ctorElim___redArg(v_t_451_, v_withNamingContext_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_455_, lean_object* v_nest_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_MessageData_ctorElim___redArg(v_t_455_, v_nest_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_nest_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_MessageData_ctorElim___redArg(v_t_459_, v_nest_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_463_, lean_object* v_group_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_MessageData_ctorElim___redArg(v_t_463_, v_group_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_466_, lean_object* v_t_467_, lean_object* v_h_468_, lean_object* v_group_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_MessageData_ctorElim___redArg(v_t_467_, v_group_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_471_, lean_object* v_compose_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_MessageData_ctorElim___redArg(v_t_471_, v_compose_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_474_, lean_object* v_t_475_, lean_object* v_h_476_, lean_object* v_compose_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_MessageData_ctorElim___redArg(v_t_475_, v_compose_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_479_, lean_object* v_tagged_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_MessageData_ctorElim___redArg(v_t_479_, v_tagged_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_482_, lean_object* v_t_483_, lean_object* v_h_484_, lean_object* v_tagged_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_MessageData_ctorElim___redArg(v_t_483_, v_tagged_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_487_, lean_object* v_trace_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_MessageData_ctorElim___redArg(v_t_487_, v_trace_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_490_, lean_object* v_t_491_, lean_object* v_h_492_, lean_object* v_trace_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_MessageData_ctorElim___redArg(v_t_491_, v_trace_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_495_, lean_object* v_ofLazy_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_MessageData_ctorElim___redArg(v_t_495_, v_ofLazy_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_498_, lean_object* v_t_499_, lean_object* v_h_500_, lean_object* v_ofLazy_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_MessageData_ctorElim___redArg(v_t_499_, v_ofLazy_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_503_, lean_object* v_ofOriginatingSyntax_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_MessageData_ctorElim___redArg(v_t_503_, v_ofOriginatingSyntax_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_506_, lean_object* v_t_507_, lean_object* v_h_508_, lean_object* v_ofOriginatingSyntax_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_MessageData_ctorElim___redArg(v_t_507_, v_ofOriginatingSyntax_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_box(1);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_fmt_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_526_, lean_object* v_onMissingContext_527_, lean_object* v_f_528_, lean_object* v_ctx_x3f_529_){
_start:
{
lean_object* v_msg_532_; 
if (lean_obj_tag(v_ctx_x3f_529_) == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v_f_528_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_apply_2(v_onMissingContext_527_, v___x_534_, lean_box(0));
v_msg_532_ = v___x_535_;
goto v___jp_531_;
}
else
{
lean_object* v_val_536_; lean_object* v___x_537_; 
lean_dec_ref(v_onMissingContext_527_);
v_val_536_ = lean_ctor_get(v_ctx_x3f_529_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_ctx_x3f_529_, 1);
v___x_537_ = lean_apply_2(v_f_528_, v_val_536_, lean_box(0));
v_msg_532_ = v___x_537_;
goto v___jp_531_;
}
v___jp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_526_);
lean_ctor_set(v___x_533_, 1, v_msg_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_538_, lean_object* v_onMissingContext_539_, lean_object* v_f_540_, lean_object* v_ctx_x3f_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_MessageData_lazy___lam__0(v___x_538_, v_onMissingContext_539_, v_f_540_, v_ctx_x3f_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_544_, lean_object* v_hasSyntheticSorry_545_, lean_object* v_onMissingContext_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_548_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_548_, 0, v___x_547_);
lean_closure_set(v___f_548_, 1, v_onMissingContext_546_);
lean_closure_set(v___f_548_, 2, v_f_544_);
v___x_549_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_549_, 0, v___f_548_);
lean_ctor_set(v___x_549_, 1, v_hasSyntheticSorry_545_);
return v___x_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_550_, lean_object* v_x_551_){
_start:
{
switch(lean_obj_tag(v_x_551_))
{
case 3:
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_552_);
lean_dec_ref_known(v_x_551_, 2);
v_x_551_ = v_a_552_;
goto _start;
}
case 4:
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_554_);
lean_dec_ref_known(v_x_551_, 2);
v_x_551_ = v_a_554_;
goto _start;
}
case 5:
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_556_);
lean_dec_ref_known(v_x_551_, 2);
v_x_551_ = v_a_556_;
goto _start;
}
case 6:
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v_x_551_, 0);
lean_inc_ref(v_a_558_);
lean_dec_ref_known(v_x_551_, 1);
v_x_551_ = v_a_558_;
goto _start;
}
case 7:
{
lean_object* v_a_560_; lean_object* v_a_561_; uint8_t v___x_562_; 
v_a_560_ = lean_ctor_get(v_x_551_, 0);
lean_inc_ref(v_a_560_);
v_a_561_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_561_);
lean_dec_ref_known(v_x_551_, 2);
lean_inc_ref(v_p_550_);
v___x_562_ = l_Lean_MessageData_hasTag(v_p_550_, v_a_560_);
if (v___x_562_ == 0)
{
v_x_551_ = v_a_561_;
goto _start;
}
else
{
lean_dec_ref(v_a_561_);
lean_dec_ref(v_p_550_);
return v___x_562_;
}
}
case 8:
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_a_564_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_a_564_);
v_a_565_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v_x_551_, 2);
lean_inc_ref(v_p_550_);
v___x_566_ = lean_apply_1(v_p_550_, v_a_564_);
v___x_567_ = lean_unbox(v___x_566_);
if (v___x_567_ == 0)
{
v_x_551_ = v_a_565_;
goto _start;
}
else
{
uint8_t v___x_569_; 
lean_dec_ref(v_a_565_);
lean_dec_ref(v_p_550_);
v___x_569_ = lean_unbox(v___x_566_);
return v___x_569_;
}
}
case 9:
{
lean_object* v_data_570_; lean_object* v_msg_571_; lean_object* v_children_572_; lean_object* v_cls_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_data_570_ = lean_ctor_get(v_x_551_, 0);
lean_inc_ref(v_data_570_);
v_msg_571_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_msg_571_);
v_children_572_ = lean_ctor_get(v_x_551_, 2);
lean_inc_ref(v_children_572_);
lean_dec_ref_known(v_x_551_, 3);
v_cls_573_ = lean_ctor_get(v_data_570_, 0);
lean_inc(v_cls_573_);
lean_dec_ref(v_data_570_);
lean_inc_ref(v_p_550_);
v___x_574_ = lean_apply_1(v_p_550_, v_cls_573_);
v___x_575_ = lean_unbox(v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; 
lean_inc_ref(v_p_550_);
v___x_576_ = l_Lean_MessageData_hasTag(v_p_550_, v_msg_571_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_array_get_size(v_children_572_);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_dec_ref(v_children_572_);
lean_dec_ref(v_p_550_);
return v___x_576_;
}
else
{
if (v___x_579_ == 0)
{
lean_dec_ref(v_children_572_);
lean_dec_ref(v_p_550_);
return v___x_576_;
}
else
{
size_t v___x_580_; size_t v___x_581_; uint8_t v___x_582_; 
v___x_580_ = ((size_t)0ULL);
v___x_581_ = lean_usize_of_nat(v___x_578_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_550_, v_children_572_, v___x_580_, v___x_581_);
lean_dec_ref(v_children_572_);
return v___x_582_;
}
}
}
else
{
lean_dec_ref(v_children_572_);
lean_dec_ref(v_p_550_);
return v___x_576_;
}
}
else
{
uint8_t v___x_583_; 
lean_dec_ref(v_children_572_);
lean_dec_ref(v_msg_571_);
lean_dec_ref(v_p_550_);
v___x_583_ = lean_unbox(v___x_574_);
return v___x_583_;
}
}
case 11:
{
lean_object* v_a_584_; 
v_a_584_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_a_584_);
lean_dec_ref_known(v_x_551_, 2);
v_x_551_ = v_a_584_;
goto _start;
}
default: 
{
uint8_t v___x_586_; 
lean_dec_ref(v_x_551_);
lean_dec_ref(v_p_550_);
v___x_586_ = 0;
return v___x_586_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_587_, lean_object* v_as_588_, size_t v_i_589_, size_t v_stop_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_589_, v_stop_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_uget_borrowed(v_as_588_, v_i_589_);
lean_inc(v___x_592_);
lean_inc_ref(v_p_587_);
v___x_593_ = l_Lean_MessageData_hasTag(v_p_587_, v___x_592_);
if (v___x_593_ == 0)
{
size_t v___x_594_; size_t v___x_595_; 
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_589_, v___x_594_);
v_i_589_ = v___x_595_;
goto _start;
}
else
{
lean_dec_ref(v_p_587_);
return v___x_593_;
}
}
else
{
uint8_t v___x_597_; 
lean_dec_ref(v_p_587_);
v___x_597_ = 0;
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_stop_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_601_);
lean_dec(v_stop_601_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_598_, v_as_599_, v_i_boxed_602_, v_stop_boxed_603_);
lean_dec_ref(v_as_599_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_606_, lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_MessageData_hasTag(v_p_606_, v_x_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_610_){
_start:
{
switch(lean_obj_tag(v_x_610_))
{
case 3:
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v_x_610_, 1);
v_x_610_ = v_a_611_;
goto _start;
}
case 4:
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v_x_610_, 1);
v_x_610_ = v_a_613_;
goto _start;
}
case 8:
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_a_615_);
return v_a_615_;
}
case 9:
{
lean_object* v_data_616_; lean_object* v_cls_617_; 
v_data_616_ = lean_ctor_get(v_x_610_, 0);
v_cls_617_ = lean_ctor_get(v_data_616_, 0);
lean_inc(v_cls_617_);
return v_cls_617_;
}
case 11:
{
lean_object* v_a_618_; 
v_a_618_ = lean_ctor_get(v_x_610_, 1);
v_x_610_ = v_a_618_;
goto _start;
}
default: 
{
lean_object* v___x_620_; 
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_MessageData_kind(v_x_621_);
lean_dec_ref(v_x_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 11)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_a_624_ = lean_ctor_get(v_x_623_, 0);
v_a_625_ = lean_ctor_get(v_x_623_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v_x_623_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v_x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_a_624_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 0);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_625_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_x_623_);
return v___x_635_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_636_){
_start:
{
switch(lean_obj_tag(v_x_636_))
{
case 3:
{
lean_object* v_a_637_; 
v_a_637_ = lean_ctor_get(v_x_636_, 1);
v_x_636_ = v_a_637_;
goto _start;
}
case 4:
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v_x_636_, 1);
v_x_636_ = v_a_639_;
goto _start;
}
case 8:
{
lean_object* v_a_641_; 
v_a_641_ = lean_ctor_get(v_x_636_, 1);
v_x_636_ = v_a_641_;
goto _start;
}
case 9:
{
uint8_t v___x_643_; 
v___x_643_ = 1;
return v___x_643_;
}
case 11:
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v_x_636_, 1);
v_x_636_ = v_a_644_;
goto _start;
}
default: 
{
uint8_t v___x_646_; 
v___x_646_ = 0;
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean_MessageData_isTrace(v_x_647_);
lean_dec_ref(v_x_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
switch(lean_obj_tag(v_x_650_))
{
case 3:
{
lean_object* v_a_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_a_652_ = lean_ctor_get(v_x_650_, 0);
v_a_653_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v_x_650_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_inc(v_a_652_);
lean_dec(v_x_650_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = l_Lean_MessageData_composePreservingKind(v_a_653_, v_x_651_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_652_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
case 4:
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_a_662_ = lean_ctor_get(v_x_650_, 0);
v_a_663_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v_x_650_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_inc(v_a_662_);
lean_dec(v_x_650_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_MessageData_composePreservingKind(v_a_663_, v_x_651_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
case 8:
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_a_672_ = lean_ctor_get(v_x_650_, 0);
v_a_673_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v_x_650_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_inc(v_a_672_);
lean_dec(v_x_650_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 7);
lean_ctor_set(v___x_675_, 1, v_x_651_);
lean_ctor_set(v___x_675_, 0, v_a_673_);
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_x_651_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_679_, 0, v_a_672_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
}
}
case 11:
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
v_a_682_ = lean_ctor_get(v_x_650_, 0);
v_a_683_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_691_ == 0)
{
v___x_685_ = v_x_650_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_inc(v_a_682_);
lean_dec(v_x_650_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_MessageData_composePreservingKind(v_a_683_, v_x_651_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_682_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
default: 
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v_x_650_);
lean_ctor_set(v___x_692_, 1, v_x_651_);
return v___x_692_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_MessageData_ofFormat(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_696_, lean_object* v_ctx_697_){
_start:
{
lean_object* v_env_698_; lean_object* v_mctx_699_; lean_object* v_lctx_700_; lean_object* v_opts_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v___x_704_; 
v_env_698_ = lean_ctor_get(v_ctx_697_, 0);
v_mctx_699_ = lean_ctor_get(v_ctx_697_, 1);
v_lctx_700_ = lean_ctor_get(v_ctx_697_, 2);
v_opts_701_ = lean_ctor_get(v_ctx_697_, 3);
v_currNamespace_702_ = lean_ctor_get(v_nCtx_696_, 0);
v_openDecls_703_ = lean_ctor_get(v_nCtx_696_, 1);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
lean_inc_ref(v_opts_701_);
lean_inc_ref(v_lctx_700_);
lean_inc_ref(v_mctx_699_);
lean_inc_ref(v_env_698_);
v___x_704_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_704_, 0, v_env_698_);
lean_ctor_set(v___x_704_, 1, v_mctx_699_);
lean_ctor_set(v___x_704_, 2, v_lctx_700_);
lean_ctor_set(v___x_704_, 3, v_opts_701_);
lean_ctor_set(v___x_704_, 4, v_currNamespace_702_);
lean_ctor_set(v___x_704_, 5, v_openDecls_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_705_, lean_object* v_ctx_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_MessageData_mkPPContext(v_nCtx_705_, v_ctx_706_);
lean_dec_ref(v_ctx_706_);
lean_dec_ref(v_nCtx_705_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_710_);
lean_dec_ref(v_x_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_713_, lean_object* v_stx_714_, lean_object* v_ctx_x3f_715_){
_start:
{
lean_object* v_val_718_; 
if (lean_obj_tag(v_ctx_x3f_715_) == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = 0;
v___x_723_ = l_Lean_Syntax_formatStx(v_stx_714_, v___x_721_, v___x_722_);
v_val_718_ = v___x_723_;
goto v___jp_717_;
}
else
{
lean_object* v_val_724_; lean_object* v___x_725_; 
v_val_724_ = lean_ctor_get(v_ctx_x3f_715_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v_ctx_x3f_715_, 1);
v___x_725_ = l_Lean_ppTerm(v_val_724_, v_stx_714_);
v_val_718_ = v___x_725_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Lean_MessageData_ofFormat(v_val_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_713_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_726_, lean_object* v_stx_727_, lean_object* v_ctx_x3f_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_726_, v_stx_727_, v_ctx_x3f_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_732_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_stx_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v___f_733_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_734_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_735_ = lean_box(0);
v_stx_736_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_732_, v___x_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_737_, 0, v___x_734_);
lean_closure_set(v___f_737_, 1, v_stx_736_);
v___x_738_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_738_, 0, v___f_737_);
lean_ctor_set(v___x_738_, 1, v___f_733_);
return v___x_738_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_739_, lean_object* v_mctx_740_){
_start:
{
lean_object* v___x_741_; lean_object* v_fst_742_; uint8_t v___x_743_; 
v___x_741_ = l_Lean_instantiateMVarsCore(v_mctx_740_, v_e_739_);
v_fst_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_fst_742_);
lean_dec_ref(v___x_741_);
v___x_743_ = l_Lean_Expr_hasSyntheticSorry(v_fst_742_);
lean_dec(v_fst_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_744_, lean_object* v_mctx_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Lean_MessageData_ofExpr___lam__0(v_e_744_, v_mctx_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_748_, lean_object* v_e_749_, lean_object* v_ctx_x3f_750_){
_start:
{
lean_object* v_val_753_; 
if (lean_obj_tag(v_ctx_x3f_750_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_756_ = lean_expr_dbg_to_string(v_e_749_);
lean_dec_ref(v_e_749_);
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_box(1);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v_val_753_ = v___x_759_;
goto v___jp_752_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_761_; 
v_val_760_ = lean_ctor_get(v_ctx_x3f_750_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_ctx_x3f_750_, 1);
v___x_761_ = l_Lean_ppExprWithInfos(v_val_760_, v_e_749_);
v_val_753_ = v___x_761_;
goto v___jp_752_;
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_val_753_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_748_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_762_, lean_object* v_e_763_, lean_object* v_ctx_x3f_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_MessageData_ofExpr___lam__1(v___x_762_, v_e_763_, v_ctx_x3f_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_767_){
_start:
{
lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
lean_inc_ref(v_e_767_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_768_, 0, v_e_767_);
v___x_769_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_770_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_770_, 0, v___x_769_);
lean_closure_set(v___f_770_, 1, v_e_767_);
v___x_771_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_771_, 0, v___f_770_);
lean_ctor_set(v___x_771_, 1, v___f_768_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_box(0);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_MessageData_ofLevel___lam__0(v_x_774_);
lean_dec(v_x_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_776_, lean_object* v_l_777_, lean_object* v___f_778_, lean_object* v_ctx_x3f_779_){
_start:
{
lean_object* v_val_782_; 
if (lean_obj_tag(v_ctx_x3f_779_) == 0)
{
uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = 1;
v___x_786_ = l_Lean_Level_format(v_l_777_, v___x_785_, v___f_778_);
v_val_782_ = v___x_786_;
goto v___jp_781_;
}
else
{
lean_object* v_val_787_; lean_object* v___x_788_; 
lean_dec_ref(v___f_778_);
v_val_787_ = lean_ctor_get(v_ctx_x3f_779_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_ctx_x3f_779_, 1);
v___x_788_ = l_Lean_ppLevel(v_val_787_, v_l_777_);
v_val_782_ = v___x_788_;
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l_Lean_MessageData_ofFormat(v_val_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_776_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_789_, lean_object* v_l_790_, lean_object* v___f_791_, lean_object* v_ctx_x3f_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_MessageData_ofLevel___lam__2(v___x_789_, v_l_790_, v___f_791_, v_ctx_x3f_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___x_801_; 
v___f_797_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_798_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_799_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_800_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_800_, 0, v___x_799_);
lean_closure_set(v___f_800_, 1, v_l_796_);
lean_closure_set(v___f_800_, 2, v___f_797_);
v___x_801_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_801_, 0, v___f_800_);
lean_ctor_set(v___x_801_, 1, v___f_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_802_){
_start:
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = 1;
v___x_804_ = l_Lean_Name_toString(v_n_802_, v___x_803_);
v___x_805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = l_Lean_MessageData_ofFormat(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_810_, lean_object* v_k_811_, uint8_t v_v_812_){
_start:
{
lean_object* v_map_813_; uint8_t v_hasTrace_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_map_813_ = lean_ctor_get(v_o_810_, 0);
v_hasTrace_814_ = lean_ctor_get_uint8(v_o_810_, sizeof(void*)*1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_o_810_);
if (v_isSharedCheck_828_ == 0)
{
v___x_816_ = v_o_810_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_map_813_);
lean_dec(v_o_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_818_, 0, v_v_812_);
lean_inc(v_k_811_);
v___x_819_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_811_, v___x_818_, v_map_813_);
if (v_hasTrace_814_ == 0)
{
lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_823_; 
v___x_820_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_821_ = l_Lean_Name_isPrefixOf(v___x_820_, v_k_811_);
lean_dec(v_k_811_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_819_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_819_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_821_);
return v___x_823_;
}
}
else
{
lean_object* v___x_826_; 
lean_dec(v_k_811_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_819_);
v___x_826_ = v___x_816_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_827_, sizeof(void*)*1, v_hasTrace_814_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_829_, lean_object* v_k_830_, lean_object* v_v_831_){
_start:
{
uint8_t v_v_boxed_832_; lean_object* v_res_833_; 
v_v_boxed_832_ = lean_unbox(v_v_831_);
v_res_833_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_829_, v_k_830_, v_v_boxed_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_839_, lean_object* v_constName_840_, uint8_t v_fullNames_841_, lean_object* v_ctx_x3f_842_){
_start:
{
lean_object* v_val_845_; lean_object* v___y_849_; 
if (lean_obj_tag(v_ctx_x3f_842_) == 0)
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_850_ = 1;
v___x_851_ = l_Lean_Name_toString(v_constName_840_, v___x_850_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_box(1);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v_val_845_ = v___x_854_;
goto v___jp_844_;
}
else
{
if (v_fullNames_841_ == 0)
{
lean_object* v_val_855_; lean_object* v___x_856_; 
v_val_855_ = lean_ctor_get(v_ctx_x3f_842_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_ctx_x3f_842_, 1);
v___x_856_ = l_Lean_ppConstNameWithInfos(v_val_855_, v_constName_840_);
v___y_849_ = v___x_856_;
goto v___jp_848_;
}
else
{
lean_object* v_val_857_; lean_object* v_env_858_; lean_object* v_mctx_859_; lean_object* v_lctx_860_; lean_object* v_opts_861_; lean_object* v_currNamespace_862_; lean_object* v_openDecls_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_val_857_ = lean_ctor_get(v_ctx_x3f_842_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v_ctx_x3f_842_, 1);
v_env_858_ = lean_ctor_get(v_val_857_, 0);
v_mctx_859_ = lean_ctor_get(v_val_857_, 1);
v_lctx_860_ = lean_ctor_get(v_val_857_, 2);
v_opts_861_ = lean_ctor_get(v_val_857_, 3);
v_currNamespace_862_ = lean_ctor_get(v_val_857_, 4);
v_openDecls_863_ = lean_ctor_get(v_val_857_, 5);
v_isSharedCheck_873_ = !lean_is_exclusive(v_val_857_);
if (v_isSharedCheck_873_ == 0)
{
v___x_865_ = v_val_857_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_openDecls_863_);
lean_inc(v_currNamespace_862_);
lean_inc(v_opts_861_);
lean_inc(v_lctx_860_);
lean_inc(v_mctx_859_);
lean_inc(v_env_858_);
lean_dec(v_val_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_868_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_861_, v___x_867_, v_fullNames_841_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 3, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_env_858_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_mctx_859_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_lctx_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_currNamespace_862_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v_openDecls_863_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_ppConstNameWithInfos(v___x_870_, v_constName_840_);
v___y_849_ = v___x_871_;
goto v___jp_848_;
}
}
}
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_val_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_839_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
return v___x_847_;
}
v___jp_848_:
{
v_val_845_ = v___y_849_;
goto v___jp_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_874_, lean_object* v_constName_875_, lean_object* v_fullNames_876_, lean_object* v_ctx_x3f_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_fullNames_boxed_879_; lean_object* v_res_880_; 
v_fullNames_boxed_879_ = lean_unbox(v_fullNames_876_);
v_res_880_ = l_Lean_MessageData_ofConstName___lam__1(v___x_874_, v_constName_875_, v_fullNames_boxed_879_, v_ctx_x3f_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_881_, uint8_t v_fullNames_882_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___x_887_; 
v___f_883_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_884_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_885_ = lean_box(v_fullNames_882_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_886_, 0, v___x_884_);
lean_closure_set(v___f_886_, 1, v_constName_881_);
lean_closure_set(v___f_886_, 2, v___x_885_);
v___x_887_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_887_, 0, v___f_886_);
lean_ctor_set(v___x_887_, 1, v___f_883_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_888_, lean_object* v_fullNames_889_){
_start:
{
uint8_t v_fullNames_boxed_890_; lean_object* v_res_891_; 
v_fullNames_boxed_890_ = lean_unbox(v_fullNames_889_);
v_res_891_ = l_Lean_MessageData_ofConstName(v_constName_888_, v_fullNames_boxed_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_val_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_MessageData_withExprHover___lam__0(v_val_896_, v___y_897_);
lean_dec_ref(v___y_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_900_, lean_object* v_v_901_, lean_object* v_t_902_){
_start:
{
if (lean_obj_tag(v_t_902_) == 0)
{
lean_object* v_size_903_; lean_object* v_k_904_; lean_object* v_v_905_; lean_object* v_l_906_; lean_object* v_r_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1188_; 
v_size_903_ = lean_ctor_get(v_t_902_, 0);
v_k_904_ = lean_ctor_get(v_t_902_, 1);
v_v_905_ = lean_ctor_get(v_t_902_, 2);
v_l_906_ = lean_ctor_get(v_t_902_, 3);
v_r_907_ = lean_ctor_get(v_t_902_, 4);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_t_902_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_909_ = v_t_902_;
v_isShared_910_ = v_isSharedCheck_1188_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_r_907_);
lean_inc(v_l_906_);
lean_inc(v_v_905_);
lean_inc(v_k_904_);
lean_inc(v_size_903_);
lean_dec(v_t_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1188_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_lt(v_k_900_, v_k_904_);
if (v___x_911_ == 0)
{
uint8_t v___x_912_; 
v___x_912_ = lean_nat_dec_eq(v_k_900_, v_k_904_);
if (v___x_912_ == 0)
{
lean_object* v_impl_913_; lean_object* v___x_914_; 
lean_dec(v_size_903_);
v_impl_913_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_900_, v_v_901_, v_r_907_);
v___x_914_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_906_) == 0)
{
lean_object* v_size_915_; lean_object* v_size_916_; lean_object* v_k_917_; lean_object* v_v_918_; lean_object* v_l_919_; lean_object* v_r_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_size_915_ = lean_ctor_get(v_l_906_, 0);
v_size_916_ = lean_ctor_get(v_impl_913_, 0);
lean_inc(v_size_916_);
v_k_917_ = lean_ctor_get(v_impl_913_, 1);
lean_inc(v_k_917_);
v_v_918_ = lean_ctor_get(v_impl_913_, 2);
lean_inc(v_v_918_);
v_l_919_ = lean_ctor_get(v_impl_913_, 3);
lean_inc(v_l_919_);
v_r_920_ = lean_ctor_get(v_impl_913_, 4);
lean_inc(v_r_920_);
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = lean_nat_mul(v___x_921_, v_size_915_);
v___x_923_ = lean_nat_dec_lt(v___x_922_, v_size_916_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec(v_r_920_);
lean_dec(v_l_919_);
lean_dec(v_v_918_);
lean_dec(v_k_917_);
v___x_924_ = lean_nat_add(v___x_914_, v_size_915_);
v___x_925_ = lean_nat_add(v___x_924_, v_size_916_);
lean_dec(v_size_916_);
lean_dec(v___x_924_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_impl_913_);
lean_ctor_set(v___x_909_, 0, v___x_925_);
v___x_927_ = v___x_909_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_l_906_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_impl_913_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_992_; 
v_isSharedCheck_992_ = !lean_is_exclusive(v_impl_913_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; 
v_unused_993_ = lean_ctor_get(v_impl_913_, 4);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_impl_913_, 3);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_impl_913_, 2);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_impl_913_, 1);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_impl_913_, 0);
lean_dec(v_unused_997_);
v___x_930_ = v_impl_913_;
v_isShared_931_ = v_isSharedCheck_992_;
goto v_resetjp_929_;
}
else
{
lean_dec(v_impl_913_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_992_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_size_932_; lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v_l_935_; lean_object* v_r_936_; lean_object* v_size_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_size_932_ = lean_ctor_get(v_l_919_, 0);
v_k_933_ = lean_ctor_get(v_l_919_, 1);
v_v_934_ = lean_ctor_get(v_l_919_, 2);
v_l_935_ = lean_ctor_get(v_l_919_, 3);
v_r_936_ = lean_ctor_get(v_l_919_, 4);
v_size_937_ = lean_ctor_get(v_r_920_, 0);
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = lean_nat_mul(v___x_938_, v_size_937_);
v___x_940_ = lean_nat_dec_lt(v_size_932_, v___x_939_);
lean_dec(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_968_; 
lean_inc(v_r_936_);
lean_inc(v_l_935_);
lean_inc(v_v_934_);
lean_inc(v_k_933_);
v_isSharedCheck_968_ = !lean_is_exclusive(v_l_919_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_969_ = lean_ctor_get(v_l_919_, 4);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_l_919_, 3);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_l_919_, 2);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_l_919_, 1);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_919_, 0);
lean_dec(v_unused_973_);
v___x_942_ = v_l_919_;
v_isShared_943_ = v_isSharedCheck_968_;
goto v_resetjp_941_;
}
else
{
lean_dec(v_l_919_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_968_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_958_; 
v___x_944_ = lean_nat_add(v___x_914_, v_size_915_);
v___x_945_ = lean_nat_add(v___x_944_, v_size_916_);
lean_dec(v_size_916_);
if (lean_obj_tag(v_l_935_) == 0)
{
lean_object* v_size_966_; 
v_size_966_ = lean_ctor_get(v_l_935_, 0);
lean_inc(v_size_966_);
v___y_958_ = v_size_966_;
goto v___jp_957_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___y_958_ = v___x_967_;
goto v___jp_957_;
}
v___jp_946_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_nat_add(v___y_947_, v___y_949_);
lean_dec(v___y_949_);
lean_dec(v___y_947_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_r_920_);
lean_ctor_set(v___x_942_, 3, v_r_936_);
lean_ctor_set(v___x_942_, 2, v_v_918_);
lean_ctor_set(v___x_942_, 1, v_k_917_);
lean_ctor_set(v___x_942_, 0, v___x_950_);
v___x_952_ = v___x_942_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_k_917_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_v_918_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_r_936_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_r_920_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_952_);
lean_ctor_set(v___x_930_, 3, v___y_948_);
lean_ctor_set(v___x_930_, 2, v_v_934_);
lean_ctor_set(v___x_930_, 1, v_k_933_);
lean_ctor_set(v___x_930_, 0, v___x_945_);
v___x_954_ = v___x_930_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_933_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_934_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v___y_948_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_nat_add(v___x_944_, v___y_958_);
lean_dec(v___y_958_);
lean_dec(v___x_944_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_l_935_);
lean_ctor_set(v___x_909_, 0, v___x_959_);
v___x_961_ = v___x_909_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_l_906_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_l_935_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_nat_add(v___x_914_, v_size_937_);
if (lean_obj_tag(v_r_936_) == 0)
{
lean_object* v_size_963_; 
v_size_963_ = lean_ctor_get(v_r_936_, 0);
lean_inc(v_size_963_);
v___y_947_ = v___x_962_;
v___y_948_ = v___x_961_;
v___y_949_ = v_size_963_;
goto v___jp_946_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_unsigned_to_nat(0u);
v___y_947_ = v___x_962_;
v___y_948_ = v___x_961_;
v___y_949_ = v___x_964_;
goto v___jp_946_;
}
}
}
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_del_object(v___x_909_);
v___x_974_ = lean_nat_add(v___x_914_, v_size_915_);
v___x_975_ = lean_nat_add(v___x_974_, v_size_916_);
lean_dec(v_size_916_);
v___x_976_ = lean_nat_add(v___x_974_, v_size_932_);
lean_dec(v___x_974_);
lean_inc_ref(v_l_906_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v_l_919_);
lean_ctor_set(v___x_930_, 3, v_l_906_);
lean_ctor_set(v___x_930_, 2, v_v_905_);
lean_ctor_set(v___x_930_, 1, v_k_904_);
lean_ctor_set(v___x_930_, 0, v___x_976_);
v___x_978_ = v___x_930_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_l_906_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_l_919_);
v___x_978_ = v_reuseFailAlloc_991_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_isSharedCheck_985_ = !lean_is_exclusive(v_l_906_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_l_906_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_906_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_906_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_906_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_906_, 0);
lean_dec(v_unused_990_);
v___x_980_ = v_l_906_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_dec(v_l_906_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 4, v_r_920_);
lean_ctor_set(v___x_980_, 3, v___x_978_);
lean_ctor_set(v___x_980_, 2, v_v_918_);
lean_ctor_set(v___x_980_, 1, v_k_917_);
lean_ctor_set(v___x_980_, 0, v___x_975_);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_917_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_918_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_r_920_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_998_; 
v_l_998_ = lean_ctor_get(v_impl_913_, 3);
lean_inc(v_l_998_);
if (lean_obj_tag(v_l_998_) == 0)
{
lean_object* v_r_999_; lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1024_; 
v_r_999_ = lean_ctor_get(v_impl_913_, 4);
v_k_1000_ = lean_ctor_get(v_impl_913_, 1);
v_v_1001_ = lean_ctor_get(v_impl_913_, 2);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_impl_913_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1025_ = lean_ctor_get(v_impl_913_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_913_, 0);
lean_dec(v_unused_1026_);
v___x_1003_ = v_impl_913_;
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_r_999_);
lean_inc(v_v_1001_);
lean_inc(v_k_1000_);
lean_dec(v_impl_913_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_k_1005_; lean_object* v_v_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1020_; 
v_k_1005_ = lean_ctor_get(v_l_998_, 1);
v_v_1006_ = lean_ctor_get(v_l_998_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_l_998_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1021_ = lean_ctor_get(v_l_998_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_l_998_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_l_998_, 0);
lean_dec(v_unused_1023_);
v___x_1008_ = v_l_998_;
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_v_1006_);
lean_inc(v_k_1005_);
lean_dec(v_l_998_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_999_, 2);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_r_999_);
lean_ctor_set(v___x_1008_, 3, v_r_999_);
lean_ctor_set(v___x_1008_, 2, v_v_905_);
lean_ctor_set(v___x_1008_, 1, v_k_904_);
lean_ctor_set(v___x_1008_, 0, v___x_914_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_r_999_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_r_999_);
v___x_1012_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
lean_inc(v_r_999_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 3, v_r_999_);
lean_ctor_set(v___x_1003_, 0, v___x_914_);
v___x_1014_ = v___x_1003_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_1000_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_1001_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_r_999_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_r_999_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v___x_1014_);
lean_ctor_set(v___x_909_, 3, v___x_1012_);
lean_ctor_set(v___x_909_, 2, v_v_1006_);
lean_ctor_set(v___x_909_, 1, v_k_1005_);
lean_ctor_set(v___x_909_, 0, v___x_1010_);
v___x_1016_ = v___x_909_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
else
{
lean_object* v_r_1027_; 
v_r_1027_ = lean_ctor_get(v_impl_913_, 4);
lean_inc(v_r_1027_);
if (lean_obj_tag(v_r_1027_) == 0)
{
lean_object* v_k_1028_; lean_object* v_v_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1040_; 
v_k_1028_ = lean_ctor_get(v_impl_913_, 1);
v_v_1029_ = lean_ctor_get(v_impl_913_, 2);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_impl_913_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1041_ = lean_ctor_get(v_impl_913_, 4);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_impl_913_, 3);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_impl_913_, 0);
lean_dec(v_unused_1043_);
v___x_1031_ = v_impl_913_;
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_v_1029_);
lean_inc(v_k_1028_);
lean_dec(v_impl_913_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_unsigned_to_nat(3u);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v_l_998_);
lean_ctor_set(v___x_1031_, 2, v_v_905_);
lean_ctor_set(v___x_1031_, 1, v_k_904_);
lean_ctor_set(v___x_1031_, 0, v___x_914_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_l_998_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_l_998_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_r_1027_);
lean_ctor_set(v___x_909_, 3, v___x_1035_);
lean_ctor_set(v___x_909_, 2, v_v_1029_);
lean_ctor_set(v___x_909_, 1, v_k_1028_);
lean_ctor_set(v___x_909_, 0, v___x_1033_);
v___x_1037_ = v___x_909_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_r_1027_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_unsigned_to_nat(2u);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_impl_913_);
lean_ctor_set(v___x_909_, 3, v_r_1027_);
lean_ctor_set(v___x_909_, 0, v___x_1044_);
v___x_1046_ = v___x_909_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_r_1027_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_impl_913_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v___x_1049_; 
lean_dec(v_v_905_);
lean_dec(v_k_904_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 2, v_v_901_);
lean_ctor_set(v___x_909_, 1, v_k_900_);
v___x_1049_ = v___x_909_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_size_903_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_l_906_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_r_907_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
lean_object* v_impl_1051_; lean_object* v___x_1052_; 
lean_dec(v_size_903_);
v_impl_1051_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_900_, v_v_901_, v_l_906_);
v___x_1052_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_907_) == 0)
{
lean_object* v_size_1053_; lean_object* v_size_1054_; lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v_r_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_size_1053_ = lean_ctor_get(v_r_907_, 0);
v_size_1054_ = lean_ctor_get(v_impl_1051_, 0);
lean_inc(v_size_1054_);
v_k_1055_ = lean_ctor_get(v_impl_1051_, 1);
lean_inc(v_k_1055_);
v_v_1056_ = lean_ctor_get(v_impl_1051_, 2);
lean_inc(v_v_1056_);
v_l_1057_ = lean_ctor_get(v_impl_1051_, 3);
lean_inc(v_l_1057_);
v_r_1058_ = lean_ctor_get(v_impl_1051_, 4);
lean_inc(v_r_1058_);
v___x_1059_ = lean_unsigned_to_nat(3u);
v___x_1060_ = lean_nat_mul(v___x_1059_, v_size_1053_);
v___x_1061_ = lean_nat_dec_lt(v___x_1060_, v_size_1054_);
lean_dec(v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_dec(v_r_1058_);
lean_dec(v_l_1057_);
lean_dec(v_v_1056_);
lean_dec(v_k_1055_);
v___x_1062_ = lean_nat_add(v___x_1052_, v_size_1054_);
lean_dec(v_size_1054_);
v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1053_);
lean_dec(v___x_1062_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 3, v_impl_1051_);
lean_ctor_set(v___x_909_, 0, v___x_1063_);
v___x_1065_ = v___x_909_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_impl_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_r_907_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
else
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1132_; 
v_isSharedCheck_1132_ = !lean_is_exclusive(v_impl_1051_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1133_ = lean_ctor_get(v_impl_1051_, 4);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_impl_1051_, 3);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_impl_1051_, 2);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1051_, 1);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1051_, 0);
lean_dec(v_unused_1137_);
v___x_1068_ = v_impl_1051_;
v_isShared_1069_ = v_isSharedCheck_1132_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_impl_1051_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1132_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_size_1070_; lean_object* v_size_1071_; lean_object* v_k_1072_; lean_object* v_v_1073_; lean_object* v_l_1074_; lean_object* v_r_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_size_1070_ = lean_ctor_get(v_l_1057_, 0);
v_size_1071_ = lean_ctor_get(v_r_1058_, 0);
v_k_1072_ = lean_ctor_get(v_r_1058_, 1);
v_v_1073_ = lean_ctor_get(v_r_1058_, 2);
v_l_1074_ = lean_ctor_get(v_r_1058_, 3);
v_r_1075_ = lean_ctor_get(v_r_1058_, 4);
v___x_1076_ = lean_unsigned_to_nat(2u);
v___x_1077_ = lean_nat_mul(v___x_1076_, v_size_1070_);
v___x_1078_ = lean_nat_dec_lt(v_size_1071_, v___x_1077_);
lean_dec(v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1107_; 
lean_inc(v_r_1075_);
lean_inc(v_l_1074_);
lean_inc(v_v_1073_);
lean_inc(v_k_1072_);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_r_1058_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; 
v_unused_1108_ = lean_ctor_get(v_r_1058_, 4);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_r_1058_, 3);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_r_1058_, 2);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_r_1058_, 1);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_r_1058_, 0);
lean_dec(v_unused_1112_);
v___x_1080_ = v_r_1058_;
v_isShared_1081_ = v_isSharedCheck_1107_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_r_1058_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1107_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___x_1095_; lean_object* v___y_1097_; 
v___x_1082_ = lean_nat_add(v___x_1052_, v_size_1054_);
lean_dec(v_size_1054_);
v___x_1083_ = lean_nat_add(v___x_1082_, v_size_1053_);
lean_dec(v___x_1082_);
v___x_1095_ = lean_nat_add(v___x_1052_, v_size_1070_);
if (lean_obj_tag(v_l_1074_) == 0)
{
lean_object* v_size_1105_; 
v_size_1105_ = lean_ctor_get(v_l_1074_, 0);
lean_inc(v_size_1105_);
v___y_1097_ = v_size_1105_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___y_1097_ = v___x_1106_;
goto v___jp_1096_;
}
v___jp_1084_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_nat_add(v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 4, v_r_907_);
lean_ctor_set(v___x_1080_, 3, v_r_1075_);
lean_ctor_set(v___x_1080_, 2, v_v_905_);
lean_ctor_set(v___x_1080_, 1, v_k_904_);
lean_ctor_set(v___x_1080_, 0, v___x_1088_);
v___x_1090_ = v___x_1080_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_r_1075_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_r_907_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1092_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v___x_1090_);
lean_ctor_set(v___x_1068_, 3, v___y_1085_);
lean_ctor_set(v___x_1068_, 2, v_v_1073_);
lean_ctor_set(v___x_1068_, 1, v_k_1072_);
lean_ctor_set(v___x_1068_, 0, v___x_1083_);
v___x_1092_ = v___x_1068_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_k_1072_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_v_1073_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v___y_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_nat_add(v___x_1095_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec(v___x_1095_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_l_1074_);
lean_ctor_set(v___x_909_, 3, v_l_1057_);
lean_ctor_set(v___x_909_, 2, v_v_1056_);
lean_ctor_set(v___x_909_, 1, v_k_1055_);
lean_ctor_set(v___x_909_, 0, v___x_1098_);
v___x_1100_ = v___x_909_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_v_1056_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_l_1057_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_l_1074_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_nat_add(v___x_1052_, v_size_1053_);
if (lean_obj_tag(v_r_1075_) == 0)
{
lean_object* v_size_1102_; 
v_size_1102_ = lean_ctor_get(v_r_1075_, 0);
lean_inc(v_size_1102_);
v___y_1085_ = v___x_1100_;
v___y_1086_ = v___x_1101_;
v___y_1087_ = v_size_1102_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_unsigned_to_nat(0u);
v___y_1085_ = v___x_1100_;
v___y_1086_ = v___x_1101_;
v___y_1087_ = v___x_1103_;
goto v___jp_1084_;
}
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_del_object(v___x_909_);
v___x_1113_ = lean_nat_add(v___x_1052_, v_size_1054_);
lean_dec(v_size_1054_);
v___x_1114_ = lean_nat_add(v___x_1113_, v_size_1053_);
lean_dec(v___x_1113_);
v___x_1115_ = lean_nat_add(v___x_1052_, v_size_1053_);
v___x_1116_ = lean_nat_add(v___x_1115_, v_size_1071_);
lean_dec(v___x_1115_);
lean_inc_ref(v_r_907_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v_r_907_);
lean_ctor_set(v___x_1068_, 3, v_r_1058_);
lean_ctor_set(v___x_1068_, 2, v_v_905_);
lean_ctor_set(v___x_1068_, 1, v_k_904_);
lean_ctor_set(v___x_1068_, 0, v___x_1116_);
v___x_1118_ = v___x_1068_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_r_1058_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_r_907_);
v___x_1118_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_isSharedCheck_1125_ = !lean_is_exclusive(v_r_907_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; 
v_unused_1126_ = lean_ctor_get(v_r_907_, 4);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_r_907_, 3);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_r_907_, 2);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_r_907_, 1);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_r_907_, 0);
lean_dec(v_unused_1130_);
v___x_1120_ = v_r_907_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_r_907_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1118_);
lean_ctor_set(v___x_1120_, 3, v_l_1057_);
lean_ctor_set(v___x_1120_, 2, v_v_1056_);
lean_ctor_set(v___x_1120_, 1, v_k_1055_);
lean_ctor_set(v___x_1120_, 0, v___x_1114_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_1056_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_l_1057_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v___x_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1138_; 
v_l_1138_ = lean_ctor_get(v_impl_1051_, 3);
lean_inc(v_l_1138_);
if (lean_obj_tag(v_l_1138_) == 0)
{
lean_object* v_r_1139_; lean_object* v_k_1140_; lean_object* v_v_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1152_; 
v_r_1139_ = lean_ctor_get(v_impl_1051_, 4);
v_k_1140_ = lean_ctor_get(v_impl_1051_, 1);
v_v_1141_ = lean_ctor_get(v_impl_1051_, 2);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_impl_1051_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; 
v_unused_1153_ = lean_ctor_get(v_impl_1051_, 3);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_impl_1051_, 0);
lean_dec(v_unused_1154_);
v___x_1143_ = v_impl_1051_;
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_r_1139_);
lean_inc(v_v_1141_);
lean_inc(v_k_1140_);
lean_dec(v_impl_1051_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1139_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 3, v_r_1139_);
lean_ctor_set(v___x_1143_, 2, v_v_905_);
lean_ctor_set(v___x_1143_, 1, v_k_904_);
lean_ctor_set(v___x_1143_, 0, v___x_1052_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_r_1139_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1139_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v___x_1147_);
lean_ctor_set(v___x_909_, 3, v_l_1138_);
lean_ctor_set(v___x_909_, 2, v_v_1141_);
lean_ctor_set(v___x_909_, 1, v_k_1140_);
lean_ctor_set(v___x_909_, 0, v___x_1145_);
v___x_1149_ = v___x_909_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_r_1155_; 
v_r_1155_ = lean_ctor_get(v_impl_1051_, 4);
lean_inc(v_r_1155_);
if (lean_obj_tag(v_r_1155_) == 0)
{
lean_object* v_k_1156_; lean_object* v_v_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1180_; 
v_k_1156_ = lean_ctor_get(v_impl_1051_, 1);
v_v_1157_ = lean_ctor_get(v_impl_1051_, 2);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_impl_1051_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1181_ = lean_ctor_get(v_impl_1051_, 4);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1051_, 3);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_impl_1051_, 0);
lean_dec(v_unused_1183_);
v___x_1159_ = v_impl_1051_;
v_isShared_1160_ = v_isSharedCheck_1180_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_v_1157_);
lean_inc(v_k_1156_);
lean_dec(v_impl_1051_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1180_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_k_1161_; lean_object* v_v_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1176_; 
v_k_1161_ = lean_ctor_get(v_r_1155_, 1);
v_v_1162_ = lean_ctor_get(v_r_1155_, 2);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_r_1155_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; 
v_unused_1177_ = lean_ctor_get(v_r_1155_, 4);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1155_, 3);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_r_1155_, 0);
lean_dec(v_unused_1179_);
v___x_1164_ = v_r_1155_;
v_isShared_1165_ = v_isSharedCheck_1176_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_v_1162_);
lean_inc(v_k_1161_);
lean_dec(v_r_1155_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1176_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_unsigned_to_nat(3u);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 4, v_l_1138_);
lean_ctor_set(v___x_1164_, 3, v_l_1138_);
lean_ctor_set(v___x_1164_, 2, v_v_1157_);
lean_ctor_set(v___x_1164_, 1, v_k_1156_);
lean_ctor_set(v___x_1164_, 0, v___x_1052_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_k_1156_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_v_1157_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_l_1138_);
v___x_1168_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_l_1138_);
lean_ctor_set(v___x_1159_, 2, v_v_905_);
lean_ctor_set(v___x_1159_, 1, v_k_904_);
lean_ctor_set(v___x_1159_, 0, v___x_1052_);
v___x_1170_ = v___x_1159_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_l_1138_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_l_1138_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v___x_1170_);
lean_ctor_set(v___x_909_, 3, v___x_1168_);
lean_ctor_set(v___x_909_, 2, v_v_1162_);
lean_ctor_set(v___x_909_, 1, v_k_1161_);
lean_ctor_set(v___x_909_, 0, v___x_1166_);
v___x_1172_ = v___x_909_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_k_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_v_1162_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(2u);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 4, v_r_1155_);
lean_ctor_set(v___x_909_, 3, v_impl_1051_);
lean_ctor_set(v___x_909_, 0, v___x_1184_);
v___x_1186_ = v___x_909_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_k_904_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_v_905_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_impl_1051_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_r_1155_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_k_900_);
lean_ctor_set(v___x_1190_, 2, v_v_901_);
lean_ctor_set(v___x_1190_, 3, v_t_902_);
lean_ctor_set(v___x_1190_, 4, v_t_902_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1191_, lean_object* v_b_1192_){
_start:
{
if (lean_obj_tag(v_as_x27_1191_) == 0)
{
return v_b_1192_;
}
else
{
lean_object* v_head_1193_; lean_object* v_tail_1194_; lean_object* v_fst_1195_; lean_object* v_snd_1196_; lean_object* v_r_1197_; 
v_head_1193_ = lean_ctor_get(v_as_x27_1191_, 0);
v_tail_1194_ = lean_ctor_get(v_as_x27_1191_, 1);
v_fst_1195_ = lean_ctor_get(v_head_1193_, 0);
v_snd_1196_ = lean_ctor_get(v_head_1193_, 1);
lean_inc(v_snd_1196_);
lean_inc(v_fst_1195_);
v_r_1197_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1195_, v_snd_1196_, v_b_1192_);
v_as_x27_1191_ = v_tail_1194_;
v_b_1192_ = v_r_1197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1199_, v_b_1200_);
lean_dec(v_as_x27_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1210_, lean_object* v_expr_1211_, lean_object* v_lctx_1212_, lean_object* v_location_x3f_1213_, lean_object* v_docString_x3f_1214_, lean_object* v_mkDocString_x3f_1215_, uint8_t v_explicit_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___y_1224_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_fmt_1210_);
v___x_1219_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1220_ = lean_box(0);
v___x_1221_ = 0;
v___x_1222_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v_lctx_1212_);
lean_ctor_set(v___x_1222_, 2, v___x_1220_);
lean_ctor_set(v___x_1222_, 3, v_expr_1211_);
lean_ctor_set_uint8(v___x_1222_, sizeof(void*)*4, v___x_1221_);
lean_ctor_set_uint8(v___x_1222_, sizeof(void*)*4 + 1, v___x_1221_);
if (lean_obj_tag(v_mkDocString_x3f_1215_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1214_) == 0)
{
v___y_1224_ = v_mkDocString_x3f_1215_;
goto v___jp_1223_;
}
else
{
lean_object* v_val_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
v_val_1234_ = lean_ctor_get(v_docString_x3f_1214_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_docString_x3f_1214_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1236_ = v_docString_x3f_1214_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_val_1234_);
lean_dec(v_docString_x3f_1214_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___f_1238_; lean_object* v___x_1240_; 
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1238_, 0, v_val_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___f_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___f_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
v___y_1224_ = v___x_1240_;
goto v___jp_1223_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1214_);
v___y_1224_ = v_mkDocString_x3f_1215_;
goto v___jp_1223_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_r_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1225_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1222_);
lean_ctor_set(v___x_1225_, 1, v_location_x3f_1213_);
lean_ctor_set(v___x_1225_, 2, v___y_1224_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*3, v_explicit_1216_);
v___x_1226_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1217_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v_r_1230_ = lean_box(1);
v___x_1231_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1229_, v_r_1230_);
lean_dec_ref_known(v___x_1229_, 2);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1218_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1243_, lean_object* v_expr_1244_, lean_object* v_lctx_1245_, lean_object* v_location_x3f_1246_, lean_object* v_docString_x3f_1247_, lean_object* v_mkDocString_x3f_1248_, lean_object* v_explicit_1249_){
_start:
{
uint8_t v_explicit_boxed_1250_; lean_object* v_res_1251_; 
v_explicit_boxed_1250_ = lean_unbox(v_explicit_1249_);
v_res_1251_ = l_Lean_MessageData_withExprHover(v_fmt_1243_, v_expr_1244_, v_lctx_1245_, v_location_x3f_1246_, v_docString_x3f_1247_, v_mkDocString_x3f_1248_, v_explicit_boxed_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_k_1253_, lean_object* v_v_1254_, lean_object* v_t_1255_, lean_object* v_hl_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1253_, v_v_1254_, v_t_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1258_, lean_object* v_as_x27_1259_, lean_object* v_b_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1259_, v_b_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1263_, lean_object* v_as_x27_1264_, lean_object* v_b_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1263_, v_as_x27_1264_, v_b_1265_, v_a_1266_);
lean_dec(v_as_x27_1264_);
lean_dec(v_as_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1268_, lean_object* v_expr_1269_, lean_object* v_location_x3f_1270_, lean_object* v_docString_x3f_1271_, lean_object* v_mkDocString_x3f_1272_, uint8_t v_explicit_1273_, lean_object* v_toPure_1274_, lean_object* v_lctx_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Lean_MessageData_withExprHover(v_fmt_1268_, v_expr_1269_, v_lctx_1275_, v_location_x3f_1270_, v_docString_x3f_1271_, v_mkDocString_x3f_1272_, v_explicit_1273_);
v___x_1277_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1278_, lean_object* v_expr_1279_, lean_object* v_location_x3f_1280_, lean_object* v_docString_x3f_1281_, lean_object* v_mkDocString_x3f_1282_, lean_object* v_explicit_1283_, lean_object* v_toPure_1284_, lean_object* v_lctx_1285_){
_start:
{
uint8_t v_explicit_boxed_1286_; lean_object* v_res_1287_; 
v_explicit_boxed_1286_ = lean_unbox(v_explicit_1283_);
v_res_1287_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1278_, v_expr_1279_, v_location_x3f_1280_, v_docString_x3f_1281_, v_mkDocString_x3f_1282_, v_explicit_boxed_1286_, v_toPure_1284_, v_lctx_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_fmt_1290_, lean_object* v_expr_1291_, lean_object* v_lctx_x3f_1292_, lean_object* v_location_x3f_1293_, lean_object* v_docString_x3f_1294_, lean_object* v_mkDocString_x3f_1295_, uint8_t v_explicit_1296_){
_start:
{
lean_object* v_toApplicative_1297_; lean_object* v_toBind_1298_; lean_object* v_toPure_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; 
v_toApplicative_1297_ = lean_ctor_get(v_inst_1288_, 0);
lean_inc_ref(v_toApplicative_1297_);
v_toBind_1298_ = lean_ctor_get(v_inst_1288_, 1);
lean_inc(v_toBind_1298_);
lean_dec_ref(v_inst_1288_);
v_toPure_1299_ = lean_ctor_get(v_toApplicative_1297_, 1);
lean_inc_n(v_toPure_1299_, 2);
lean_dec_ref(v_toApplicative_1297_);
v___x_1300_ = lean_box(v_explicit_1296_);
v___f_1301_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1301_, 0, v_fmt_1290_);
lean_closure_set(v___f_1301_, 1, v_expr_1291_);
lean_closure_set(v___f_1301_, 2, v_location_x3f_1293_);
lean_closure_set(v___f_1301_, 3, v_docString_x3f_1294_);
lean_closure_set(v___f_1301_, 4, v_mkDocString_x3f_1295_);
lean_closure_set(v___f_1301_, 5, v___x_1300_);
lean_closure_set(v___f_1301_, 6, v_toPure_1299_);
if (lean_obj_tag(v_lctx_x3f_1292_) == 0)
{
lean_object* v___x_1302_; 
lean_dec(v_toPure_1299_);
v___x_1302_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v_inst_1289_, v___f_1301_);
return v___x_1302_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_inst_1289_);
v_val_1303_ = lean_ctor_get(v_lctx_x3f_1292_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_lctx_x3f_1292_, 1);
v___x_1304_ = lean_apply_2(v_toPure_1299_, lean_box(0), v_val_1303_);
v___x_1305_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v___x_1304_, v___f_1301_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_fmt_1308_, lean_object* v_expr_1309_, lean_object* v_lctx_x3f_1310_, lean_object* v_location_x3f_1311_, lean_object* v_docString_x3f_1312_, lean_object* v_mkDocString_x3f_1313_, lean_object* v_explicit_1314_){
_start:
{
uint8_t v_explicit_boxed_1315_; lean_object* v_res_1316_; 
v_explicit_boxed_1315_ = lean_unbox(v_explicit_1314_);
v_res_1316_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1306_, v_inst_1307_, v_fmt_1308_, v_expr_1309_, v_lctx_x3f_1310_, v_location_x3f_1311_, v_docString_x3f_1312_, v_mkDocString_x3f_1313_, v_explicit_boxed_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_fmt_1320_, lean_object* v_expr_1321_, lean_object* v_lctx_x3f_1322_, lean_object* v_location_x3f_1323_, lean_object* v_docString_x3f_1324_, lean_object* v_mkDocString_x3f_1325_, uint8_t v_explicit_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1318_, v_inst_1319_, v_fmt_1320_, v_expr_1321_, v_lctx_x3f_1322_, v_location_x3f_1323_, v_docString_x3f_1324_, v_mkDocString_x3f_1325_, v_explicit_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_fmt_1331_, lean_object* v_expr_1332_, lean_object* v_lctx_x3f_1333_, lean_object* v_location_x3f_1334_, lean_object* v_docString_x3f_1335_, lean_object* v_mkDocString_x3f_1336_, lean_object* v_explicit_1337_){
_start:
{
uint8_t v_explicit_boxed_1338_; lean_object* v_res_1339_; 
v_explicit_boxed_1338_ = lean_unbox(v_explicit_1337_);
v_res_1339_ = l_Lean_MessageData_withExprHoverM(v_m_1328_, v_inst_1329_, v_inst_1330_, v_fmt_1331_, v_expr_1332_, v_lctx_x3f_1333_, v_location_x3f_1334_, v_docString_x3f_1335_, v_mkDocString_x3f_1336_, v_explicit_boxed_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1340_, lean_object* v_display_1341_, lean_object* v_toPure_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_____do__lift_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1345_, v_userName_1340_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v_inst_1344_);
lean_dec_ref(v_inst_1343_);
v___x_1347_ = l_Lean_MessageData_ofName(v_display_1341_);
v___x_1348_ = lean_apply_2(v_toPure_1342_, lean_box(0), v___x_1347_);
return v___x_1348_;
}
else
{
lean_object* v_val_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_toPure_1342_);
v_val_1349_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1351_ = v___x_1346_;
v_isShared_1352_ = v_isSharedCheck_1363_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_val_1349_);
lean_dec(v___x_1346_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1363_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = 1;
v___x_1354_ = l_Lean_Name_toString(v_display_1341_, v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 3);
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = l_Lean_LocalDecl_fvarId(v_val_1349_);
lean_dec(v_val_1349_);
v___x_1358_ = l_Lean_Expr_fvar___override(v___x_1357_);
v___x_1359_ = lean_box(0);
v___x_1360_ = 0;
v___x_1361_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1343_, v_inst_1344_, v___x_1356_, v___x_1358_, v___x_1359_, v___x_1359_, v___x_1359_, v___x_1359_, v___x_1360_);
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1364_, lean_object* v_display_1365_, lean_object* v_toPure_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_____do__lift_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1364_, v_display_1365_, v_toPure_1366_, v_inst_1367_, v_inst_1368_, v_____do__lift_1369_);
lean_dec_ref(v_____do__lift_1369_);
lean_dec(v_userName_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_userName_1373_){
_start:
{
lean_object* v_toApplicative_1374_; lean_object* v_toBind_1375_; lean_object* v_toPure_1376_; lean_object* v_display_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; 
v_toApplicative_1374_ = lean_ctor_get(v_inst_1371_, 0);
v_toBind_1375_ = lean_ctor_get(v_inst_1371_, 1);
lean_inc(v_toBind_1375_);
v_toPure_1376_ = lean_ctor_get(v_toApplicative_1374_, 1);
lean_inc(v_toPure_1376_);
lean_inc(v_userName_1373_);
v_display_1377_ = l_Lean_Name_simpMacroScopes(v_userName_1373_);
lean_inc(v_inst_1372_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1378_, 0, v_userName_1373_);
lean_closure_set(v___f_1378_, 1, v_display_1377_);
lean_closure_set(v___f_1378_, 2, v_toPure_1376_);
lean_closure_set(v___f_1378_, 3, v_inst_1371_);
lean_closure_set(v___f_1378_, 4, v_inst_1372_);
v___x_1379_ = lean_apply_4(v_toBind_1375_, lean_box(0), lean_box(0), v_inst_1372_, v___f_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_userName_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1381_, v_inst_1382_, v_userName_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
lean_ctor_set(v___x_1390_, 3, v___x_1389_);
lean_ctor_set(v___x_1390_, 4, v___x_1388_);
lean_ctor_set(v___x_1390_, 5, v___x_1388_);
lean_ctor_set(v___x_1390_, 6, v___x_1388_);
lean_ctor_set(v___x_1390_, 7, v___x_1388_);
lean_ctor_set(v___x_1390_, 8, v___x_1388_);
lean_ctor_set(v___x_1390_, 9, v___x_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1391_, lean_object* v_a_1392_){
_start:
{
switch(lean_obj_tag(v_a_1392_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1391_) == 0)
{
lean_object* v_hasSyntheticSorry_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_hasSyntheticSorry_1393_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_hasSyntheticSorry_1393_);
lean_dec_ref_known(v_a_1392_, 2);
v___x_1394_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1395_ = lean_apply_1(v_hasSyntheticSorry_1393_, v___x_1394_);
v___x_1396_ = lean_unbox(v___x_1395_);
return v___x_1396_;
}
else
{
lean_object* v_hasSyntheticSorry_1397_; lean_object* v_val_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_hasSyntheticSorry_1397_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_hasSyntheticSorry_1397_);
lean_dec_ref_known(v_a_1392_, 2);
v_val_1398_ = lean_ctor_get(v_mctx_x3f_1391_, 0);
lean_inc(v_val_1398_);
lean_dec_ref_known(v_mctx_x3f_1391_, 1);
v___x_1399_ = lean_apply_1(v_hasSyntheticSorry_1397_, v_val_1398_);
v___x_1400_ = lean_unbox(v___x_1399_);
return v___x_1400_;
}
}
case 3:
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v_mctx_1403_; lean_object* v___x_1404_; 
lean_dec(v_mctx_x3f_1391_);
v_a_1401_ = lean_ctor_get(v_a_1392_, 0);
lean_inc_ref(v_a_1401_);
v_a_1402_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1402_);
lean_dec_ref_known(v_a_1392_, 2);
v_mctx_1403_ = lean_ctor_get(v_a_1401_, 1);
lean_inc_ref(v_mctx_1403_);
lean_dec_ref(v_a_1401_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_mctx_1403_);
v_mctx_x3f_1391_ = v___x_1404_;
v_a_1392_ = v_a_1402_;
goto _start;
}
case 4:
{
lean_object* v_a_1406_; 
v_a_1406_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1406_);
lean_dec_ref_known(v_a_1392_, 2);
v_a_1392_ = v_a_1406_;
goto _start;
}
case 5:
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1408_);
lean_dec_ref_known(v_a_1392_, 2);
v_a_1392_ = v_a_1408_;
goto _start;
}
case 6:
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v_a_1392_, 0);
lean_inc_ref(v_a_1410_);
lean_dec_ref_known(v_a_1392_, 1);
v_a_1392_ = v_a_1410_;
goto _start;
}
case 7:
{
lean_object* v_a_1412_; lean_object* v_a_1413_; uint8_t v___x_1414_; 
v_a_1412_ = lean_ctor_get(v_a_1392_, 0);
lean_inc_ref(v_a_1412_);
v_a_1413_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1413_);
lean_dec_ref_known(v_a_1392_, 2);
lean_inc(v_mctx_x3f_1391_);
v___x_1414_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1391_, v_a_1412_);
if (v___x_1414_ == 0)
{
v_a_1392_ = v_a_1413_;
goto _start;
}
else
{
lean_dec_ref(v_a_1413_);
lean_dec(v_mctx_x3f_1391_);
return v___x_1414_;
}
}
case 8:
{
lean_object* v_a_1416_; 
v_a_1416_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1416_);
lean_dec_ref_known(v_a_1392_, 2);
v_a_1392_ = v_a_1416_;
goto _start;
}
case 11:
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_a_1418_);
lean_dec_ref_known(v_a_1392_, 2);
v_a_1392_ = v_a_1418_;
goto _start;
}
case 9:
{
lean_object* v_msg_1420_; lean_object* v_children_1421_; uint8_t v___x_1422_; 
v_msg_1420_ = lean_ctor_get(v_a_1392_, 1);
lean_inc_ref(v_msg_1420_);
v_children_1421_ = lean_ctor_get(v_a_1392_, 2);
lean_inc_ref(v_children_1421_);
lean_dec_ref_known(v_a_1392_, 3);
lean_inc(v_mctx_x3f_1391_);
v___x_1422_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1391_, v_msg_1420_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v_children_1421_);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v_children_1421_);
lean_dec(v_mctx_x3f_1391_);
return v___x_1422_;
}
else
{
if (v___x_1425_ == 0)
{
lean_dec_ref(v_children_1421_);
lean_dec(v_mctx_x3f_1391_);
return v___x_1422_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1424_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1391_, v_children_1421_, v___x_1426_, v___x_1427_);
lean_dec_ref(v_children_1421_);
return v___x_1428_;
}
}
}
else
{
lean_dec_ref(v_children_1421_);
lean_dec(v_mctx_x3f_1391_);
return v___x_1422_;
}
}
default: 
{
uint8_t v___x_1429_; 
lean_dec_ref(v_a_1392_);
lean_dec(v_mctx_x3f_1391_);
v___x_1429_ = 0;
return v___x_1429_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1430_, lean_object* v_as_1431_, size_t v_i_1432_, size_t v_stop_1433_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_eq(v_i_1432_, v_stop_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_array_uget_borrowed(v_as_1431_, v_i_1432_);
lean_inc(v___x_1435_);
lean_inc(v_mctx_x3f_1430_);
v___x_1436_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1430_, v___x_1435_);
if (v___x_1436_ == 0)
{
size_t v___x_1437_; size_t v___x_1438_; 
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_add(v_i_1432_, v___x_1437_);
v_i_1432_ = v___x_1438_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1430_);
return v___x_1436_;
}
}
else
{
uint8_t v___x_1440_; 
lean_dec(v_mctx_x3f_1430_);
v___x_1440_ = 0;
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1441_, lean_object* v_as_1442_, lean_object* v_i_1443_, lean_object* v_stop_1444_){
_start:
{
size_t v_i_boxed_1445_; size_t v_stop_boxed_1446_; uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_i_boxed_1445_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_stop_boxed_1446_ = lean_unbox_usize(v_stop_1444_);
lean_dec(v_stop_1444_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1441_, v_as_1442_, v_i_boxed_1445_, v_stop_boxed_1446_);
lean_dec_ref(v_as_1442_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1449_, v_a_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1453_){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1454_, v_msg_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1456_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_1459_, lean_object* v_decl_1460_, lean_object* v_ref_1461_){
_start:
{
lean_object* v_defValue_1463_; lean_object* v_descr_1464_; lean_object* v_deprecation_x3f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_defValue_1463_ = lean_ctor_get(v_decl_1460_, 0);
v_descr_1464_ = lean_ctor_get(v_decl_1460_, 1);
v_deprecation_x3f_1465_ = lean_ctor_get(v_decl_1460_, 2);
lean_inc(v_defValue_1463_);
v___x_1466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_defValue_1463_);
lean_inc(v_deprecation_x3f_1465_);
lean_inc_ref(v_descr_1464_);
lean_inc_n(v_name_1459_, 2);
v___x_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1467_, 0, v_name_1459_);
lean_ctor_set(v___x_1467_, 1, v_ref_1461_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
lean_ctor_set(v___x_1467_, 3, v_descr_1464_);
lean_ctor_set(v___x_1467_, 4, v_deprecation_x3f_1465_);
v___x_1468_ = lean_register_option(v_name_1459_, v___x_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1477_);
v___x_1470_ = v___x_1468_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v___x_1468_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc(v_defValue_1463_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_name_1459_);
lean_ctor_set(v___x_1472_, 1, v_defValue_1463_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_name_1459_);
v_a_1478_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1468_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1486_, lean_object* v_decl_1487_, lean_object* v_ref_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_1486_, v_decl_1487_, v_ref_1488_);
lean_dec_ref(v_decl_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1505_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1506_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1507_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_1504_, v___x_1505_, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_nat_to_int(v_a_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = l_instMonadBaseIO;
v___x_1514_ = l_instInhabitedOfMonad___redArg(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_2214__overap_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2214__overap_1518_ = lean_panic_fn_borrowed(v___x_1517_, v_msg_1515_);
v___x_1519_ = lean_apply_1(v___x_2214__overap_1518_, lean_box(0));
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_dec(v_x_1523_);
return v_x_1524_;
}
else
{
lean_object* v_head_1526_; lean_object* v_tail_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
v_head_1526_ = lean_ctor_get(v_x_1525_, 0);
v_tail_1527_ = lean_ctor_get(v_x_1525_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1529_ = v_x_1525_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_tail_1527_);
lean_inc(v_head_1526_);
lean_dec(v_x_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
lean_inc(v_x_1523_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 5);
lean_ctor_set(v___x_1529_, 1, v_x_1523_);
lean_ctor_set(v___x_1529_, 0, v_x_1524_);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_x_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_x_1523_);
v___x_1532_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_head_1526_);
v_x_1524_ = v___x_1533_;
v_x_1525_ = v_tail_1527_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_x_1538_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
else
{
lean_object* v_tail_1540_; 
v_tail_1540_ = lean_ctor_get(v_x_1537_, 1);
if (lean_obj_tag(v_tail_1540_) == 0)
{
lean_object* v_head_1541_; 
lean_dec(v_x_1538_);
v_head_1541_ = lean_ctor_get(v_x_1537_, 0);
lean_inc(v_head_1541_);
lean_dec_ref_known(v_x_1537_, 2);
return v_head_1541_;
}
else
{
lean_object* v_head_1542_; lean_object* v___x_1543_; 
lean_inc(v_tail_1540_);
v_head_1542_ = lean_ctor_get(v_x_1537_, 0);
lean_inc(v_head_1542_);
lean_dec_ref_known(v_x_1537_, 2);
v___x_1543_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1538_, v_head_1542_, v_tail_1540_);
return v___x_1543_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1558_; double v___x_1559_; 
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = lean_float_of_nat(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
switch(lean_obj_tag(v_x_1565_))
{
case 0:
{
lean_object* v_a_1567_; lean_object* v_fmt_1568_; 
lean_dec(v_x_1564_);
lean_dec_ref(v_x_1563_);
v_a_1567_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_a_1567_);
lean_dec_ref_known(v_x_1565_, 1);
v_fmt_1568_ = lean_ctor_get(v_a_1567_, 0);
lean_inc(v_fmt_1568_);
lean_dec_ref(v_a_1567_);
return v_fmt_1568_;
}
case 1:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_x_1563_);
v_a_1569_ = lean_ctor_get(v_x_1565_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v_x_1565_, 1);
v___x_1570_ = l_Lean_formatRawGoal(v_a_1569_);
return v___x_1570_;
}
else
{
lean_object* v_a_1571_; lean_object* v_val_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1571_ = lean_ctor_get(v_x_1565_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_x_1565_, 1);
v_val_1572_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v_x_1564_, 1);
v___x_1573_ = l_Lean_MessageData_mkPPContext(v_x_1563_, v_val_1572_);
lean_dec(v_val_1572_);
lean_dec_ref(v_x_1563_);
v___x_1574_ = l_Lean_ppGoal(v___x_1573_, v_a_1571_);
return v___x_1574_;
}
}
case 3:
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1577_; 
lean_dec(v_x_1564_);
v_a_1575_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_a_1575_);
v_a_1576_ = lean_ctor_get(v_x_1565_, 1);
lean_inc_ref(v_a_1576_);
lean_dec_ref_known(v_x_1565_, 2);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1575_);
v_x_1564_ = v___x_1577_;
v_x_1565_ = v_a_1576_;
goto _start;
}
case 4:
{
lean_object* v_a_1579_; lean_object* v_a_1580_; 
lean_dec_ref(v_x_1563_);
v_a_1579_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_a_1579_);
v_a_1580_ = lean_ctor_get(v_x_1565_, 1);
lean_inc_ref(v_a_1580_);
lean_dec_ref_known(v_x_1565_, 2);
v_x_1563_ = v_a_1579_;
v_x_1565_ = v_a_1580_;
goto _start;
}
case 5:
{
lean_object* v_a_1582_; lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1592_; 
v_a_1582_ = lean_ctor_get(v_x_1565_, 0);
v_a_1583_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1585_ = v_x_1565_;
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_inc(v_a_1582_);
lean_dec(v_x_1565_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1587_ = l_Lean_MessageData_formatAux(v_x_1563_, v_x_1564_, v_a_1583_);
v___x_1588_ = lean_nat_to_int(v_a_1582_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 4);
lean_ctor_set(v___x_1585_, 1, v___x_1587_);
lean_ctor_set(v___x_1585_, 0, v___x_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1587_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
case 6:
{
lean_object* v_a_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; 
v_a_1593_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_a_1593_);
lean_dec_ref_known(v_x_1565_, 1);
v___x_1594_ = l_Lean_MessageData_formatAux(v_x_1563_, v_x_1564_, v_a_1593_);
v___x_1595_ = 0;
v___x_1596_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*1, v___x_1595_);
return v___x_1596_;
}
case 7:
{
lean_object* v_a_1597_; lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1607_; 
v_a_1597_ = lean_ctor_get(v_x_1565_, 0);
v_a_1598_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1600_ = v_x_1565_;
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_inc(v_a_1597_);
lean_dec(v_x_1565_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_inc(v_x_1564_);
lean_inc_ref(v_x_1563_);
v___x_1602_ = l_Lean_MessageData_formatAux(v_x_1563_, v_x_1564_, v_a_1597_);
v___x_1603_ = l_Lean_MessageData_formatAux(v_x_1563_, v_x_1564_, v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 5);
lean_ctor_set(v___x_1600_, 1, v___x_1603_);
lean_ctor_set(v___x_1600_, 0, v___x_1602_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
case 9:
{
lean_object* v_data_1608_; lean_object* v_msg_1609_; lean_object* v_children_1610_; size_t v_sz_1611_; size_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v_cls_1627_; lean_object* v_result_x3f_1628_; double v_startTime_1629_; double v_stopTime_1630_; lean_object* v_msg_1632_; uint8_t v___x_1647_; 
v_data_1608_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_data_1608_);
v_msg_1609_ = lean_ctor_get(v_x_1565_, 1);
lean_inc_ref(v_msg_1609_);
v_children_1610_ = lean_ctor_get(v_x_1565_, 2);
lean_inc_ref(v_children_1610_);
lean_dec_ref_known(v_x_1565_, 3);
v_sz_1611_ = lean_array_size(v_children_1610_);
v___x_1612_ = ((size_t)0ULL);
lean_inc(v_x_1564_);
lean_inc_ref(v_x_1563_);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1563_, v_x_1564_, v_sz_1611_, v___x_1612_, v_children_1610_);
v_cls_1627_ = lean_ctor_get(v_data_1608_, 0);
lean_inc(v_cls_1627_);
v_result_x3f_1628_ = lean_ctor_get(v_data_1608_, 1);
lean_inc(v_result_x3f_1628_);
v_startTime_1629_ = lean_ctor_get_float(v_data_1608_, sizeof(void*)*3);
v_stopTime_1630_ = lean_ctor_get_float(v_data_1608_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1608_);
v___x_1647_ = l_Lean_Name_isAnonymous(v_cls_1627_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; double v___x_1663_; uint8_t v___x_1664_; 
v___x_1648_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1649_ = 1;
v___x_1650_ = l_Lean_Name_toString(v_cls_1627_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1648_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1663_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1664_ = lean_float_beq(v_startTime_1629_, v___x_1663_);
if (v___x_1664_ == 0)
{
goto v___jp_1655_;
}
else
{
if (v___x_1647_ == 0)
{
v_msg_1632_ = v___x_1654_;
goto v___jp_1631_;
}
else
{
goto v___jp_1655_;
}
}
v___jp_1655_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; double v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1656_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1654_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_float_sub(v_stopTime_1630_, v_startTime_1629_);
v___x_1659_ = lean_float_to_string(v___x_1658_);
v___x_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1657_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___x_1653_);
v_msg_1632_ = v___x_1662_;
goto v___jp_1631_;
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_result_x3f_1628_);
lean_dec(v_cls_1627_);
lean_dec_ref(v_msg_1609_);
lean_dec(v_x_1564_);
lean_dec_ref(v_x_1563_);
v___x_1665_ = lean_array_to_list(v___x_1613_);
v___x_1666_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1667_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1665_, v___x_1666_);
return v___x_1667_;
}
v___jp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1617_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___y_1615_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v___y_1616_);
v___x_1621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1618_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_array_to_list(v___x_1613_);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1625_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1619_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
return v___x_1626_;
}
v___jp_1631_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_MessageData_formatAux(v_x_1563_, v_x_1564_, v_msg_1609_);
if (lean_obj_tag(v_result_x3f_1628_) == 0)
{
v___y_1615_ = v_msg_1632_;
v___y_1616_ = v___x_1633_;
goto v___jp_1614_;
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1646_; 
v_val_1634_ = lean_ctor_get(v_result_x3f_1628_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_result_x3f_1628_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1636_ = v_result_x3f_1628_;
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v_result_x3f_1628_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1638_ = lean_unbox(v_val_1634_);
lean_dec(v_val_1634_);
v___x_1639_ = l_Lean_TraceResult_toEmoji(v___x_1638_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 3);
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1633_);
v___y_1615_ = v_msg_1632_;
v___y_1616_ = v___x_1644_;
goto v___jp_1614_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1668_; lean_object* v___x_1669_; lean_object* v___y_1671_; 
v_f_1668_ = lean_ctor_get(v_x_1565_, 0);
lean_inc_ref(v_f_1668_);
lean_dec_ref_known(v_x_1565_, 2);
v___x_1669_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_box(0);
v___y_1671_ = v___x_1687_;
goto v___jp_1670_;
}
else
{
lean_object* v_val_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_val_1688_ = lean_ctor_get(v_x_1564_, 0);
v___x_1689_ = l_Lean_MessageData_mkPPContext(v_x_1563_, v_val_1688_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
v___y_1671_ = v___x_1690_;
goto v___jp_1670_;
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_apply_2(v_f_1668_, v___y_1671_, lean_box(0));
v___x_1673_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1672_, v___x_1669_);
if (lean_obj_tag(v___x_1673_) == 1)
{
lean_object* v_val_1674_; 
lean_dec(v___x_1672_);
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_x_1565_ = v_val_1674_;
goto _start;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec(v___x_1673_);
lean_dec(v_x_1564_);
lean_dec_ref(v_x_1563_);
v___x_1676_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1677_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1678_ = lean_unsigned_to_nat(409u);
v___x_1679_ = lean_unsigned_to_nat(8u);
v___x_1680_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1681_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1672_);
lean_dec(v___x_1672_);
v___x_1682_ = 1;
v___x_1683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1681_, v___x_1682_);
v___x_1684_ = lean_string_append(v___x_1680_, v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = l_mkPanicMessageWithDecl(v___x_1676_, v___x_1677_, v___x_1678_, v___x_1679_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1685_);
return v___x_1686_;
}
}
}
default: 
{
lean_object* v_a_1691_; 
v_a_1691_ = lean_ctor_get(v_x_1565_, 1);
lean_inc_ref(v_a_1691_);
lean_dec_ref(v_x_1565_);
v_x_1565_ = v_a_1691_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1693_, lean_object* v_x_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_bs_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1699_ == 0)
{
lean_dec(v_x_1694_);
lean_dec_ref(v_x_1693_);
return v_bs_1697_;
}
else
{
lean_object* v_v_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_bs_x27_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v_v_1700_ = lean_array_uget_borrowed(v_bs_1697_, v_i_1696_);
lean_inc(v_v_1700_);
lean_inc(v_x_1694_);
lean_inc_ref(v_x_1693_);
v___x_1701_ = l_Lean_MessageData_formatAux(v_x_1693_, v_x_1694_, v_v_1700_);
v___x_1702_ = lean_unsigned_to_nat(0u);
v_bs_x27_1703_ = lean_array_uset(v_bs_1697_, v_i_1696_, v___x_1702_);
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1696_, v___x_1704_);
v___x_1706_ = lean_array_uset(v_bs_x27_1703_, v_i_1696_, v___x_1701_);
v_i_1696_ = v___x_1705_;
v_bs_1697_ = v___x_1706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1708_, lean_object* v_x_1709_, lean_object* v_sz_1710_, lean_object* v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1710_);
lean_dec(v_sz_1710_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1708_, v_x_1709_, v_sz_boxed_1714_, v_i_boxed_1715_, v_bs_1712_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_MessageData_formatAux(v_x_1717_, v_x_1718_, v_x_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1725_, lean_object* v_ctx_x3f_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1729_ = l_Lean_MessageData_formatAux(v___x_1728_, v_ctx_x3f_1726_, v_msgData_1725_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1730_, lean_object* v_ctx_x3f_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_MessageData_format(v_msgData_1730_, v_ctx_x3f_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_box(0);
v___x_1737_ = l_Lean_MessageData_format(v_msgData_1734_, v___x_1736_);
v___x_1738_ = l_Std_Format_defWidth;
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = l_Std_Format_pretty(v___x_1737_, v___x_1738_, v___x_1739_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_MessageData_toString(v_msgData_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1744_);
lean_ctor_set(v___x_1746_, 1, v_a_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_s_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1774_ = l_Lean_MessageData_ofFormat(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1775_){
_start:
{
if (lean_obj_tag(v_o_1775_) == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1776_;
}
else
{
lean_object* v_val_1777_; lean_object* v___x_1778_; 
v_val_1777_ = lean_ctor_get(v_o_1775_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v_o_1775_, 1);
v___x_1778_ = l_Lean_MessageData_ofExpr(v_val_1777_);
return v___x_1778_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1782_ = l_Lean_MessageData_ofFormat(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1787_ = l_Lean_MessageData_ofFormat(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1788_, lean_object* v_i_1789_, lean_object* v_acc_1790_){
_start:
{
lean_object* v___y_1792_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_array_get_size(v_es_1788_);
v___x_1797_ = lean_nat_dec_lt(v_i_1789_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_i_1789_);
v___x_1798_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_acc_1790_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v_e_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_e_1800_ = lean_array_fget_borrowed(v_es_1788_, v_i_1789_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_i_1789_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_acc_1790_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_inc(v_e_1800_);
v___x_1805_ = l_Lean_MessageData_ofExpr(v_e_1800_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___y_1792_ = v___x_1806_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_inc(v_e_1800_);
v___x_1807_ = l_Lean_MessageData_ofExpr(v_e_1800_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_acc_1790_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___y_1792_ = v___x_1808_;
goto v___jp_1791_;
}
}
v___jp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_nat_add(v_i_1789_, v___x_1793_);
lean_dec(v_i_1789_);
v_i_1789_ = v___x_1794_;
v_acc_1790_ = v___y_1792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1809_, lean_object* v_i_1810_, lean_object* v_acc_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1809_, v_i_1810_, v_acc_1811_);
lean_dec_ref(v_es_1809_);
return v_res_1812_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1817_ = l_Lean_MessageData_ofFormat(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1821_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1818_, v___x_1819_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1822_);
lean_dec_ref(v_es_1822_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1826_, lean_object* v_f_1827_, lean_object* v_r_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1829_ = lean_string_length(v_l_1826_);
v___x_1830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_l_1826_);
v___x_1831_ = l_Lean_MessageData_ofFormat(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v_f_1827_);
v___x_1833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_r_1828_);
v___x_1834_ = l_Lean_MessageData_ofFormat(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1829_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1840_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1841_ = l_Lean_MessageData_bracket(v___x_1839_, v_f_1838_, v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1842_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1844_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1845_ = l_Lean_MessageData_bracket(v___x_1843_, v_f_1842_, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref(v_x_1847_);
v___x_1848_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1848_;
}
else
{
lean_object* v_tail_1849_; 
v_tail_1849_ = lean_ctor_get(v_x_1846_, 1);
if (lean_obj_tag(v_tail_1849_) == 0)
{
lean_object* v_head_1850_; 
lean_dec_ref(v_x_1847_);
v_head_1850_ = lean_ctor_get(v_x_1846_, 0);
lean_inc(v_head_1850_);
lean_dec_ref_known(v_x_1846_, 2);
return v_head_1850_;
}
else
{
lean_object* v_head_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1860_; 
lean_inc(v_tail_1849_);
v_head_1851_ = lean_ctor_get(v_x_1846_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_x_1846_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_x_1846_, 1);
lean_dec(v_unused_1861_);
v___x_1853_ = v_x_1846_;
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_head_1851_);
lean_dec(v_x_1846_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
lean_inc_ref(v_x_1847_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 7);
lean_ctor_set(v___x_1853_, 1, v_x_1847_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_head_1851_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_x_1847_);
v___x_1856_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_Lean_MessageData_joinSep(v_tail_1849_, v_x_1847_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1866_ = l_Lean_MessageData_ofFormat(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1871_ = l_Lean_MessageData_ofFormat(v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_box(1);
v___x_1873_ = l_Lean_MessageData_ofFormat(v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1875_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1880_ = l_Lean_MessageData_joinSep(v_x_1877_, v___x_1879_);
v___x_1881_ = l_Lean_MessageData_sbracket(v___x_1880_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_array_to_list(v_msgs_1882_);
v___x_1884_ = l_Lean_MessageData_ofList(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1889_ = l_Lean_MessageData_ofFormat(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1894_ = l_Lean_MessageData_ofFormat(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1899_ = l_Lean_MessageData_ofFormat(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1900_){
_start:
{
if (lean_obj_tag(v_xs_1900_) == 0)
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1901_;
}
else
{
lean_object* v_tail_1902_; 
v_tail_1902_ = lean_ctor_get(v_xs_1900_, 1);
lean_inc(v_tail_1902_);
if (lean_obj_tag(v_tail_1902_) == 0)
{
lean_object* v_head_1903_; 
v_head_1903_ = lean_ctor_get(v_xs_1900_, 0);
lean_inc(v_head_1903_);
lean_dec_ref_known(v_xs_1900_, 2);
return v_head_1903_;
}
else
{
lean_object* v_tail_1904_; 
v_tail_1904_ = lean_ctor_get(v_tail_1902_, 1);
if (lean_obj_tag(v_tail_1904_) == 0)
{
lean_object* v_head_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1922_; 
v_head_1905_ = lean_ctor_get(v_xs_1900_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_xs_1900_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_xs_1900_, 1);
lean_dec(v_unused_1923_);
v___x_1907_ = v_xs_1900_;
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_head_1905_);
lean_dec(v_xs_1900_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_head_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1920_; 
v_head_1909_ = lean_ctor_get(v_tail_1902_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_tail_1902_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_tail_1902_, 1);
lean_dec(v_unused_1921_);
v___x_1911_ = v_tail_1902_;
v_isShared_1912_ = v_isSharedCheck_1920_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_head_1909_);
lean_dec(v_tail_1902_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1920_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 7);
lean_ctor_set(v___x_1911_, 1, v___x_1913_);
lean_ctor_set(v___x_1911_, 0, v_head_1905_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_head_1905_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 7);
lean_ctor_set(v___x_1907_, 1, v_head_1909_);
lean_ctor_set(v___x_1907_, 0, v___x_1915_);
v___x_1917_ = v___x_1907_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_head_1909_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
else
{
lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1947_; 
v_isSharedCheck_1947_ = !lean_is_exclusive(v_tail_1902_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; lean_object* v_unused_1949_; 
v_unused_1948_ = lean_ctor_get(v_tail_1902_, 1);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_tail_1902_, 0);
lean_dec(v_unused_1949_);
v___x_1925_ = v_tail_1902_;
v_isShared_1926_ = v_isSharedCheck_1947_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v_tail_1902_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1947_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1927_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1900_);
v___x_1928_ = lean_array_mk(v_xs_1900_);
v___x_1929_ = lean_array_pop(v___x_1928_);
v___x_1930_ = lean_array_to_list(v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1932_ = l_Lean_MessageData_joinSep(v___x_1930_, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 7);
lean_ctor_set(v___x_1925_, 1, v___x_1933_);
lean_ctor_set(v___x_1925_, 0, v___x_1932_);
v___x_1935_ = v___x_1925_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v___x_1936_ = l_List_getLast_x21___redArg(v___x_1927_, v_xs_1900_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_xs_1900_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; 
v_unused_1944_ = lean_ctor_get(v_xs_1900_, 1);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_xs_1900_, 0);
lean_dec(v_unused_1945_);
v___x_1938_ = v_xs_1900_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v_xs_1900_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 7);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
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
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1954_ = l_Lean_MessageData_ofFormat(v___x_1953_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1959_ = l_Lean_MessageData_ofFormat(v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1960_){
_start:
{
if (lean_obj_tag(v_xs_1960_) == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1961_;
}
else
{
lean_object* v_tail_1962_; 
v_tail_1962_ = lean_ctor_get(v_xs_1960_, 1);
lean_inc(v_tail_1962_);
if (lean_obj_tag(v_tail_1962_) == 0)
{
lean_object* v_head_1963_; 
v_head_1963_ = lean_ctor_get(v_xs_1960_, 0);
lean_inc(v_head_1963_);
lean_dec_ref_known(v_xs_1960_, 2);
return v_head_1963_;
}
else
{
lean_object* v_tail_1964_; 
v_tail_1964_ = lean_ctor_get(v_tail_1962_, 1);
if (lean_obj_tag(v_tail_1964_) == 0)
{
lean_object* v_head_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1982_; 
v_head_1965_ = lean_ctor_get(v_xs_1960_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_xs_1960_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_xs_1960_, 1);
lean_dec(v_unused_1983_);
v___x_1967_ = v_xs_1960_;
v_isShared_1968_ = v_isSharedCheck_1982_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_head_1965_);
lean_dec(v_xs_1960_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1982_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_head_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v_head_1969_ = lean_ctor_get(v_tail_1962_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_tail_1962_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_tail_1962_, 1);
lean_dec(v_unused_1981_);
v___x_1971_ = v_tail_1962_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_head_1969_);
lean_dec(v_tail_1962_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 7);
lean_ctor_set(v___x_1971_, 1, v___x_1973_);
lean_ctor_set(v___x_1971_, 0, v_head_1965_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_head_1965_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 7);
lean_ctor_set(v___x_1967_, 1, v_head_1969_);
lean_ctor_set(v___x_1967_, 0, v___x_1975_);
v___x_1977_ = v___x_1967_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_head_1969_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2007_; 
v_isSharedCheck_2007_ = !lean_is_exclusive(v_tail_1962_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; lean_object* v_unused_2009_; 
v_unused_2008_ = lean_ctor_get(v_tail_1962_, 1);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_tail_1962_, 0);
lean_dec(v_unused_2009_);
v___x_1985_ = v_tail_1962_;
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_tail_1962_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1987_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1960_);
v___x_1988_ = lean_array_mk(v_xs_1960_);
v___x_1989_ = lean_array_pop(v___x_1988_);
v___x_1990_ = lean_array_to_list(v___x_1989_);
v___x_1991_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1992_ = l_Lean_MessageData_joinSep(v___x_1990_, v___x_1991_);
v___x_1993_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 7);
lean_ctor_set(v___x_1985_, 1, v___x_1993_);
lean_ctor_set(v___x_1985_, 0, v___x_1992_);
v___x_1995_ = v___x_1985_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v___x_1996_ = l_List_getLast_x21___redArg(v___x_1987_, v_xs_1960_);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_xs_1960_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; lean_object* v_unused_2005_; 
v_unused_2004_ = lean_ctor_get(v_xs_1960_, 1);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_xs_1960_, 0);
lean_dec(v_unused_2005_);
v___x_1998_ = v_xs_1960_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_xs_1960_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 7);
lean_ctor_set(v___x_1998_, 1, v___x_1996_);
lean_ctor_set(v___x_1998_, 0, v___x_1995_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
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
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2016_ = l_Lean_MessageData_ofFormat(v___x_2015_);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2018_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v_note_2020_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2027_ = l_Lean_MessageData_ofFormat(v___x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2029_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2031_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v_hint_2031_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2038_ = lean_box(0);
v___x_2039_ = l_List_mapTR_loop___redArg(v___x_2037_, v_es_2036_, v___x_2038_);
v___x_2040_ = l_Lean_MessageData_ofList(v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2044_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2045_ = l_Lean_instInhabitedPosition_default;
v___x_2046_ = lean_box(0);
v___x_2047_ = 0;
v___x_2048_ = 2;
v___x_2049_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2049_, 0, v___x_2044_);
lean_ctor_set(v___x_2049_, 1, v___x_2045_);
lean_ctor_set(v___x_2049_, 2, v___x_2046_);
lean_ctor_set(v___x_2049_, 3, v___x_2044_);
lean_ctor_set(v___x_2049_, 4, v_inst_2043_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*5, v___x_2047_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*5 + 1, v___x_2048_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*5 + 2, v___x_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2050_, lean_object* v_inst_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2055_, lean_object* v_inst_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v_fileName_2072_; lean_object* v_pos_2073_; lean_object* v_endPos_2074_; uint8_t v_keepFullRange_2075_; uint8_t v_severity_2076_; uint8_t v_isSilent_2077_; lean_object* v_caption_2078_; lean_object* v_data_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_fileName_2072_ = lean_ctor_get(v_x_2071_, 0);
lean_inc_ref(v_fileName_2072_);
v_pos_2073_ = lean_ctor_get(v_x_2071_, 1);
lean_inc_ref(v_pos_2073_);
v_endPos_2074_ = lean_ctor_get(v_x_2071_, 2);
lean_inc(v_endPos_2074_);
v_keepFullRange_2075_ = lean_ctor_get_uint8(v_x_2071_, sizeof(void*)*5);
v_severity_2076_ = lean_ctor_get_uint8(v_x_2071_, sizeof(void*)*5 + 1);
v_isSilent_2077_ = lean_ctor_get_uint8(v_x_2071_, sizeof(void*)*5 + 2);
v_caption_2078_ = lean_ctor_get(v_x_2071_, 3);
lean_inc_ref(v_caption_2078_);
v_data_2079_ = lean_ctor_get(v_x_2071_, 4);
lean_inc(v_data_2079_);
lean_dec_ref(v_x_2071_);
v___x_2080_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2081_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_fileName_2072_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2087_ = l_Lean_instToJsonPosition_toJson(v_pos_2073_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2084_);
v___x_2090_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2091_ = l_Lean_Option_toJson___redArg(v___x_2080_, v_endPos_2074_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2084_);
v___x_2094_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2095_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2095_, 0, v_keepFullRange_2075_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2084_);
v___x_2098_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2099_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2076_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2084_);
v___x_2102_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2103_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2103_, 0, v_isSilent_2077_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2084_);
v___x_2106_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_caption_2078_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2084_);
v___x_2110_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2111_ = lean_apply_1(v_inst_2070_, v_data_2079_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___x_2084_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2084_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2109_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2105_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2101_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2097_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2093_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2089_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2085_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2123_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2124_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2122_, v___x_2121_, v___x_2123_);
v___x_2125_ = l_Lean_Json_mkObj(v___x_2124_);
lean_dec(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2126_, lean_object* v_inst_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2131_, 0, lean_box(0));
lean_closure_set(v___x_2131_, 1, v_inst_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2132_, lean_object* v_inst_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2134_, 0, lean_box(0));
lean_closure_set(v___x_2134_, 1, v_inst_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = 1;
v___x_2141_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2145_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2146_ = lean_string_append(v___x_2145_, v___x_2144_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = 1;
v___x_2150_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2150_, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2153_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2154_ = lean_string_append(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2157_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2158_ = lean_string_append(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = 1;
v___x_2165_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2166_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2168_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2169_ = lean_string_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2171_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = 1;
v___x_2176_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2177_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2179_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2180_ = lean_string_append(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2182_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2183_ = lean_string_append(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = 1;
v___x_2188_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2191_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2192_ = lean_string_append(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2194_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2195_ = lean_string_append(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = 1;
v___x_2199_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2200_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2202_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2203_ = lean_string_append(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2205_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2206_ = lean_string_append(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = 1;
v___x_2210_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2213_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2214_ = lean_string_append(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2216_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2217_ = lean_string_append(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = 1;
v___x_2221_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2222_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2221_, v___x_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2224_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2225_ = lean_string_append(v___x_2224_, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2227_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2228_ = lean_string_append(v___x_2227_, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = 1;
v___x_2232_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2233_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2235_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2236_ = lean_string_append(v___x_2235_, v___x_2234_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2238_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2239_ = lean_string_append(v___x_2238_, v___x_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2240_, lean_object* v_json_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2243_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2241_);
v___x_2244_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2242_, v___x_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
v___x_2249_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
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
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_a_2263_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2264_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2265_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2266_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2241_);
v___x_2267_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2264_, v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
v___x_2272_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
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
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
v___x_2287_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2241_);
v___x_2288_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2265_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
v___x_2293_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
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
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
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
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2307_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2308_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2309_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2241_);
v___x_2310_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2308_, v___x_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2316_ = lean_string_append(v___x_2315_, v_a_2311_);
lean_dec(v_a_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2316_);
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2321_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2310_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2310_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 0);
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
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
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2329_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2330_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2331_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2241_);
v___x_2332_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2330_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2342_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2342_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2338_ = lean_string_append(v___x_2337_, v_a_2333_);
lean_dec(v_a_2333_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2338_);
v___x_2340_ = v___x_2335_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2343_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2332_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2332_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 0);
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2351_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2352_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2241_);
v___x_2353_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2308_, v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2358_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2359_ = lean_string_append(v___x_2358_, v_a_2354_);
lean_dec(v_a_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
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
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2364_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2353_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2353_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 0);
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2372_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2373_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2241_);
v___x_2374_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v___x_2242_, v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2384_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2384_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2379_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2380_ = lean_string_append(v___x_2379_, v_a_2375_);
lean_dec(v_a_2375_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
lean_dec(v_json_2241_);
lean_dec_ref(v_inst_2240_);
v_a_2385_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2374_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2374_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_a_2393_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2394_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2395_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2241_, v_inst_2240_, v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_a_2393_);
lean_dec(v_a_2372_);
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2405_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2405_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2401_ = lean_string_append(v___x_2400_, v_a_2396_);
lean_dec(v_a_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
else
{
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_a_2393_);
lean_dec(v_a_2372_);
lean_dec(v_a_2351_);
lean_dec(v_a_2329_);
lean_dec(v_a_2307_);
lean_dec(v_a_2286_);
lean_dec(v_a_2263_);
v_a_2406_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2395_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2395_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 0);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2425_; 
v_a_2414_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2416_ = v___x_2395_;
v_isShared_2417_ = v_isSharedCheck_2425_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2395_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2425_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2423_; 
v___x_2418_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2418_, 0, v_a_2263_);
lean_ctor_set(v___x_2418_, 1, v_a_2286_);
lean_ctor_set(v___x_2418_, 2, v_a_2307_);
lean_ctor_set(v___x_2418_, 3, v_a_2393_);
lean_ctor_set(v___x_2418_, 4, v_a_2414_);
v___x_2419_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*5, v___x_2419_);
v___x_2420_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*5 + 1, v___x_2420_);
v___x_2421_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*5 + 2, v___x_2421_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2423_ = v___x_2416_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2426_, lean_object* v_inst_2427_, lean_object* v_json_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2427_, v_json_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2431_, 0, lean_box(0));
lean_closure_set(v___x_2431_, 1, v_inst_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2432_, lean_object* v_inst_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2434_, 0, lean_box(0));
lean_closure_set(v___x_2434_, 1, v_inst_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_box(0);
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; lean_object* v___x_2438_; 
v_val_2437_ = lean_ctor_get(v_x_2435_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v_x_2435_, 1);
v___x_2438_ = l_Lean_instToJsonPosition_toJson(v_val_2437_);
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
if (lean_obj_tag(v_a_2439_) == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_array_to_list(v_a_2440_);
return v___x_2441_;
}
else
{
lean_object* v_head_2442_; lean_object* v_tail_2443_; lean_object* v___x_2444_; 
v_head_2442_ = lean_ctor_get(v_a_2439_, 0);
lean_inc(v_head_2442_);
v_tail_2443_ = lean_ctor_get(v_a_2439_, 1);
lean_inc(v_tail_2443_);
lean_dec_ref_known(v_a_2439_, 2);
v___x_2444_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2440_, v_head_2442_);
v_a_2439_ = v_tail_2443_;
v_a_2440_ = v___x_2444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2447_){
_start:
{
lean_object* v_toBaseMessage_2448_; lean_object* v_kind_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2514_; 
v_toBaseMessage_2448_ = lean_ctor_get(v_x_2447_, 0);
v_kind_2449_ = lean_ctor_get(v_x_2447_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_x_2447_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2451_ = v_x_2447_;
v_isShared_2452_ = v_isSharedCheck_2514_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_kind_2449_);
lean_inc(v_toBaseMessage_2448_);
lean_dec(v_x_2447_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2514_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_fileName_2453_; lean_object* v_pos_2454_; lean_object* v_endPos_2455_; uint8_t v_keepFullRange_2456_; uint8_t v_severity_2457_; uint8_t v_isSilent_2458_; lean_object* v_caption_2459_; lean_object* v_data_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v_fileName_2453_ = lean_ctor_get(v_toBaseMessage_2448_, 0);
lean_inc_ref(v_fileName_2453_);
v_pos_2454_ = lean_ctor_get(v_toBaseMessage_2448_, 1);
lean_inc_ref(v_pos_2454_);
v_endPos_2455_ = lean_ctor_get(v_toBaseMessage_2448_, 2);
lean_inc(v_endPos_2455_);
v_keepFullRange_2456_ = lean_ctor_get_uint8(v_toBaseMessage_2448_, sizeof(void*)*5);
v_severity_2457_ = lean_ctor_get_uint8(v_toBaseMessage_2448_, sizeof(void*)*5 + 1);
v_isSilent_2458_ = lean_ctor_get_uint8(v_toBaseMessage_2448_, sizeof(void*)*5 + 2);
v_caption_2459_ = lean_ctor_get(v_toBaseMessage_2448_, 3);
lean_inc_ref(v_caption_2459_);
v_data_2460_ = lean_ctor_get(v_toBaseMessage_2448_, 4);
lean_inc(v_data_2460_);
lean_dec_ref(v_toBaseMessage_2448_);
v___x_2461_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_fileName_2453_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2462_);
lean_ctor_set(v___x_2451_, 0, v___x_2461_);
v___x_2464_ = v___x_2451_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2468_ = l_Lean_instToJsonPosition_toJson(v_pos_2454_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2465_);
v___x_2471_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2472_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2455_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v___x_2465_);
v___x_2475_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2476_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2476_, 0, v_keepFullRange_2456_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2465_);
v___x_2479_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2480_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2457_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2465_);
v___x_2483_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2484_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2484_, 0, v_isSilent_2458_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2465_);
v___x_2487_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_caption_2459_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2465_);
v___x_2491_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_data_2460_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2465_);
v___x_2495_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2496_ = 1;
v___x_2497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2449_, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2495_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2465_);
v___x_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2465_);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2494_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2490_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2486_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2482_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2478_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2474_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2470_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2466_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2511_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2509_, v___x_2510_);
v___x_2512_ = l_Lean_Json_mkObj(v___x_2511_);
lean_dec(v___x_2511_);
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2517_, lean_object* v_k_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = l_Lean_Json_getObjValD(v_j_2517_, v_k_2518_);
v___x_2520_ = l_Lean_Json_getStr_x3f(v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2521_, lean_object* v_k_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2521_, v_k_2522_);
lean_dec_ref(v_k_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2524_, lean_object* v_k_2525_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = l_Lean_Json_getObjValD(v_j_2524_, v_k_2525_);
v___x_2527_ = l_Lean_instFromJsonPosition_fromJson(v___x_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2528_, lean_object* v_k_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2528_, v_k_2529_);
lean_dec_ref(v_k_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2531_, lean_object* v_k_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = l_Lean_Json_getObjValD(v_j_2531_, v_k_2532_);
v___x_2534_ = l_Lean_Json_getBool_x3f(v___x_2533_);
lean_dec(v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2535_, lean_object* v_k_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2535_, v_k_2536_);
lean_dec_ref(v_k_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2538_, lean_object* v_k_2539_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = l_Lean_Json_getObjValD(v_j_2538_, v_k_2539_);
v___x_2541_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2542_, lean_object* v_k_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2542_, v_k_2543_);
lean_dec_ref(v_k_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2545_, lean_object* v_k_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = l_Lean_Json_getObjValD(v_j_2545_, v_k_2546_);
v___x_2548_ = l_Lean_Name_fromJson_x3f(v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2549_, lean_object* v_k_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2549_, v_k_2550_);
lean_dec_ref(v_k_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2554_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_instFromJsonPosition_fromJson(v_x_2554_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2573_; 
v_a_2565_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2567_ = v___x_2556_;
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2556_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2573_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_a_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2574_, lean_object* v_k_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = l_Lean_Json_getObjValD(v_j_2574_, v_k_2575_);
v___x_2577_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2578_, lean_object* v_k_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2578_, v_k_2579_);
lean_dec_ref(v_k_2579_);
return v_res_2580_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = 1;
v___x_2586_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2587_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2589_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2590_ = lean_string_append(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2592_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2593_ = lean_string_append(v___x_2592_, v___x_2591_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2595_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2596_ = lean_string_append(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2598_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2599_ = lean_string_append(v___x_2598_, v___x_2597_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2601_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2602_ = lean_string_append(v___x_2601_, v___x_2600_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2604_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2605_ = lean_string_append(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2607_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2608_ = lean_string_append(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2610_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2611_ = lean_string_append(v___x_2610_, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2613_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2614_ = lean_string_append(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2616_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2617_ = lean_string_append(v___x_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2619_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2620_ = lean_string_append(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2622_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2623_ = lean_string_append(v___x_2622_, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2625_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2626_ = lean_string_append(v___x_2625_, v___x_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2628_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2629_ = lean_string_append(v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2631_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2632_ = lean_string_append(v___x_2631_, v___x_2630_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2634_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2635_ = lean_string_append(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2637_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2638_ = lean_string_append(v___x_2637_, v___x_2636_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = 1;
v___x_2642_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2645_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2646_ = lean_string_append(v___x_2645_, v___x_2644_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2648_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2649_ = lean_string_append(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2650_);
v___x_2652_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2650_, v___x_2651_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_json_2650_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2662_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2662_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2657_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2658_ = lean_string_append(v___x_2657_, v_a_2653_);
lean_dec(v_a_2653_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2658_);
v___x_2660_ = v___x_2655_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v_json_2650_);
v_a_2663_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2652_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2652_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 0);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2672_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2650_);
v___x_2673_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2650_, v___x_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2683_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2683_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2679_ = lean_string_append(v___x_2678_, v_a_2674_);
lean_dec(v_a_2674_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2679_);
v___x_2681_ = v___x_2676_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2684_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2673_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2673_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set_tag(v___x_2686_, 0);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_a_2692_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2693_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2650_);
v___x_2694_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2650_, v___x_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2699_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2700_ = lean_string_append(v___x_2699_, v_a_2695_);
lean_dec(v_a_2695_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2705_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2694_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2694_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 0);
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2713_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2714_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2650_);
v___x_2715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2650_, v___x_2714_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2725_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2725_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2720_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2721_ = lean_string_append(v___x_2720_, v_a_2716_);
lean_dec(v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2721_);
v___x_2723_ = v___x_2718_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
else
{
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2726_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2715_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2715_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set_tag(v___x_2728_, 0);
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_a_2734_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2735_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2650_);
v___x_2736_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2650_, v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2742_ = lean_string_append(v___x_2741_, v_a_2737_);
lean_dec(v_a_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2742_);
v___x_2744_ = v___x_2739_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2747_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2736_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2736_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 0);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2756_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2650_);
v___x_2757_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2650_, v___x_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2767_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2767_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2762_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2763_ = lean_string_append(v___x_2762_, v_a_2758_);
lean_dec(v_a_2758_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2768_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2757_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2757_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2757_, 1);
v___x_2777_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2650_);
v___x_2778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2650_, v___x_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2783_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2784_ = lean_string_append(v___x_2783_, v_a_2779_);
lean_dec(v_a_2779_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2789_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2778_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2778_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2798_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2650_);
v___x_2799_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2650_, v___x_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2809_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2809_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2804_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2805_ = lean_string_append(v___x_2804_, v_a_2800_);
lean_dec(v_a_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2805_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
lean_dec(v_json_2650_);
v_a_2810_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2799_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2799_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 0);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2819_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2820_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2650_, v___x_2819_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2818_);
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2825_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2826_ = lean_string_append(v___x_2825_, v_a_2821_);
lean_dec(v_a_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2826_);
v___x_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_a_2818_);
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_a_2734_);
lean_dec(v_a_2713_);
lean_dec(v_a_2692_);
lean_dec(v_a_2671_);
v_a_2831_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2820_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2820_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 0);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2851_; 
v_a_2839_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2841_ = v___x_2820_;
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2820_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; uint8_t v___x_2844_; uint8_t v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2843_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2843_, 0, v_a_2671_);
lean_ctor_set(v___x_2843_, 1, v_a_2692_);
lean_ctor_set(v___x_2843_, 2, v_a_2713_);
lean_ctor_set(v___x_2843_, 3, v_a_2797_);
lean_ctor_set(v___x_2843_, 4, v_a_2818_);
v___x_2844_ = lean_unbox(v_a_2734_);
lean_dec(v_a_2734_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*5, v___x_2844_);
v___x_2845_ = lean_unbox(v_a_2755_);
lean_dec(v_a_2755_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*5 + 1, v___x_2845_);
v___x_2846_ = lean_unbox(v_a_2776_);
lean_dec(v_a_2776_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*5 + 2, v___x_2846_);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2843_);
lean_ctor_set(v___x_2847_, 1, v_a_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2847_);
v___x_2849_ = v___x_2841_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2858_ = l_Lean_Name_str___override(v_errorName_2856_, v___x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2859_, lean_object* v_name_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = l_Lean_kindOfErrorName(v_name_2860_);
v___x_2862_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_msg_2859_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2864_){
_start:
{
switch(lean_obj_tag(v_a_2864_))
{
case 0:
{
return v_a_2864_;
}
case 1:
{
lean_object* v_pre_2865_; lean_object* v_str_2866_; lean_object* v_p_x27_2867_; uint8_t v___y_2869_; uint8_t v___x_2872_; 
v_pre_2865_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_pre_2865_);
v_str_2866_ = lean_ctor_get(v_a_2864_, 1);
lean_inc_ref(v_str_2866_);
lean_dec_ref_known(v_a_2864_, 2);
v_p_x27_2867_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2865_);
v___x_2872_ = l_Lean_Name_isAnonymous(v_p_x27_2867_);
if (v___x_2872_ == 0)
{
v___y_2869_ = v___x_2872_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2874_ = lean_string_dec_eq(v_str_2866_, v___x_2873_);
v___y_2869_ = v___x_2874_;
goto v___jp_2868_;
}
v___jp_2868_:
{
if (v___y_2869_ == 0)
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Name_str___override(v_p_x27_2867_, v_str_2866_);
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_p_x27_2867_);
lean_dec_ref(v_str_2866_);
v___x_2871_ = lean_box(0);
return v___x_2871_;
}
}
}
default: 
{
lean_object* v_pre_2875_; lean_object* v_i_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_pre_2875_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_pre_2875_);
v_i_2876_ = lean_ctor_get(v_a_2864_, 1);
lean_inc(v_i_2876_);
lean_dec_ref_known(v_a_2864_, 2);
v___x_2877_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2875_);
v___x_2878_ = l_Lean_Name_num___override(v___x_2877_, v_i_2876_);
return v___x_2878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2879_){
_start:
{
switch(lean_obj_tag(v_x_2879_))
{
case 3:
{
lean_object* v_a_2880_; lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2889_; 
v_a_2880_ = lean_ctor_get(v_x_2879_, 0);
v_a_2881_ = lean_ctor_get(v_x_2879_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2883_ = v_x_2879_;
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_inc(v_a_2880_);
lean_dec(v_x_2879_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2885_ = l_Lean_MessageData_stripNestedTags(v_a_2881_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 1, v___x_2885_);
v___x_2887_ = v___x_2883_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2880_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
case 4:
{
lean_object* v_a_2890_; lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_a_2890_ = lean_ctor_get(v_x_2879_, 0);
v_a_2891_ = lean_ctor_get(v_x_2879_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v_x_2879_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_inc(v_a_2890_);
lean_dec(v_x_2879_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Lean_MessageData_stripNestedTags(v_a_2891_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2890_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
case 8:
{
lean_object* v_a_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_a_2900_ = lean_ctor_get(v_x_2879_, 0);
v_a_2901_ = lean_ctor_get(v_x_2879_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v_x_2879_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_inc(v_a_2900_);
lean_dec(v_x_2879_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2900_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_a_2901_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
case 11:
{
lean_object* v_a_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_a_2910_ = lean_ctor_get(v_x_2879_, 0);
v_a_2911_ = lean_ctor_get(v_x_2879_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v_x_2879_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_inc(v_a_2910_);
lean_dec(v_x_2879_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l_Lean_MessageData_stripNestedTags(v_a_2911_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
default: 
{
return v_x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2920_){
_start:
{
if (lean_obj_tag(v_x_2920_) == 1)
{
lean_object* v_pre_2921_; lean_object* v_str_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_pre_2921_ = lean_ctor_get(v_x_2920_, 0);
v_str_2922_ = lean_ctor_get(v_x_2920_, 1);
v___x_2923_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2924_ = lean_string_dec_eq(v_str_2922_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_box(0);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; 
lean_inc(v_pre_2921_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_pre_2921_);
return v___x_2926_;
}
}
else
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_box(0);
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_errorNameOfKind_x3f(v_x_2928_);
lean_dec(v_x_2928_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2930_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = l_Lean_MessageData_kind(v_msg_2930_);
v___x_2932_ = l_Lean_errorNameOfKind_x3f(v___x_2931_);
lean_dec(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_MessageData_errorName_x3f(v_msg_2933_);
lean_dec_ref(v_msg_2933_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2935_){
_start:
{
lean_object* v_data_2936_; lean_object* v___x_2937_; 
v_data_2936_ = lean_ctor_get(v_msg_2935_, 4);
v___x_2937_ = l_Lean_MessageData_errorName_x3f(v_data_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Message_errorName_x3f(v_msg_2938_);
lean_dec_ref(v_msg_2938_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2940_){
_start:
{
lean_object* v_toBaseMessage_2941_; lean_object* v_fileName_2942_; lean_object* v_pos_2943_; lean_object* v_endPos_2944_; uint8_t v_keepFullRange_2945_; uint8_t v_severity_2946_; uint8_t v_isSilent_2947_; lean_object* v_caption_2948_; lean_object* v_data_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2958_; 
v_toBaseMessage_2941_ = lean_ctor_get(v_msg_2940_, 0);
lean_inc_ref(v_toBaseMessage_2941_);
lean_dec_ref(v_msg_2940_);
v_fileName_2942_ = lean_ctor_get(v_toBaseMessage_2941_, 0);
v_pos_2943_ = lean_ctor_get(v_toBaseMessage_2941_, 1);
v_endPos_2944_ = lean_ctor_get(v_toBaseMessage_2941_, 2);
v_keepFullRange_2945_ = lean_ctor_get_uint8(v_toBaseMessage_2941_, sizeof(void*)*5);
v_severity_2946_ = lean_ctor_get_uint8(v_toBaseMessage_2941_, sizeof(void*)*5 + 1);
v_isSilent_2947_ = lean_ctor_get_uint8(v_toBaseMessage_2941_, sizeof(void*)*5 + 2);
v_caption_2948_ = lean_ctor_get(v_toBaseMessage_2941_, 3);
v_data_2949_ = lean_ctor_get(v_toBaseMessage_2941_, 4);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_toBaseMessage_2941_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2951_ = v_toBaseMessage_2941_;
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_data_2949_);
lean_inc(v_caption_2948_);
lean_inc(v_endPos_2944_);
lean_inc(v_pos_2943_);
lean_inc(v_fileName_2942_);
lean_dec(v_toBaseMessage_2941_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_data_2949_);
v___x_2954_ = l_Lean_MessageData_ofFormat(v___x_2953_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 4, v___x_2954_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_fileName_2942_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_pos_2943_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_endPos_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_caption_2948_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___x_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*5, v_keepFullRange_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*5 + 1, v_severity_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*5 + 2, v_isSilent_2947_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2964_, uint8_t v_includeEndPos_2965_){
_start:
{
lean_object* v___y_2967_; uint8_t v___y_2971_; lean_object* v___y_2972_; uint32_t v___y_2973_; lean_object* v_str_2977_; lean_object* v_toBaseMessage_2989_; lean_object* v_kind_2990_; lean_object* v_fileName_2991_; lean_object* v_pos_2992_; lean_object* v_endPos_2993_; uint8_t v_severity_2994_; lean_object* v_caption_2995_; lean_object* v_data_2996_; lean_object* v___y_2998_; lean_object* v_str_2999_; lean_object* v___y_3007_; 
v_toBaseMessage_2989_ = lean_ctor_get(v_msg_2964_, 0);
lean_inc_ref(v_toBaseMessage_2989_);
v_kind_2990_ = lean_ctor_get(v_msg_2964_, 1);
lean_inc(v_kind_2990_);
lean_dec_ref(v_msg_2964_);
v_fileName_2991_ = lean_ctor_get(v_toBaseMessage_2989_, 0);
lean_inc_ref(v_fileName_2991_);
v_pos_2992_ = lean_ctor_get(v_toBaseMessage_2989_, 1);
lean_inc_ref(v_pos_2992_);
v_endPos_2993_ = lean_ctor_get(v_toBaseMessage_2989_, 2);
lean_inc(v_endPos_2993_);
v_severity_2994_ = lean_ctor_get_uint8(v_toBaseMessage_2989_, sizeof(void*)*5 + 1);
v_caption_2995_ = lean_ctor_get(v_toBaseMessage_2989_, 3);
lean_inc_ref(v_caption_2995_);
v_data_2996_ = lean_ctor_get(v_toBaseMessage_2989_, 4);
lean_inc(v_data_2996_);
lean_dec_ref(v_toBaseMessage_2989_);
if (v_includeEndPos_2965_ == 0)
{
lean_object* v___x_3013_; 
lean_dec(v_endPos_2993_);
v___x_3013_ = lean_box(0);
v___y_3007_ = v___x_3013_;
goto v___jp_3006_;
}
else
{
v___y_3007_ = v_endPos_2993_;
goto v___jp_3006_;
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v_str_2969_; 
v___x_2968_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2969_ = lean_string_append(v___y_2967_, v___x_2968_);
return v_str_2969_;
}
v___jp_2970_:
{
uint32_t v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = 10;
v___x_2975_ = lean_uint32_dec_eq(v___y_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
v___y_2967_ = v___y_2972_;
goto v___jp_2966_;
}
else
{
if (v___y_2971_ == 0)
{
return v___y_2972_;
}
else
{
v___y_2967_ = v___y_2972_;
goto v___jp_2966_;
}
}
}
v___jp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_string_utf8_byte_size(v_str_2977_);
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_nat_dec_eq(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_inc_ref(v_str_2977_);
v___x_2981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2981_, 0, v_str_2977_);
lean_ctor_set(v___x_2981_, 1, v___x_2979_);
lean_ctor_set(v___x_2981_, 2, v___x_2978_);
v___x_2982_ = l_String_Slice_Pos_prev_x3f(v___x_2981_, v___x_2978_);
if (lean_obj_tag(v___x_2982_) == 0)
{
uint32_t v___x_2983_; 
lean_dec_ref_known(v___x_2981_, 3);
v___x_2983_ = 65;
v___y_2971_ = v___x_2980_;
v___y_2972_ = v_str_2977_;
v___y_2973_ = v___x_2983_;
goto v___jp_2970_;
}
else
{
lean_object* v_val_2984_; lean_object* v___x_2985_; 
v_val_2984_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2985_ = l_String_Slice_Pos_get_x3f(v___x_2981_, v_val_2984_);
lean_dec(v_val_2984_);
lean_dec_ref_known(v___x_2981_, 3);
if (lean_obj_tag(v___x_2985_) == 0)
{
uint32_t v___x_2986_; 
v___x_2986_ = 65;
v___y_2971_ = v___x_2980_;
v___y_2972_ = v_str_2977_;
v___y_2973_ = v___x_2986_;
goto v___jp_2970_;
}
else
{
lean_object* v_val_2987_; uint32_t v___x_2988_; 
v_val_2987_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_val_2987_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2988_ = lean_unbox_uint32(v_val_2987_);
lean_dec(v_val_2987_);
v___y_2971_ = v___x_2980_;
v___y_2972_ = v_str_2977_;
v___y_2973_ = v___x_2988_;
goto v___jp_2970_;
}
}
}
else
{
v___y_2967_ = v_str_2977_;
goto v___jp_2966_;
}
}
v___jp_2997_:
{
switch(v_severity_2994_)
{
case 0:
{
lean_dec(v___y_2998_);
lean_dec_ref(v_pos_2992_);
lean_dec_ref(v_fileName_2991_);
lean_dec(v_kind_2990_);
v_str_2977_ = v_str_2999_;
goto v___jp_2976_;
}
case 1:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v_str_3002_; 
v___x_3000_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3001_ = l_Lean_errorNameOfKind_x3f(v_kind_2990_);
lean_dec(v_kind_2990_);
v_str_3002_ = l_Lean_mkErrorStringWithPos(v_fileName_2991_, v_pos_2992_, v_str_2999_, v___y_2998_, v___x_3000_, v___x_3001_);
lean_dec_ref(v_str_2999_);
v_str_2977_ = v_str_3002_;
goto v___jp_2976_;
}
default: 
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_str_3005_; 
v___x_3003_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3004_ = l_Lean_errorNameOfKind_x3f(v_kind_2990_);
lean_dec(v_kind_2990_);
v_str_3005_ = l_Lean_mkErrorStringWithPos(v_fileName_2991_, v_pos_2992_, v_str_2999_, v___y_2998_, v___x_3003_, v___x_3004_);
lean_dec_ref(v_str_2999_);
v_str_2977_ = v_str_3005_;
goto v___jp_2976_;
}
}
}
v___jp_3006_:
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3009_ = lean_string_dec_eq(v_caption_2995_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_str_3012_; 
v___x_3010_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3011_ = lean_string_append(v_caption_2995_, v___x_3010_);
v_str_3012_ = lean_string_append(v___x_3011_, v_data_2996_);
lean_dec(v_data_2996_);
v___y_2998_ = v___y_3007_;
v_str_2999_ = v_str_3012_;
goto v___jp_2997_;
}
else
{
lean_dec_ref(v_caption_2995_);
v___y_2998_ = v___y_3007_;
v_str_2999_ = v_data_2996_;
goto v___jp_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3014_, lean_object* v_includeEndPos_3015_){
_start:
{
uint8_t v_includeEndPos_boxed_3016_; lean_object* v_res_3017_; 
v_includeEndPos_boxed_3016_ = lean_unbox(v_includeEndPos_3015_);
v_res_3017_ = l_Lean_SerialMessage_toString(v_msg_3014_, v_includeEndPos_boxed_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3018_){
_start:
{
uint8_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = 0;
v___x_3020_ = l_Lean_SerialMessage_toString(v_msg_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3023_){
_start:
{
lean_object* v_data_3024_; lean_object* v___x_3025_; 
v_data_3024_ = lean_ctor_get(v_msg_3023_, 4);
v___x_3025_ = l_Lean_MessageData_kind(v_data_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Message_kind(v_msg_3026_);
lean_dec_ref(v_msg_3026_);
return v_res_3027_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3028_){
_start:
{
lean_object* v_data_3029_; uint8_t v___x_3030_; 
v_data_3029_ = lean_ctor_get(v_msg_3028_, 4);
v___x_3030_ = l_Lean_MessageData_isTrace(v_data_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3031_){
_start:
{
uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_res_3032_ = l_Lean_Message_isTrace(v_msg_3031_);
lean_dec_ref(v_msg_3031_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3034_){
_start:
{
lean_object* v_fileName_3036_; lean_object* v_pos_3037_; lean_object* v_endPos_3038_; uint8_t v_keepFullRange_3039_; uint8_t v_severity_3040_; uint8_t v_isSilent_3041_; lean_object* v_caption_3042_; lean_object* v_data_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3053_; 
v_fileName_3036_ = lean_ctor_get(v_msg_3034_, 0);
v_pos_3037_ = lean_ctor_get(v_msg_3034_, 1);
v_endPos_3038_ = lean_ctor_get(v_msg_3034_, 2);
v_keepFullRange_3039_ = lean_ctor_get_uint8(v_msg_3034_, sizeof(void*)*5);
v_severity_3040_ = lean_ctor_get_uint8(v_msg_3034_, sizeof(void*)*5 + 1);
v_isSilent_3041_ = lean_ctor_get_uint8(v_msg_3034_, sizeof(void*)*5 + 2);
v_caption_3042_ = lean_ctor_get(v_msg_3034_, 3);
v_data_3043_ = lean_ctor_get(v_msg_3034_, 4);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_msg_3034_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3045_ = v_msg_3034_;
v_isShared_3046_ = v_isSharedCheck_3053_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_data_3043_);
lean_inc(v_caption_3042_);
lean_inc(v_endPos_3038_);
lean_inc(v_pos_3037_);
lean_inc(v_fileName_3036_);
lean_dec(v_msg_3034_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3053_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_inc(v_data_3043_);
v___x_3047_ = l_Lean_MessageData_toString(v_data_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 4, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_fileName_3036_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_pos_3037_);
lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_endPos_3038_);
lean_ctor_set(v_reuseFailAlloc_3052_, 3, v_caption_3042_);
lean_ctor_set(v_reuseFailAlloc_3052_, 4, v___x_3047_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, sizeof(void*)*5, v_keepFullRange_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, sizeof(void*)*5 + 1, v_severity_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3052_, sizeof(void*)*5 + 2, v_isSilent_3041_);
v___x_3049_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = l_Lean_MessageData_kind(v_data_3043_);
lean_dec(v_data_3043_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Message_serialize(v_msg_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3057_, uint8_t v_includeEndPos_3058_){
_start:
{
lean_object* v_fileName_3060_; lean_object* v_pos_3061_; lean_object* v_endPos_3062_; uint8_t v_severity_3063_; lean_object* v_caption_3064_; lean_object* v_data_3065_; lean_object* v___x_3066_; lean_object* v___y_3068_; uint8_t v___y_3072_; lean_object* v___y_3073_; uint32_t v___y_3074_; lean_object* v_str_3078_; lean_object* v___x_3090_; lean_object* v___y_3092_; lean_object* v_str_3093_; lean_object* v___y_3101_; 
v_fileName_3060_ = lean_ctor_get(v_msg_3057_, 0);
lean_inc_ref(v_fileName_3060_);
v_pos_3061_ = lean_ctor_get(v_msg_3057_, 1);
lean_inc_ref(v_pos_3061_);
v_endPos_3062_ = lean_ctor_get(v_msg_3057_, 2);
lean_inc(v_endPos_3062_);
v_severity_3063_ = lean_ctor_get_uint8(v_msg_3057_, sizeof(void*)*5 + 1);
v_caption_3064_ = lean_ctor_get(v_msg_3057_, 3);
lean_inc_ref(v_caption_3064_);
v_data_3065_ = lean_ctor_get(v_msg_3057_, 4);
lean_inc_n(v_data_3065_, 2);
lean_dec_ref(v_msg_3057_);
v___x_3066_ = l_Lean_MessageData_toString(v_data_3065_);
v___x_3090_ = l_Lean_MessageData_kind(v_data_3065_);
lean_dec(v_data_3065_);
if (v_includeEndPos_3058_ == 0)
{
lean_object* v___x_3107_; 
lean_dec(v_endPos_3062_);
v___x_3107_ = lean_box(0);
v___y_3101_ = v___x_3107_;
goto v___jp_3100_;
}
else
{
v___y_3101_ = v_endPos_3062_;
goto v___jp_3100_;
}
v___jp_3067_:
{
lean_object* v___x_3069_; lean_object* v_str_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3070_ = lean_string_append(v___y_3068_, v___x_3069_);
return v_str_3070_;
}
v___jp_3071_:
{
uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = 10;
v___x_3076_ = lean_uint32_dec_eq(v___y_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
v___y_3068_ = v___y_3073_;
goto v___jp_3067_;
}
else
{
if (v___y_3072_ == 0)
{
return v___y_3073_;
}
else
{
v___y_3068_ = v___y_3073_;
goto v___jp_3067_;
}
}
}
v___jp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = lean_string_utf8_byte_size(v_str_3078_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = lean_nat_dec_eq(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc_ref(v_str_3078_);
v___x_3082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3082_, 0, v_str_3078_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
lean_ctor_set(v___x_3082_, 2, v___x_3079_);
v___x_3083_ = l_String_Slice_Pos_prev_x3f(v___x_3082_, v___x_3079_);
if (lean_obj_tag(v___x_3083_) == 0)
{
uint32_t v___x_3084_; 
lean_dec_ref_known(v___x_3082_, 3);
v___x_3084_ = 65;
v___y_3072_ = v___x_3081_;
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3084_;
goto v___jp_3071_;
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3086_; 
v_val_3085_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_val_3085_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3086_ = l_String_Slice_Pos_get_x3f(v___x_3082_, v_val_3085_);
lean_dec(v_val_3085_);
lean_dec_ref_known(v___x_3082_, 3);
if (lean_obj_tag(v___x_3086_) == 0)
{
uint32_t v___x_3087_; 
v___x_3087_ = 65;
v___y_3072_ = v___x_3081_;
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3087_;
goto v___jp_3071_;
}
else
{
lean_object* v_val_3088_; uint32_t v___x_3089_; 
v_val_3088_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_val_3088_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3089_ = lean_unbox_uint32(v_val_3088_);
lean_dec(v_val_3088_);
v___y_3072_ = v___x_3081_;
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3089_;
goto v___jp_3071_;
}
}
}
else
{
v___y_3068_ = v_str_3078_;
goto v___jp_3067_;
}
}
v___jp_3091_:
{
switch(v_severity_3063_)
{
case 0:
{
lean_dec(v___y_3092_);
lean_dec(v___x_3090_);
lean_dec_ref(v_pos_3061_);
lean_dec_ref(v_fileName_3060_);
v_str_3078_ = v_str_3093_;
goto v___jp_3077_;
}
case 1:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_str_3096_; 
v___x_3094_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3095_ = l_Lean_errorNameOfKind_x3f(v___x_3090_);
lean_dec(v___x_3090_);
v_str_3096_ = l_Lean_mkErrorStringWithPos(v_fileName_3060_, v_pos_3061_, v_str_3093_, v___y_3092_, v___x_3094_, v___x_3095_);
lean_dec_ref(v_str_3093_);
v_str_3078_ = v_str_3096_;
goto v___jp_3077_;
}
default: 
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v_str_3099_; 
v___x_3097_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3098_ = l_Lean_errorNameOfKind_x3f(v___x_3090_);
lean_dec(v___x_3090_);
v_str_3099_ = l_Lean_mkErrorStringWithPos(v_fileName_3060_, v_pos_3061_, v_str_3093_, v___y_3092_, v___x_3097_, v___x_3098_);
lean_dec_ref(v_str_3093_);
v_str_3078_ = v_str_3099_;
goto v___jp_3077_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3103_ = lean_string_dec_eq(v_caption_3064_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_str_3106_; 
v___x_3104_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3105_ = lean_string_append(v_caption_3064_, v___x_3104_);
v_str_3106_ = lean_string_append(v___x_3105_, v___x_3066_);
lean_dec_ref(v___x_3066_);
v___y_3092_ = v___y_3101_;
v_str_3093_ = v_str_3106_;
goto v___jp_3091_;
}
else
{
lean_dec_ref(v_caption_3064_);
v___y_3092_ = v___y_3101_;
v_str_3093_ = v___x_3066_;
goto v___jp_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3108_, lean_object* v_includeEndPos_3109_, lean_object* v_a_3110_){
_start:
{
uint8_t v_includeEndPos_boxed_3111_; lean_object* v_res_3112_; 
v_includeEndPos_boxed_3111_ = lean_unbox(v_includeEndPos_3109_);
v_res_3112_ = l_Lean_Message_toString(v_msg_3108_, v_includeEndPos_boxed_3111_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_3113_){
_start:
{
lean_object* v_fileName_3115_; lean_object* v_pos_3116_; lean_object* v_endPos_3117_; uint8_t v_keepFullRange_3118_; uint8_t v_severity_3119_; uint8_t v_isSilent_3120_; lean_object* v_caption_3121_; lean_object* v_data_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_fileName_3115_ = lean_ctor_get(v_msg_3113_, 0);
lean_inc_ref(v_fileName_3115_);
v_pos_3116_ = lean_ctor_get(v_msg_3113_, 1);
lean_inc_ref(v_pos_3116_);
v_endPos_3117_ = lean_ctor_get(v_msg_3113_, 2);
lean_inc(v_endPos_3117_);
v_keepFullRange_3118_ = lean_ctor_get_uint8(v_msg_3113_, sizeof(void*)*5);
v_severity_3119_ = lean_ctor_get_uint8(v_msg_3113_, sizeof(void*)*5 + 1);
v_isSilent_3120_ = lean_ctor_get_uint8(v_msg_3113_, sizeof(void*)*5 + 2);
v_caption_3121_ = lean_ctor_get(v_msg_3113_, 3);
lean_inc_ref(v_caption_3121_);
v_data_3122_ = lean_ctor_get(v_msg_3113_, 4);
lean_inc_n(v_data_3122_, 2);
lean_dec_ref(v_msg_3113_);
v___x_3123_ = l_Lean_MessageData_toString(v_data_3122_);
v___x_3124_ = l_Lean_MessageData_kind(v_data_3122_);
lean_dec(v_data_3122_);
v___x_3125_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_fileName_3115_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3131_ = l_Lean_instToJsonPosition_toJson(v_pos_3116_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___x_3128_);
v___x_3134_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3135_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3117_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___x_3128_);
v___x_3138_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3139_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3139_, 0, v_keepFullRange_3118_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3128_);
v___x_3142_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3143_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3119_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v___x_3128_);
v___x_3146_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3147_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3147_, 0, v_isSilent_3120_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v___x_3128_);
v___x_3150_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_caption_3121_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3128_);
v___x_3154_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3123_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v___x_3128_);
v___x_3158_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3159_ = 1;
v___x_3160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3124_, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3158_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v___x_3128_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3128_);
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3157_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3153_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3149_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3145_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3141_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3137_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3133_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3129_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3174_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3172_, v___x_3173_);
v___x_3175_ = l_Lean_Json_mkObj(v___x_3174_);
lean_dec(v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Message_toJson(v_msg_3176_);
return v_res_3178_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_unsigned_to_nat(32u);
v___x_3180_ = lean_mk_empty_array_with_capacity(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = ((size_t)5ULL);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_unsigned_to_nat(32u);
v___x_3185_ = lean_mk_empty_array_with_capacity(v___x_3184_);
v___x_3186_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3183_);
lean_ctor_set(v___x_3187_, 3, v___x_3183_);
lean_ctor_set_usize(v___x_3187_, 4, v___x_3182_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = l_Lean_NameSet_empty;
v___x_3189_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
lean_ctor_set(v___x_3190_, 2, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_unsigned_to_nat(32u);
v___x_3194_ = lean_mk_empty_array_with_capacity(v___x_3193_);
lean_dec_ref(v___x_3194_);
v___x_3195_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3196_){
_start:
{
lean_object* v_unreported_3197_; 
v_unreported_3197_ = lean_ctor_get(v_self_3196_, 1);
lean_inc_ref(v_unreported_3197_);
return v_unreported_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_MessageLog_msgs(v_self_3198_);
lean_dec_ref(v_self_3198_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3200_){
_start:
{
lean_object* v_reported_3201_; lean_object* v_unreported_3202_; lean_object* v___x_3203_; 
v_reported_3201_ = lean_ctor_get(v_x_3200_, 0);
lean_inc_ref(v_reported_3201_);
v_unreported_3202_ = lean_ctor_get(v_x_3200_, 1);
lean_inc_ref(v_unreported_3202_);
lean_dec_ref(v_x_3200_);
v___x_3203_ = l_Lean_PersistentArray_append___redArg(v_reported_3201_, v_unreported_3202_);
lean_dec_ref(v_unreported_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3204_){
_start:
{
lean_object* v_unreported_3205_; uint8_t v___x_3206_; 
v_unreported_3205_ = lean_ctor_get(v_log_3204_, 1);
v___x_3206_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3205_);
if (v___x_3206_ == 0)
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
return v___x_3207_;
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_Lean_MessageLog_hasUnreported(v_log_3209_);
lean_dec_ref(v_log_3209_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3212_, lean_object* v_log_3213_){
_start:
{
lean_object* v_reported_3214_; lean_object* v_unreported_3215_; lean_object* v_loggedKinds_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3224_; 
v_reported_3214_ = lean_ctor_get(v_log_3213_, 0);
v_unreported_3215_ = lean_ctor_get(v_log_3213_, 1);
v_loggedKinds_3216_ = lean_ctor_get(v_log_3213_, 2);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_log_3213_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3218_ = v_log_3213_;
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_loggedKinds_3216_);
lean_inc(v_unreported_3215_);
lean_inc(v_reported_3214_);
lean_dec(v_log_3213_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3224_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = l_Lean_PersistentArray_push___redArg(v_unreported_3215_, v_msg_3212_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_reported_3214_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3223_, 2, v_loggedKinds_3216_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3227_, lean_object* v_x_3228_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 0)
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_b_u2082_3227_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3231_, v_x_3232_);
lean_dec(v_x_3232_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3234_, lean_object* v_k_3235_, lean_object* v_t_3236_){
_start:
{
if (lean_obj_tag(v_t_3236_) == 0)
{
lean_object* v_size_3237_; lean_object* v_k_3238_; lean_object* v_v_3239_; lean_object* v_l_3240_; lean_object* v_r_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3256_; 
v_size_3237_ = lean_ctor_get(v_t_3236_, 0);
v_k_3238_ = lean_ctor_get(v_t_3236_, 1);
v_v_3239_ = lean_ctor_get(v_t_3236_, 2);
v_l_3240_ = lean_ctor_get(v_t_3236_, 3);
v_r_3241_ = lean_ctor_get(v_t_3236_, 4);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_t_3236_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3243_ = v_t_3236_;
v_isShared_3244_ = v_isSharedCheck_3256_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_r_3241_);
lean_inc(v_l_3240_);
lean_inc(v_v_3239_);
lean_inc(v_k_3238_);
lean_inc(v_size_3237_);
lean_dec(v_t_3236_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3256_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
uint8_t v___x_3245_; 
v___x_3245_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3235_, v_k_3238_);
switch(v___x_3245_)
{
case 0:
{
lean_object* v_impl_3246_; lean_object* v___x_3247_; 
lean_del_object(v___x_3243_);
lean_dec(v_size_3237_);
v_impl_3246_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3234_, v_k_3235_, v_l_3240_);
v___x_3247_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3238_, v_v_3239_, v_impl_3246_, v_r_3241_);
return v___x_3247_;
}
case 1:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v_val_3250_; lean_object* v___x_3252_; 
lean_dec(v_k_3238_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_v_3239_);
v___x_3249_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3234_, v___x_3248_);
lean_dec_ref_known(v___x_3248_, 1);
v_val_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3250_);
lean_dec(v___x_3249_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 2, v_val_3250_);
lean_ctor_set(v___x_3243_, 1, v_k_3235_);
v___x_3252_ = v___x_3243_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_size_3237_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_val_3250_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v_l_3240_);
lean_ctor_set(v_reuseFailAlloc_3253_, 4, v_r_3241_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
default: 
{
lean_object* v_impl_3254_; lean_object* v___x_3255_; 
lean_del_object(v___x_3243_);
lean_dec(v_size_3237_);
v_impl_3254_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3234_, v_k_3235_, v_r_3241_);
v___x_3255_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3238_, v_v_3239_, v_l_3240_, v_impl_3254_);
return v___x_3255_;
}
}
}
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_val_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3257_ = lean_box(0);
v___x_3258_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3234_, v___x_3257_);
v_val_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3259_);
lean_dec(v___x_3258_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v_k_3235_);
lean_ctor_set(v___x_3261_, 2, v_val_3259_);
lean_ctor_set(v___x_3261_, 3, v_t_3236_);
lean_ctor_set(v___x_3261_, 4, v_t_3236_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3262_, lean_object* v_x_3263_){
_start:
{
if (lean_obj_tag(v_x_3263_) == 0)
{
lean_object* v_k_3264_; lean_object* v_v_3265_; lean_object* v_l_3266_; lean_object* v_r_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_k_3264_ = lean_ctor_get(v_x_3263_, 1);
lean_inc(v_k_3264_);
v_v_3265_ = lean_ctor_get(v_x_3263_, 2);
lean_inc(v_v_3265_);
v_l_3266_ = lean_ctor_get(v_x_3263_, 3);
lean_inc(v_l_3266_);
v_r_3267_ = lean_ctor_get(v_x_3263_, 4);
lean_inc(v_r_3267_);
lean_dec_ref_known(v_x_3263_, 5);
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3262_, v_l_3266_);
v___x_3269_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3265_, v_k_3264_, v___x_3268_);
v_init_3262_ = v___x_3269_;
v_x_3263_ = v_r_3267_;
goto _start;
}
else
{
return v_init_3262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3271_, lean_object* v_l_u2082_3272_){
_start:
{
lean_object* v_reported_3273_; lean_object* v_unreported_3274_; lean_object* v_loggedKinds_3275_; lean_object* v_reported_3276_; lean_object* v_unreported_3277_; lean_object* v_loggedKinds_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3288_; 
v_reported_3273_ = lean_ctor_get(v_l_u2081_3271_, 0);
lean_inc_ref(v_reported_3273_);
v_unreported_3274_ = lean_ctor_get(v_l_u2081_3271_, 1);
lean_inc_ref(v_unreported_3274_);
v_loggedKinds_3275_ = lean_ctor_get(v_l_u2081_3271_, 2);
lean_inc(v_loggedKinds_3275_);
lean_dec_ref(v_l_u2081_3271_);
v_reported_3276_ = lean_ctor_get(v_l_u2082_3272_, 0);
v_unreported_3277_ = lean_ctor_get(v_l_u2082_3272_, 1);
v_loggedKinds_3278_ = lean_ctor_get(v_l_u2082_3272_, 2);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_l_u2082_3272_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3280_ = v_l_u2082_3272_;
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_loggedKinds_3278_);
lean_inc(v_unreported_3277_);
lean_inc(v_reported_3276_);
lean_dec(v_l_u2082_3272_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3282_ = l_Lean_PersistentArray_append___redArg(v_reported_3273_, v_reported_3276_);
lean_dec_ref(v_reported_3276_);
v___x_3283_ = l_Lean_PersistentArray_append___redArg(v_unreported_3274_, v_unreported_3277_);
lean_dec_ref(v_unreported_3277_);
v___x_3284_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3275_, v_loggedKinds_3278_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 2, v___x_3284_);
lean_ctor_set(v___x_3280_, 1, v___x_3283_);
lean_ctor_set(v___x_3280_, 0, v___x_3282_);
v___x_3286_ = v___x_3280_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3289_, lean_object* v_k_3290_, lean_object* v_t_3291_, lean_object* v_hl_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3289_, v_k_3290_, v_t_3291_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3294_, lean_object* v_t_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3294_, v_t_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3299_, size_t v_i_3300_, size_t v_stop_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_usize_dec_eq(v_i_3300_, v_stop_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; uint8_t v_severity_3304_; uint8_t v___x_3305_; 
v___x_3303_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v_severity_3304_ = lean_ctor_get_uint8(v___x_3303_, sizeof(void*)*5 + 1);
v___x_3305_ = 1;
if (v_severity_3304_ == 2)
{
return v___x_3305_;
}
else
{
if (v___x_3302_ == 0)
{
size_t v___x_3306_; size_t v___x_3307_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3300_, v___x_3306_);
v_i_3300_ = v___x_3307_;
goto _start;
}
else
{
return v___x_3305_;
}
}
}
else
{
uint8_t v___x_3309_; 
v___x_3309_ = 0;
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3310_, lean_object* v_i_3311_, lean_object* v_stop_3312_){
_start:
{
size_t v_i_boxed_3313_; size_t v_stop_boxed_3314_; uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_i_boxed_3313_ = lean_unbox_usize(v_i_3311_);
lean_dec(v_i_3311_);
v_stop_boxed_3314_ = lean_unbox_usize(v_stop_3312_);
lean_dec(v_stop_3312_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3310_, v_i_boxed_3313_, v_stop_boxed_3314_);
lean_dec_ref(v_as_3310_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3317_){
_start:
{
if (lean_obj_tag(v_x_3317_) == 0)
{
lean_object* v_cs_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_cs_3318_ = lean_ctor_get(v_x_3317_, 0);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_array_get_size(v_cs_3318_);
v___x_3321_ = lean_nat_dec_lt(v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
return v___x_3321_;
}
else
{
if (v___x_3321_ == 0)
{
return v___x_3321_;
}
else
{
size_t v___x_3322_; size_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___x_3320_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3318_, v___x_3322_, v___x_3323_);
return v___x_3324_;
}
}
}
else
{
lean_object* v_vs_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_vs_3325_ = lean_ctor_get(v_x_3317_, 0);
v___x_3326_ = lean_unsigned_to_nat(0u);
v___x_3327_ = lean_array_get_size(v_vs_3325_);
v___x_3328_ = lean_nat_dec_lt(v___x_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
return v___x_3328_;
}
else
{
if (v___x_3328_ == 0)
{
return v___x_3328_;
}
else
{
size_t v___x_3329_; size_t v___x_3330_; uint8_t v___x_3331_; 
v___x_3329_ = ((size_t)0ULL);
v___x_3330_ = lean_usize_of_nat(v___x_3327_);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3325_, v___x_3329_, v___x_3330_);
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_eq(v_i_3333_, v_stop_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = lean_array_uget_borrowed(v_as_3332_, v_i_3333_);
v___x_3337_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3336_);
if (v___x_3337_ == 0)
{
size_t v___x_3338_; size_t v___x_3339_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3333_, v___x_3338_);
v_i_3333_ = v___x_3339_;
goto _start;
}
else
{
return v___x_3337_;
}
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = 0;
return v___x_3341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3342_, lean_object* v_i_3343_, lean_object* v_stop_3344_){
_start:
{
size_t v_i_boxed_3345_; size_t v_stop_boxed_3346_; uint8_t v_res_3347_; lean_object* v_r_3348_; 
v_i_boxed_3345_ = lean_unbox_usize(v_i_3343_);
lean_dec(v_i_3343_);
v_stop_boxed_3346_ = lean_unbox_usize(v_stop_3344_);
lean_dec(v_stop_3344_);
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3342_, v_i_boxed_3345_, v_stop_boxed_3346_);
lean_dec_ref(v_as_3342_);
v_r_3348_ = lean_box(v_res_3347_);
return v_r_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3349_);
lean_dec_ref(v_x_3349_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3352_){
_start:
{
lean_object* v_root_3353_; lean_object* v_tail_3354_; uint8_t v___x_3355_; 
v_root_3353_ = lean_ctor_get(v_t_3352_, 0);
v_tail_3354_ = lean_ctor_get(v_t_3352_, 1);
v___x_3355_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3353_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = lean_array_get_size(v_tail_3354_);
v___x_3358_ = lean_nat_dec_lt(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
return v___x_3355_;
}
else
{
if (v___x_3358_ == 0)
{
return v___x_3355_;
}
else
{
size_t v___x_3359_; size_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3357_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3354_, v___x_3359_, v___x_3360_);
return v___x_3361_;
}
}
}
else
{
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3362_){
_start:
{
uint8_t v_res_3363_; lean_object* v_r_3364_; 
v_res_3363_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3362_);
lean_dec_ref(v_t_3362_);
v_r_3364_ = lean_box(v_res_3363_);
return v_r_3364_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3365_, lean_object* v_as_3366_, size_t v_i_3367_, size_t v_stop_3368_){
_start:
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_usize_dec_eq(v_i_3367_, v_stop_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; uint8_t v_severity_3371_; uint8_t v___x_3372_; 
v___x_3370_ = lean_array_uget_borrowed(v_as_3366_, v_i_3367_);
v_severity_3371_ = lean_ctor_get_uint8(v___x_3370_, sizeof(void*)*5 + 1);
v___x_3372_ = 1;
if (v_severity_3371_ == 2)
{
return v___x_3372_;
}
else
{
if (v___x_3365_ == 0)
{
size_t v___x_3373_; size_t v___x_3374_; 
v___x_3373_ = ((size_t)1ULL);
v___x_3374_ = lean_usize_add(v_i_3367_, v___x_3373_);
v_i_3367_ = v___x_3374_;
goto _start;
}
else
{
return v___x_3372_;
}
}
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = 0;
return v___x_3376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3377_, lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_){
_start:
{
uint8_t v___x_1884__boxed_3381_; size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; uint8_t v_res_3384_; lean_object* v_r_3385_; 
v___x_1884__boxed_3381_ = lean_unbox(v___x_3377_);
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_3381_, v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_);
lean_dec_ref(v_as_3378_);
v_r_3385_ = lean_box(v_res_3384_);
return v_r_3385_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3386_, lean_object* v_x_3387_){
_start:
{
if (lean_obj_tag(v_x_3387_) == 0)
{
lean_object* v_cs_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_cs_3388_ = lean_ctor_get(v_x_3387_, 0);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_array_get_size(v_cs_3388_);
v___x_3391_ = lean_nat_dec_lt(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
return v___x_3391_;
}
else
{
if (v___x_3391_ == 0)
{
return v___x_3391_;
}
else
{
size_t v___x_3392_; size_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = ((size_t)0ULL);
v___x_3393_ = lean_usize_of_nat(v___x_3390_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3386_, v_cs_3388_, v___x_3392_, v___x_3393_);
return v___x_3394_;
}
}
}
else
{
lean_object* v_vs_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v_vs_3395_ = lean_ctor_get(v_x_3387_, 0);
v___x_3396_ = lean_unsigned_to_nat(0u);
v___x_3397_ = lean_array_get_size(v_vs_3395_);
v___x_3398_ = lean_nat_dec_lt(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
return v___x_3398_;
}
else
{
if (v___x_3398_ == 0)
{
return v___x_3398_;
}
else
{
size_t v___x_3399_; size_t v___x_3400_; uint8_t v___x_3401_; 
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = lean_usize_of_nat(v___x_3397_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3386_, v_vs_3395_, v___x_3399_, v___x_3400_);
return v___x_3401_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3402_, lean_object* v_as_3403_, size_t v_i_3404_, size_t v_stop_3405_){
_start:
{
uint8_t v___x_3406_; 
v___x_3406_ = lean_usize_dec_eq(v_i_3404_, v_stop_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = lean_array_uget_borrowed(v_as_3403_, v_i_3404_);
v___x_3408_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3402_, v___x_3407_);
if (v___x_3408_ == 0)
{
size_t v___x_3409_; size_t v___x_3410_; 
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_add(v_i_3404_, v___x_3409_);
v_i_3404_ = v___x_3410_;
goto _start;
}
else
{
return v___x_3408_;
}
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = 0;
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3413_, lean_object* v_as_3414_, lean_object* v_i_3415_, lean_object* v_stop_3416_){
_start:
{
uint8_t v___x_1901__boxed_3417_; size_t v_i_boxed_3418_; size_t v_stop_boxed_3419_; uint8_t v_res_3420_; lean_object* v_r_3421_; 
v___x_1901__boxed_3417_ = lean_unbox(v___x_3413_);
v_i_boxed_3418_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_stop_boxed_3419_ = lean_unbox_usize(v_stop_3416_);
lean_dec(v_stop_3416_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_3417_, v_as_3414_, v_i_boxed_3418_, v_stop_boxed_3419_);
lean_dec_ref(v_as_3414_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3422_, lean_object* v_x_3423_){
_start:
{
uint8_t v___x_1909__boxed_3424_; uint8_t v_res_3425_; lean_object* v_r_3426_; 
v___x_1909__boxed_3424_ = lean_unbox(v___x_3422_);
v_res_3425_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_3424_, v_x_3423_);
lean_dec_ref(v_x_3423_);
v_r_3426_ = lean_box(v_res_3425_);
return v_r_3426_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3427_, lean_object* v_t_3428_){
_start:
{
lean_object* v_root_3429_; lean_object* v_tail_3430_; uint8_t v___x_3431_; 
v_root_3429_ = lean_ctor_get(v_t_3428_, 0);
v_tail_3430_ = lean_ctor_get(v_t_3428_, 1);
v___x_3431_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3427_, v_root_3429_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_array_get_size(v_tail_3430_);
v___x_3434_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
return v___x_3431_;
}
else
{
if (v___x_3434_ == 0)
{
return v___x_3431_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; uint8_t v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3433_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3427_, v_tail_3430_, v___x_3435_, v___x_3436_);
return v___x_3437_;
}
}
}
else
{
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3438_, lean_object* v_t_3439_){
_start:
{
uint8_t v___x_1952__boxed_3440_; uint8_t v_res_3441_; lean_object* v_r_3442_; 
v___x_1952__boxed_3440_ = lean_unbox(v___x_3438_);
v_res_3441_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_3440_, v_t_3439_);
lean_dec_ref(v_t_3439_);
v_r_3442_ = lean_box(v_res_3441_);
return v_r_3442_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3443_){
_start:
{
lean_object* v_reported_3444_; lean_object* v_unreported_3445_; uint8_t v___x_3446_; 
v_reported_3444_ = lean_ctor_get(v_log_3443_, 0);
v_unreported_3445_ = lean_ctor_get(v_log_3443_, 1);
v___x_3446_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3444_);
if (v___x_3446_ == 0)
{
uint8_t v___x_3447_; 
v___x_3447_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3446_, v_unreported_3445_);
return v___x_3447_;
}
else
{
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3448_){
_start:
{
uint8_t v_res_3449_; lean_object* v_r_3450_; 
v_res_3449_ = l_Lean_MessageLog_hasErrors(v_log_3448_);
lean_dec_ref(v_log_3448_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3451_){
_start:
{
lean_object* v_reported_3452_; lean_object* v_unreported_3453_; lean_object* v_loggedKinds_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3465_; 
v_reported_3452_ = lean_ctor_get(v_log_3451_, 0);
v_unreported_3453_ = lean_ctor_get(v_log_3451_, 1);
v_loggedKinds_3454_ = lean_ctor_get(v_log_3451_, 2);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_log_3451_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3456_ = v_log_3451_;
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_loggedKinds_3454_);
lean_inc(v_unreported_3453_);
lean_inc(v_reported_3452_);
lean_dec(v_log_3451_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3458_ = l_Lean_PersistentArray_append___redArg(v_reported_3452_, v_unreported_3453_);
lean_dec_ref(v_unreported_3453_);
v___x_3459_ = lean_unsigned_to_nat(32u);
v___x_3460_ = lean_mk_empty_array_with_capacity(v___x_3459_);
lean_dec_ref(v___x_3460_);
v___x_3461_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___x_3461_);
lean_ctor_set(v___x_3456_, 0, v___x_3458_);
v___x_3463_ = v___x_3456_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_loggedKinds_3454_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3466_, size_t v_i_3467_, lean_object* v_bs_3468_){
_start:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
if (v___x_3469_ == 0)
{
return v_bs_3468_;
}
else
{
lean_object* v_v_3470_; lean_object* v_fileName_3471_; lean_object* v_pos_3472_; lean_object* v_endPos_3473_; uint8_t v_keepFullRange_3474_; uint8_t v_severity_3475_; uint8_t v_isSilent_3476_; lean_object* v_caption_3477_; lean_object* v_data_3478_; lean_object* v___x_3479_; lean_object* v_bs_x27_3480_; lean_object* v___y_3482_; 
v_v_3470_ = lean_array_uget(v_bs_3468_, v_i_3467_);
v_fileName_3471_ = lean_ctor_get(v_v_3470_, 0);
v_pos_3472_ = lean_ctor_get(v_v_3470_, 1);
v_endPos_3473_ = lean_ctor_get(v_v_3470_, 2);
v_keepFullRange_3474_ = lean_ctor_get_uint8(v_v_3470_, sizeof(void*)*5);
v_severity_3475_ = lean_ctor_get_uint8(v_v_3470_, sizeof(void*)*5 + 1);
v_isSilent_3476_ = lean_ctor_get_uint8(v_v_3470_, sizeof(void*)*5 + 2);
v_caption_3477_ = lean_ctor_get(v_v_3470_, 3);
v_data_3478_ = lean_ctor_get(v_v_3470_, 4);
v___x_3479_ = lean_unsigned_to_nat(0u);
v_bs_x27_3480_ = lean_array_uset(v_bs_3468_, v_i_3467_, v___x_3479_);
if (v_severity_3475_ == 2)
{
lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3494_; 
lean_inc(v_data_3478_);
lean_inc_ref(v_caption_3477_);
lean_inc(v_endPos_3473_);
lean_inc_ref(v_pos_3472_);
lean_inc_ref(v_fileName_3471_);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_v_3470_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; lean_object* v_unused_3496_; lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; 
v_unused_3495_ = lean_ctor_get(v_v_3470_, 4);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_v_3470_, 3);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_v_3470_, 2);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v_v_3470_, 1);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_v_3470_, 0);
lean_dec(v_unused_3499_);
v___x_3488_ = v_v_3470_;
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
else
{
lean_dec(v_v_3470_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
uint8_t v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = 1;
if (v_isShared_3489_ == 0)
{
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_fileName_3471_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_pos_3472_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_endPos_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_caption_3477_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_data_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3493_, sizeof(void*)*5, v_keepFullRange_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3493_, sizeof(void*)*5 + 2, v_isSilent_3476_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*5 + 1, v___x_3490_);
v___y_3482_ = v___x_3492_;
goto v___jp_3481_;
}
}
}
else
{
v___y_3482_ = v_v_3470_;
goto v___jp_3481_;
}
v___jp_3481_:
{
size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = ((size_t)1ULL);
v___x_3484_ = lean_usize_add(v_i_3467_, v___x_3483_);
v___x_3485_ = lean_array_uset(v_bs_x27_3480_, v_i_3467_, v___y_3482_);
v_i_3467_ = v___x_3484_;
v_bs_3468_ = v___x_3485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_bs_3502_){
_start:
{
size_t v_sz_boxed_3503_; size_t v_i_boxed_3504_; lean_object* v_res_3505_; 
v_sz_boxed_3503_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3504_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3503_, v_i_boxed_3504_, v_bs_3502_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3506_, size_t v_i_3507_, lean_object* v_bs_3508_){
_start:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_usize_dec_lt(v_i_3507_, v_sz_3506_);
if (v___x_3509_ == 0)
{
return v_bs_3508_;
}
else
{
lean_object* v_v_3510_; lean_object* v___x_3511_; lean_object* v_bs_x27_3512_; lean_object* v___x_3513_; size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v_v_3510_ = lean_array_uget(v_bs_3508_, v_i_3507_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v_bs_x27_3512_ = lean_array_uset(v_bs_3508_, v_i_3507_, v___x_3511_);
v___x_3513_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3510_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3507_, v___x_3514_);
v___x_3516_ = lean_array_uset(v_bs_x27_3512_, v_i_3507_, v___x_3513_);
v_i_3507_ = v___x_3515_;
v_bs_3508_ = v___x_3516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3518_){
_start:
{
if (lean_obj_tag(v_x_3518_) == 0)
{
lean_object* v_cs_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3529_; 
v_cs_3519_ = lean_ctor_get(v_x_3518_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_x_3518_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3521_ = v_x_3518_;
v_isShared_3522_ = v_isSharedCheck_3529_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_cs_3519_);
lean_dec(v_x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3529_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
size_t v_sz_3523_; size_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v_sz_3523_ = lean_array_size(v_cs_3519_);
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3523_, v___x_3524_, v_cs_3519_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3525_);
v___x_3527_ = v___x_3521_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
else
{
lean_object* v_vs_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3540_; 
v_vs_3530_ = lean_ctor_get(v_x_3518_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_x_3518_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3532_ = v_x_3518_;
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_vs_3530_);
lean_dec(v_x_3518_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
size_t v_sz_3534_; size_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_sz_3534_ = lean_array_size(v_vs_3530_);
v___x_3535_ = ((size_t)0ULL);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3534_, v___x_3535_, v_vs_3530_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3536_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3541_, lean_object* v_i_3542_, lean_object* v_bs_3543_){
_start:
{
size_t v_sz_boxed_3544_; size_t v_i_boxed_3545_; lean_object* v_res_3546_; 
v_sz_boxed_3544_ = lean_unbox_usize(v_sz_3541_);
lean_dec(v_sz_3541_);
v_i_boxed_3545_ = lean_unbox_usize(v_i_3542_);
lean_dec(v_i_3542_);
v_res_3546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3544_, v_i_boxed_3545_, v_bs_3543_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3547_){
_start:
{
lean_object* v_root_3548_; lean_object* v_tail_3549_; lean_object* v_size_3550_; size_t v_shift_3551_; lean_object* v_tailOff_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3563_; 
v_root_3548_ = lean_ctor_get(v_t_3547_, 0);
v_tail_3549_ = lean_ctor_get(v_t_3547_, 1);
v_size_3550_ = lean_ctor_get(v_t_3547_, 2);
v_shift_3551_ = lean_ctor_get_usize(v_t_3547_, 4);
v_tailOff_3552_ = lean_ctor_get(v_t_3547_, 3);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_t_3547_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3554_ = v_t_3547_;
v_isShared_3555_ = v_isSharedCheck_3563_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_tailOff_3552_);
lean_inc(v_size_3550_);
lean_inc(v_tail_3549_);
lean_inc(v_root_3548_);
lean_dec(v_t_3547_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3563_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; size_t v_sz_3557_; size_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3556_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3548_);
v_sz_3557_ = lean_array_size(v_tail_3549_);
v___x_3558_ = ((size_t)0ULL);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3557_, v___x_3558_, v_tail_3549_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v___x_3559_);
lean_ctor_set(v___x_3554_, 0, v___x_3556_);
v___x_3561_ = v___x_3554_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_size_3550_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_tailOff_3552_);
lean_ctor_set_usize(v_reuseFailAlloc_3562_, 4, v_shift_3551_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3564_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v_unreported_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3577_; 
v___x_3565_ = lean_unsigned_to_nat(32u);
v___x_3566_ = lean_mk_empty_array_with_capacity(v___x_3565_);
lean_dec_ref(v___x_3566_);
v___x_3567_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3568_ = lean_ctor_get(v_log_3564_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_log_3564_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; 
v_unused_3578_ = lean_ctor_get(v_log_3564_, 2);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_log_3564_, 0);
lean_dec(v_unused_3579_);
v___x_3570_ = v_log_3564_;
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_unreported_3568_);
lean_dec(v_log_3564_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3568_);
v___x_3573_ = l_Lean_NameSet_empty;
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 2, v___x_3573_);
lean_ctor_set(v___x_3570_, 1, v___x_3572_);
lean_ctor_set(v___x_3570_, 0, v___x_3567_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3580_, size_t v_i_3581_, lean_object* v_bs_3582_){
_start:
{
uint8_t v___x_3583_; 
v___x_3583_ = lean_usize_dec_lt(v_i_3581_, v_sz_3580_);
if (v___x_3583_ == 0)
{
return v_bs_3582_;
}
else
{
lean_object* v_v_3584_; lean_object* v_fileName_3585_; lean_object* v_pos_3586_; lean_object* v_endPos_3587_; uint8_t v_keepFullRange_3588_; uint8_t v_severity_3589_; uint8_t v_isSilent_3590_; lean_object* v_caption_3591_; lean_object* v_data_3592_; lean_object* v___x_3593_; lean_object* v_bs_x27_3594_; lean_object* v___y_3596_; 
v_v_3584_ = lean_array_uget(v_bs_3582_, v_i_3581_);
v_fileName_3585_ = lean_ctor_get(v_v_3584_, 0);
v_pos_3586_ = lean_ctor_get(v_v_3584_, 1);
v_endPos_3587_ = lean_ctor_get(v_v_3584_, 2);
v_keepFullRange_3588_ = lean_ctor_get_uint8(v_v_3584_, sizeof(void*)*5);
v_severity_3589_ = lean_ctor_get_uint8(v_v_3584_, sizeof(void*)*5 + 1);
v_isSilent_3590_ = lean_ctor_get_uint8(v_v_3584_, sizeof(void*)*5 + 2);
v_caption_3591_ = lean_ctor_get(v_v_3584_, 3);
v_data_3592_ = lean_ctor_get(v_v_3584_, 4);
v___x_3593_ = lean_unsigned_to_nat(0u);
v_bs_x27_3594_ = lean_array_uset(v_bs_3582_, v_i_3581_, v___x_3593_);
if (v_severity_3589_ == 2)
{
lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3608_; 
lean_inc(v_data_3592_);
lean_inc_ref(v_caption_3591_);
lean_inc(v_endPos_3587_);
lean_inc_ref(v_pos_3586_);
lean_inc_ref(v_fileName_3585_);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_v_3584_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; lean_object* v_unused_3610_; lean_object* v_unused_3611_; lean_object* v_unused_3612_; lean_object* v_unused_3613_; 
v_unused_3609_ = lean_ctor_get(v_v_3584_, 4);
lean_dec(v_unused_3609_);
v_unused_3610_ = lean_ctor_get(v_v_3584_, 3);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_v_3584_, 2);
lean_dec(v_unused_3611_);
v_unused_3612_ = lean_ctor_get(v_v_3584_, 1);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_v_3584_, 0);
lean_dec(v_unused_3613_);
v___x_3602_ = v_v_3584_;
v_isShared_3603_ = v_isSharedCheck_3608_;
goto v_resetjp_3601_;
}
else
{
lean_dec(v_v_3584_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3608_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
uint8_t v___x_3604_; lean_object* v___x_3606_; 
v___x_3604_ = 0;
if (v_isShared_3603_ == 0)
{
v___x_3606_ = v___x_3602_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_fileName_3585_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_pos_3586_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_endPos_3587_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_caption_3591_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_data_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3607_, sizeof(void*)*5, v_keepFullRange_3588_);
lean_ctor_set_uint8(v_reuseFailAlloc_3607_, sizeof(void*)*5 + 2, v_isSilent_3590_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_ctor_set_uint8(v___x_3606_, sizeof(void*)*5 + 1, v___x_3604_);
v___y_3596_ = v___x_3606_;
goto v___jp_3595_;
}
}
}
else
{
v___y_3596_ = v_v_3584_;
goto v___jp_3595_;
}
v___jp_3595_:
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((size_t)1ULL);
v___x_3598_ = lean_usize_add(v_i_3581_, v___x_3597_);
v___x_3599_ = lean_array_uset(v_bs_x27_3594_, v_i_3581_, v___y_3596_);
v_i_3581_ = v___x_3598_;
v_bs_3582_ = v___x_3599_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3614_, lean_object* v_i_3615_, lean_object* v_bs_3616_){
_start:
{
size_t v_sz_boxed_3617_; size_t v_i_boxed_3618_; lean_object* v_res_3619_; 
v_sz_boxed_3617_ = lean_unbox_usize(v_sz_3614_);
lean_dec(v_sz_3614_);
v_i_boxed_3618_ = lean_unbox_usize(v_i_3615_);
lean_dec(v_i_3615_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3617_, v_i_boxed_3618_, v_bs_3616_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3620_, size_t v_i_3621_, lean_object* v_bs_3622_){
_start:
{
uint8_t v___x_3623_; 
v___x_3623_ = lean_usize_dec_lt(v_i_3621_, v_sz_3620_);
if (v___x_3623_ == 0)
{
return v_bs_3622_;
}
else
{
lean_object* v_v_3624_; lean_object* v___x_3625_; lean_object* v_bs_x27_3626_; lean_object* v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
v_v_3624_ = lean_array_uget(v_bs_3622_, v_i_3621_);
v___x_3625_ = lean_unsigned_to_nat(0u);
v_bs_x27_3626_ = lean_array_uset(v_bs_3622_, v_i_3621_, v___x_3625_);
v___x_3627_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3624_);
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3621_, v___x_3628_);
v___x_3630_ = lean_array_uset(v_bs_x27_3626_, v_i_3621_, v___x_3627_);
v_i_3621_ = v___x_3629_;
v_bs_3622_ = v___x_3630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3632_) == 0)
{
lean_object* v_cs_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3643_; 
v_cs_3633_ = lean_ctor_get(v_x_3632_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_x_3632_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3635_ = v_x_3632_;
v_isShared_3636_ = v_isSharedCheck_3643_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_cs_3633_);
lean_dec(v_x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3643_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
size_t v_sz_3637_; size_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v_sz_3637_ = lean_array_size(v_cs_3633_);
v___x_3638_ = ((size_t)0ULL);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3637_, v___x_3638_, v_cs_3633_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3639_);
v___x_3641_ = v___x_3635_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
else
{
lean_object* v_vs_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3654_; 
v_vs_3644_ = lean_ctor_get(v_x_3632_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_x_3632_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3646_ = v_x_3632_;
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_vs_3644_);
lean_dec(v_x_3632_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
size_t v_sz_3648_; size_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
v_sz_3648_ = lean_array_size(v_vs_3644_);
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3648_, v___x_3649_, v_vs_3644_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3650_);
v___x_3652_ = v___x_3646_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3655_, lean_object* v_i_3656_, lean_object* v_bs_3657_){
_start:
{
size_t v_sz_boxed_3658_; size_t v_i_boxed_3659_; lean_object* v_res_3660_; 
v_sz_boxed_3658_ = lean_unbox_usize(v_sz_3655_);
lean_dec(v_sz_3655_);
v_i_boxed_3659_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3658_, v_i_boxed_3659_, v_bs_3657_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3661_){
_start:
{
lean_object* v_root_3662_; lean_object* v_tail_3663_; lean_object* v_size_3664_; size_t v_shift_3665_; lean_object* v_tailOff_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3677_; 
v_root_3662_ = lean_ctor_get(v_t_3661_, 0);
v_tail_3663_ = lean_ctor_get(v_t_3661_, 1);
v_size_3664_ = lean_ctor_get(v_t_3661_, 2);
v_shift_3665_ = lean_ctor_get_usize(v_t_3661_, 4);
v_tailOff_3666_ = lean_ctor_get(v_t_3661_, 3);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_t_3661_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3668_ = v_t_3661_;
v_isShared_3669_ = v_isSharedCheck_3677_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_tailOff_3666_);
lean_inc(v_size_3664_);
lean_inc(v_tail_3663_);
lean_inc(v_root_3662_);
lean_dec(v_t_3661_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3677_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; size_t v_sz_3671_; size_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3670_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3662_);
v_sz_3671_ = lean_array_size(v_tail_3663_);
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3671_, v___x_3672_, v_tail_3663_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 1, v___x_3673_);
lean_ctor_set(v___x_3668_, 0, v___x_3670_);
v___x_3675_ = v___x_3668_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_size_3664_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_tailOff_3666_);
lean_ctor_set_usize(v_reuseFailAlloc_3676_, 4, v_shift_3665_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3678_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_unreported_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3691_; 
v___x_3679_ = lean_unsigned_to_nat(32u);
v___x_3680_ = lean_mk_empty_array_with_capacity(v___x_3679_);
lean_dec_ref(v___x_3680_);
v___x_3681_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3682_ = lean_ctor_get(v_log_3678_, 1);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_log_3678_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3692_ = lean_ctor_get(v_log_3678_, 2);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_log_3678_, 0);
lean_dec(v_unused_3693_);
v___x_3684_ = v_log_3678_;
v_isShared_3685_ = v_isSharedCheck_3691_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_unreported_3682_);
lean_dec(v_log_3678_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3691_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3686_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3682_);
v___x_3687_ = l_Lean_NameSet_empty;
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 2, v___x_3687_);
lean_ctor_set(v___x_3684_, 1, v___x_3686_);
lean_ctor_set(v___x_3684_, 0, v___x_3681_);
v___x_3689_ = v___x_3684_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3694_, size_t v_i_3695_, size_t v_stop_3696_, lean_object* v_b_3697_){
_start:
{
lean_object* v___y_3699_; uint8_t v___x_3703_; 
v___x_3703_ = lean_usize_dec_eq(v_i_3695_, v_stop_3696_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; uint8_t v_severity_3705_; 
v___x_3704_ = lean_array_uget_borrowed(v_as_3694_, v_i_3695_);
v_severity_3705_ = lean_ctor_get_uint8(v___x_3704_, sizeof(void*)*5 + 1);
if (v_severity_3705_ == 0)
{
lean_object* v___x_3706_; 
lean_inc(v___x_3704_);
v___x_3706_ = l_Lean_PersistentArray_push___redArg(v_b_3697_, v___x_3704_);
v___y_3699_ = v___x_3706_;
goto v___jp_3698_;
}
else
{
v___y_3699_ = v_b_3697_;
goto v___jp_3698_;
}
}
else
{
return v_b_3697_;
}
v___jp_3698_:
{
size_t v___x_3700_; size_t v___x_3701_; 
v___x_3700_ = ((size_t)1ULL);
v___x_3701_ = lean_usize_add(v_i_3695_, v___x_3700_);
v_i_3695_ = v___x_3701_;
v_b_3697_ = v___y_3699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3707_, lean_object* v_i_3708_, lean_object* v_stop_3709_, lean_object* v_b_3710_){
_start:
{
size_t v_i_boxed_3711_; size_t v_stop_boxed_3712_; lean_object* v_res_3713_; 
v_i_boxed_3711_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_stop_boxed_3712_ = lean_unbox_usize(v_stop_3709_);
lean_dec(v_stop_3709_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3707_, v_i_boxed_3711_, v_stop_boxed_3712_, v_b_3710_);
lean_dec_ref(v_as_3707_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3714_, lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3714_) == 0)
{
lean_object* v_cs_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_cs_3716_ = lean_ctor_get(v_x_3714_, 0);
v___x_3717_ = lean_unsigned_to_nat(0u);
v___x_3718_ = lean_array_get_size(v_cs_3716_);
v___x_3719_ = lean_nat_dec_lt(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
return v_x_3715_;
}
else
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_nat_dec_le(v___x_3718_, v___x_3718_);
if (v___x_3720_ == 0)
{
if (v___x_3719_ == 0)
{
return v_x_3715_;
}
else
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = ((size_t)0ULL);
v___x_3722_ = lean_usize_of_nat(v___x_3718_);
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3716_, v___x_3721_, v___x_3722_, v_x_3715_);
return v___x_3723_;
}
}
else
{
size_t v___x_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = ((size_t)0ULL);
v___x_3725_ = lean_usize_of_nat(v___x_3718_);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3716_, v___x_3724_, v___x_3725_, v_x_3715_);
return v___x_3726_;
}
}
}
else
{
lean_object* v_vs_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v_vs_3727_ = lean_ctor_get(v_x_3714_, 0);
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = lean_array_get_size(v_vs_3727_);
v___x_3730_ = lean_nat_dec_lt(v___x_3728_, v___x_3729_);
if (v___x_3730_ == 0)
{
return v_x_3715_;
}
else
{
uint8_t v___x_3731_; 
v___x_3731_ = lean_nat_dec_le(v___x_3729_, v___x_3729_);
if (v___x_3731_ == 0)
{
if (v___x_3730_ == 0)
{
return v_x_3715_;
}
else
{
size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = lean_usize_of_nat(v___x_3729_);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3727_, v___x_3732_, v___x_3733_, v_x_3715_);
return v___x_3734_;
}
}
else
{
size_t v___x_3735_; size_t v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = ((size_t)0ULL);
v___x_3736_ = lean_usize_of_nat(v___x_3729_);
v___x_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3727_, v___x_3735_, v___x_3736_, v_x_3715_);
return v___x_3737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3738_, size_t v_i_3739_, size_t v_stop_3740_, lean_object* v_b_3741_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_usize_dec_eq(v_i_3739_, v_stop_3740_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; lean_object* v___x_3744_; size_t v___x_3745_; size_t v___x_3746_; 
v___x_3743_ = lean_array_uget_borrowed(v_as_3738_, v_i_3739_);
v___x_3744_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3743_, v_b_3741_);
v___x_3745_ = ((size_t)1ULL);
v___x_3746_ = lean_usize_add(v_i_3739_, v___x_3745_);
v_i_3739_ = v___x_3746_;
v_b_3741_ = v___x_3744_;
goto _start;
}
else
{
return v_b_3741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3748_, lean_object* v_i_3749_, lean_object* v_stop_3750_, lean_object* v_b_3751_){
_start:
{
size_t v_i_boxed_3752_; size_t v_stop_boxed_3753_; lean_object* v_res_3754_; 
v_i_boxed_3752_ = lean_unbox_usize(v_i_3749_);
lean_dec(v_i_3749_);
v_stop_boxed_3753_ = lean_unbox_usize(v_stop_3750_);
lean_dec(v_stop_3750_);
v_res_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3748_, v_i_boxed_3752_, v_stop_boxed_3753_, v_b_3751_);
lean_dec_ref(v_as_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3755_, lean_object* v_x_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3755_, v_x_3756_);
lean_dec_ref(v_x_3755_);
return v_res_3757_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3759_, size_t v_x_3760_, size_t v_x_3761_, lean_object* v_x_3762_){
_start:
{
if (lean_obj_tag(v_x_3759_) == 0)
{
lean_object* v_cs_3763_; lean_object* v___x_3764_; size_t v___x_3765_; lean_object* v_j_3766_; lean_object* v___x_3767_; size_t v___x_3768_; size_t v___x_3769_; size_t v___x_3770_; size_t v___x_3771_; size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_cs_3763_ = lean_ctor_get(v_x_3759_, 0);
v___x_3764_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3765_ = lean_usize_shift_right(v_x_3760_, v_x_3761_);
v_j_3766_ = lean_usize_to_nat(v___x_3765_);
v___x_3767_ = lean_array_get_borrowed(v___x_3764_, v_cs_3763_, v_j_3766_);
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = lean_usize_shift_left(v___x_3768_, v_x_3761_);
v___x_3770_ = lean_usize_sub(v___x_3769_, v___x_3768_);
v___x_3771_ = lean_usize_land(v_x_3760_, v___x_3770_);
v___x_3772_ = ((size_t)5ULL);
v___x_3773_ = lean_usize_sub(v_x_3761_, v___x_3772_);
v___x_3774_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3767_, v___x_3771_, v___x_3773_, v_x_3762_);
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_add(v_j_3766_, v___x_3775_);
lean_dec(v_j_3766_);
v___x_3777_ = lean_array_get_size(v_cs_3763_);
v___x_3778_ = lean_nat_dec_lt(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_dec(v___x_3776_);
return v___x_3774_;
}
else
{
uint8_t v___x_3779_; 
v___x_3779_ = lean_nat_dec_le(v___x_3777_, v___x_3777_);
if (v___x_3779_ == 0)
{
if (v___x_3778_ == 0)
{
lean_dec(v___x_3776_);
return v___x_3774_;
}
else
{
size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v___x_3780_ = lean_usize_of_nat(v___x_3776_);
lean_dec(v___x_3776_);
v___x_3781_ = lean_usize_of_nat(v___x_3777_);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3763_, v___x_3780_, v___x_3781_, v___x_3774_);
return v___x_3782_;
}
}
else
{
size_t v___x_3783_; size_t v___x_3784_; lean_object* v___x_3785_; 
v___x_3783_ = lean_usize_of_nat(v___x_3776_);
lean_dec(v___x_3776_);
v___x_3784_ = lean_usize_of_nat(v___x_3777_);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3763_, v___x_3783_, v___x_3784_, v___x_3774_);
return v___x_3785_;
}
}
}
else
{
lean_object* v_vs_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_vs_3786_ = lean_ctor_get(v_x_3759_, 0);
v___x_3787_ = lean_usize_to_nat(v_x_3760_);
v___x_3788_ = lean_array_get_size(v_vs_3786_);
v___x_3789_ = lean_nat_dec_lt(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_dec(v___x_3787_);
return v_x_3762_;
}
else
{
uint8_t v___x_3790_; 
v___x_3790_ = lean_nat_dec_le(v___x_3788_, v___x_3788_);
if (v___x_3790_ == 0)
{
if (v___x_3789_ == 0)
{
lean_dec(v___x_3787_);
return v_x_3762_;
}
else
{
size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_usize_of_nat(v___x_3787_);
lean_dec(v___x_3787_);
v___x_3792_ = lean_usize_of_nat(v___x_3788_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3786_, v___x_3791_, v___x_3792_, v_x_3762_);
return v___x_3793_;
}
}
else
{
size_t v___x_3794_; size_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_usize_of_nat(v___x_3787_);
lean_dec(v___x_3787_);
v___x_3795_ = lean_usize_of_nat(v___x_3788_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3786_, v___x_3794_, v___x_3795_, v_x_3762_);
return v___x_3796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3797_, lean_object* v_x_3798_, lean_object* v_x_3799_, lean_object* v_x_3800_){
_start:
{
size_t v_x_1528__boxed_3801_; size_t v_x_1529__boxed_3802_; lean_object* v_res_3803_; 
v_x_1528__boxed_3801_ = lean_unbox_usize(v_x_3798_);
lean_dec(v_x_3798_);
v_x_1529__boxed_3802_ = lean_unbox_usize(v_x_3799_);
lean_dec(v_x_3799_);
v_res_3803_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3797_, v_x_1528__boxed_3801_, v_x_1529__boxed_3802_, v_x_3800_);
lean_dec_ref(v_x_3797_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3804_, lean_object* v_init_3805_, lean_object* v_start_3806_){
_start:
{
lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3807_ = lean_unsigned_to_nat(0u);
v___x_3808_ = lean_nat_dec_eq(v_start_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v_root_3809_; lean_object* v_tail_3810_; size_t v_shift_3811_; lean_object* v_tailOff_3812_; uint8_t v___x_3813_; 
v_root_3809_ = lean_ctor_get(v_t_3804_, 0);
v_tail_3810_ = lean_ctor_get(v_t_3804_, 1);
v_shift_3811_ = lean_ctor_get_usize(v_t_3804_, 4);
v_tailOff_3812_ = lean_ctor_get(v_t_3804_, 3);
v___x_3813_ = lean_nat_dec_le(v_tailOff_3812_, v_start_3806_);
if (v___x_3813_ == 0)
{
size_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v___x_3814_ = lean_usize_of_nat(v_start_3806_);
v___x_3815_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3809_, v___x_3814_, v_shift_3811_, v_init_3805_);
v___x_3816_ = lean_array_get_size(v_tail_3810_);
v___x_3817_ = lean_nat_dec_lt(v___x_3807_, v___x_3816_);
if (v___x_3817_ == 0)
{
return v___x_3815_;
}
else
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_nat_dec_le(v___x_3816_, v___x_3816_);
if (v___x_3818_ == 0)
{
if (v___x_3817_ == 0)
{
return v___x_3815_;
}
else
{
size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = lean_usize_of_nat(v___x_3816_);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3810_, v___x_3819_, v___x_3820_, v___x_3815_);
return v___x_3821_;
}
}
else
{
size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = lean_usize_of_nat(v___x_3816_);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3810_, v___x_3822_, v___x_3823_, v___x_3815_);
return v___x_3824_;
}
}
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3825_ = lean_nat_sub(v_start_3806_, v_tailOff_3812_);
v___x_3826_ = lean_array_get_size(v_tail_3810_);
v___x_3827_ = lean_nat_dec_lt(v___x_3825_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_dec(v___x_3825_);
return v_init_3805_;
}
else
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_le(v___x_3826_, v___x_3826_);
if (v___x_3828_ == 0)
{
if (v___x_3827_ == 0)
{
lean_dec(v___x_3825_);
return v_init_3805_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_usize_of_nat(v___x_3825_);
lean_dec(v___x_3825_);
v___x_3830_ = lean_usize_of_nat(v___x_3826_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3810_, v___x_3829_, v___x_3830_, v_init_3805_);
return v___x_3831_;
}
}
else
{
size_t v___x_3832_; size_t v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = lean_usize_of_nat(v___x_3825_);
lean_dec(v___x_3825_);
v___x_3833_ = lean_usize_of_nat(v___x_3826_);
v___x_3834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3810_, v___x_3832_, v___x_3833_, v_init_3805_);
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_root_3835_; lean_object* v_tail_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_root_3835_ = lean_ctor_get(v_t_3804_, 0);
v_tail_3836_ = lean_ctor_get(v_t_3804_, 1);
v___x_3837_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3835_, v_init_3805_);
v___x_3838_ = lean_array_get_size(v_tail_3836_);
v___x_3839_ = lean_nat_dec_lt(v___x_3807_, v___x_3838_);
if (v___x_3839_ == 0)
{
return v___x_3837_;
}
else
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_nat_dec_le(v___x_3838_, v___x_3838_);
if (v___x_3840_ == 0)
{
if (v___x_3839_ == 0)
{
return v___x_3837_;
}
else
{
size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = ((size_t)0ULL);
v___x_3842_ = lean_usize_of_nat(v___x_3838_);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3836_, v___x_3841_, v___x_3842_, v___x_3837_);
return v___x_3843_;
}
}
else
{
size_t v___x_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = lean_usize_of_nat(v___x_3838_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3836_, v___x_3844_, v___x_3845_, v___x_3837_);
return v___x_3846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3847_, lean_object* v_init_3848_, lean_object* v_start_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3847_, v_init_3848_, v_start_3849_);
lean_dec(v_start_3849_);
lean_dec_ref(v_t_3847_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3851_){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v_unreported_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3865_; 
v___x_3852_ = lean_unsigned_to_nat(32u);
v___x_3853_ = lean_mk_empty_array_with_capacity(v___x_3852_);
lean_dec_ref(v___x_3853_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3856_ = lean_ctor_get(v_log_3851_, 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_log_3851_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; lean_object* v_unused_3867_; 
v_unused_3866_ = lean_ctor_get(v_log_3851_, 2);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_log_3851_, 0);
lean_dec(v_unused_3867_);
v___x_3858_ = v_log_3851_;
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_unreported_3856_);
lean_dec(v_log_3851_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3860_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3856_, v___x_3855_, v___x_3854_);
lean_dec_ref(v_unreported_3856_);
v___x_3861_ = l_Lean_NameSet_empty;
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 2, v___x_3861_);
lean_ctor_set(v___x_3858_, 1, v___x_3860_);
lean_ctor_set(v___x_3858_, 0, v___x_3855_);
v___x_3863_ = v___x_3858_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v___x_3861_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3868_, size_t v_i_3869_, size_t v_stop_3870_, lean_object* v_b_3871_){
_start:
{
lean_object* v___y_3873_; uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_eq(v_i_3869_, v_stop_3870_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; uint8_t v_severity_3879_; 
v___x_3878_ = lean_array_uget_borrowed(v_as_3868_, v_i_3869_);
v_severity_3879_ = lean_ctor_get_uint8(v___x_3878_, sizeof(void*)*5 + 1);
if (v_severity_3879_ == 1)
{
lean_object* v___x_3880_; 
lean_inc(v___x_3878_);
v___x_3880_ = l_Lean_PersistentArray_push___redArg(v_b_3871_, v___x_3878_);
v___y_3873_ = v___x_3880_;
goto v___jp_3872_;
}
else
{
v___y_3873_ = v_b_3871_;
goto v___jp_3872_;
}
}
else
{
return v_b_3871_;
}
v___jp_3872_:
{
size_t v___x_3874_; size_t v___x_3875_; 
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3869_, v___x_3874_);
v_i_3869_ = v___x_3875_;
v_b_3871_ = v___y_3873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3881_, lean_object* v_i_3882_, lean_object* v_stop_3883_, lean_object* v_b_3884_){
_start:
{
size_t v_i_boxed_3885_; size_t v_stop_boxed_3886_; lean_object* v_res_3887_; 
v_i_boxed_3885_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_stop_boxed_3886_ = lean_unbox_usize(v_stop_3883_);
lean_dec(v_stop_3883_);
v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3881_, v_i_boxed_3885_, v_stop_boxed_3886_, v_b_3884_);
lean_dec_ref(v_as_3881_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 0)
{
lean_object* v_cs_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_cs_3890_ = lean_ctor_get(v_x_3888_, 0);
v___x_3891_ = lean_unsigned_to_nat(0u);
v___x_3892_ = lean_array_get_size(v_cs_3890_);
v___x_3893_ = lean_nat_dec_lt(v___x_3891_, v___x_3892_);
if (v___x_3893_ == 0)
{
return v_x_3889_;
}
else
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_nat_dec_le(v___x_3892_, v___x_3892_);
if (v___x_3894_ == 0)
{
if (v___x_3893_ == 0)
{
return v_x_3889_;
}
else
{
size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = ((size_t)0ULL);
v___x_3896_ = lean_usize_of_nat(v___x_3892_);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3890_, v___x_3895_, v___x_3896_, v_x_3889_);
return v___x_3897_;
}
}
else
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((size_t)0ULL);
v___x_3899_ = lean_usize_of_nat(v___x_3892_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3890_, v___x_3898_, v___x_3899_, v_x_3889_);
return v___x_3900_;
}
}
}
else
{
lean_object* v_vs_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_vs_3901_ = lean_ctor_get(v_x_3888_, 0);
v___x_3902_ = lean_unsigned_to_nat(0u);
v___x_3903_ = lean_array_get_size(v_vs_3901_);
v___x_3904_ = lean_nat_dec_lt(v___x_3902_, v___x_3903_);
if (v___x_3904_ == 0)
{
return v_x_3889_;
}
else
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_nat_dec_le(v___x_3903_, v___x_3903_);
if (v___x_3905_ == 0)
{
if (v___x_3904_ == 0)
{
return v_x_3889_;
}
else
{
size_t v___x_3906_; size_t v___x_3907_; lean_object* v___x_3908_; 
v___x_3906_ = ((size_t)0ULL);
v___x_3907_ = lean_usize_of_nat(v___x_3903_);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3901_, v___x_3906_, v___x_3907_, v_x_3889_);
return v___x_3908_;
}
}
else
{
size_t v___x_3909_; size_t v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = ((size_t)0ULL);
v___x_3910_ = lean_usize_of_nat(v___x_3903_);
v___x_3911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3901_, v___x_3909_, v___x_3910_, v_x_3889_);
return v___x_3911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3912_, size_t v_i_3913_, size_t v_stop_3914_, lean_object* v_b_3915_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_usize_dec_eq(v_i_3913_, v_stop_3914_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; 
v___x_3917_ = lean_array_uget_borrowed(v_as_3912_, v_i_3913_);
v___x_3918_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3917_, v_b_3915_);
v___x_3919_ = ((size_t)1ULL);
v___x_3920_ = lean_usize_add(v_i_3913_, v___x_3919_);
v_i_3913_ = v___x_3920_;
v_b_3915_ = v___x_3918_;
goto _start;
}
else
{
return v_b_3915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3922_, lean_object* v_i_3923_, lean_object* v_stop_3924_, lean_object* v_b_3925_){
_start:
{
size_t v_i_boxed_3926_; size_t v_stop_boxed_3927_; lean_object* v_res_3928_; 
v_i_boxed_3926_ = lean_unbox_usize(v_i_3923_);
lean_dec(v_i_3923_);
v_stop_boxed_3927_ = lean_unbox_usize(v_stop_3924_);
lean_dec(v_stop_3924_);
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3922_, v_i_boxed_3926_, v_stop_boxed_3927_, v_b_3925_);
lean_dec_ref(v_as_3922_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3929_, v_x_3930_);
lean_dec_ref(v_x_3929_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3932_, size_t v_x_3933_, size_t v_x_3934_, lean_object* v_x_3935_){
_start:
{
if (lean_obj_tag(v_x_3932_) == 0)
{
lean_object* v_cs_3936_; lean_object* v___x_3937_; size_t v___x_3938_; lean_object* v_j_3939_; lean_object* v___x_3940_; size_t v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v_cs_3936_ = lean_ctor_get(v_x_3932_, 0);
v___x_3937_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3938_ = lean_usize_shift_right(v_x_3933_, v_x_3934_);
v_j_3939_ = lean_usize_to_nat(v___x_3938_);
v___x_3940_ = lean_array_get_borrowed(v___x_3937_, v_cs_3936_, v_j_3939_);
v___x_3941_ = ((size_t)1ULL);
v___x_3942_ = lean_usize_shift_left(v___x_3941_, v_x_3934_);
v___x_3943_ = lean_usize_sub(v___x_3942_, v___x_3941_);
v___x_3944_ = lean_usize_land(v_x_3933_, v___x_3943_);
v___x_3945_ = ((size_t)5ULL);
v___x_3946_ = lean_usize_sub(v_x_3934_, v___x_3945_);
v___x_3947_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3940_, v___x_3944_, v___x_3946_, v_x_3935_);
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_nat_add(v_j_3939_, v___x_3948_);
lean_dec(v_j_3939_);
v___x_3950_ = lean_array_get_size(v_cs_3936_);
v___x_3951_ = lean_nat_dec_lt(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_dec(v___x_3949_);
return v___x_3947_;
}
else
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_nat_dec_le(v___x_3950_, v___x_3950_);
if (v___x_3952_ == 0)
{
if (v___x_3951_ == 0)
{
lean_dec(v___x_3949_);
return v___x_3947_;
}
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_usize_of_nat(v___x_3949_);
lean_dec(v___x_3949_);
v___x_3954_ = lean_usize_of_nat(v___x_3950_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3936_, v___x_3953_, v___x_3954_, v___x_3947_);
return v___x_3955_;
}
}
else
{
size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_usize_of_nat(v___x_3949_);
lean_dec(v___x_3949_);
v___x_3957_ = lean_usize_of_nat(v___x_3950_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3936_, v___x_3956_, v___x_3957_, v___x_3947_);
return v___x_3958_;
}
}
}
else
{
lean_object* v_vs_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_vs_3959_ = lean_ctor_get(v_x_3932_, 0);
v___x_3960_ = lean_usize_to_nat(v_x_3933_);
v___x_3961_ = lean_array_get_size(v_vs_3959_);
v___x_3962_ = lean_nat_dec_lt(v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_dec(v___x_3960_);
return v_x_3935_;
}
else
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_le(v___x_3961_, v___x_3961_);
if (v___x_3963_ == 0)
{
if (v___x_3962_ == 0)
{
lean_dec(v___x_3960_);
return v_x_3935_;
}
else
{
size_t v___x_3964_; size_t v___x_3965_; lean_object* v___x_3966_; 
v___x_3964_ = lean_usize_of_nat(v___x_3960_);
lean_dec(v___x_3960_);
v___x_3965_ = lean_usize_of_nat(v___x_3961_);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3959_, v___x_3964_, v___x_3965_, v_x_3935_);
return v___x_3966_;
}
}
else
{
size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_usize_of_nat(v___x_3960_);
lean_dec(v___x_3960_);
v___x_3968_ = lean_usize_of_nat(v___x_3961_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3959_, v___x_3967_, v___x_3968_, v_x_3935_);
return v___x_3969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_, lean_object* v_x_3973_){
_start:
{
size_t v_x_1527__boxed_3974_; size_t v_x_1528__boxed_3975_; lean_object* v_res_3976_; 
v_x_1527__boxed_3974_ = lean_unbox_usize(v_x_3971_);
lean_dec(v_x_3971_);
v_x_1528__boxed_3975_ = lean_unbox_usize(v_x_3972_);
lean_dec(v_x_3972_);
v_res_3976_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3970_, v_x_1527__boxed_3974_, v_x_1528__boxed_3975_, v_x_3973_);
lean_dec_ref(v_x_3970_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3977_, lean_object* v_init_3978_, lean_object* v_start_3979_){
_start:
{
lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = lean_nat_dec_eq(v_start_3979_, v___x_3980_);
if (v___x_3981_ == 0)
{
lean_object* v_root_3982_; lean_object* v_tail_3983_; size_t v_shift_3984_; lean_object* v_tailOff_3985_; uint8_t v___x_3986_; 
v_root_3982_ = lean_ctor_get(v_t_3977_, 0);
v_tail_3983_ = lean_ctor_get(v_t_3977_, 1);
v_shift_3984_ = lean_ctor_get_usize(v_t_3977_, 4);
v_tailOff_3985_ = lean_ctor_get(v_t_3977_, 3);
v___x_3986_ = lean_nat_dec_le(v_tailOff_3985_, v_start_3979_);
if (v___x_3986_ == 0)
{
size_t v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3987_ = lean_usize_of_nat(v_start_3979_);
v___x_3988_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3982_, v___x_3987_, v_shift_3984_, v_init_3978_);
v___x_3989_ = lean_array_get_size(v_tail_3983_);
v___x_3990_ = lean_nat_dec_lt(v___x_3980_, v___x_3989_);
if (v___x_3990_ == 0)
{
return v___x_3988_;
}
else
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_nat_dec_le(v___x_3989_, v___x_3989_);
if (v___x_3991_ == 0)
{
if (v___x_3990_ == 0)
{
return v___x_3988_;
}
else
{
size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = lean_usize_of_nat(v___x_3989_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3983_, v___x_3992_, v___x_3993_, v___x_3988_);
return v___x_3994_;
}
}
else
{
size_t v___x_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = lean_usize_of_nat(v___x_3989_);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3983_, v___x_3995_, v___x_3996_, v___x_3988_);
return v___x_3997_;
}
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3998_ = lean_nat_sub(v_start_3979_, v_tailOff_3985_);
v___x_3999_ = lean_array_get_size(v_tail_3983_);
v___x_4000_ = lean_nat_dec_lt(v___x_3998_, v___x_3999_);
if (v___x_4000_ == 0)
{
lean_dec(v___x_3998_);
return v_init_3978_;
}
else
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_nat_dec_le(v___x_3999_, v___x_3999_);
if (v___x_4001_ == 0)
{
if (v___x_4000_ == 0)
{
lean_dec(v___x_3998_);
return v_init_3978_;
}
else
{
size_t v___x_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = lean_usize_of_nat(v___x_3998_);
lean_dec(v___x_3998_);
v___x_4003_ = lean_usize_of_nat(v___x_3999_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3983_, v___x_4002_, v___x_4003_, v_init_3978_);
return v___x_4004_;
}
}
else
{
size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_usize_of_nat(v___x_3998_);
lean_dec(v___x_3998_);
v___x_4006_ = lean_usize_of_nat(v___x_3999_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3983_, v___x_4005_, v___x_4006_, v_init_3978_);
return v___x_4007_;
}
}
}
}
else
{
lean_object* v_root_4008_; lean_object* v_tail_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; 
v_root_4008_ = lean_ctor_get(v_t_3977_, 0);
v_tail_4009_ = lean_ctor_get(v_t_3977_, 1);
v___x_4010_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_4008_, v_init_3978_);
v___x_4011_ = lean_array_get_size(v_tail_4009_);
v___x_4012_ = lean_nat_dec_lt(v___x_3980_, v___x_4011_);
if (v___x_4012_ == 0)
{
return v___x_4010_;
}
else
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_nat_dec_le(v___x_4011_, v___x_4011_);
if (v___x_4013_ == 0)
{
if (v___x_4012_ == 0)
{
return v___x_4010_;
}
else
{
size_t v___x_4014_; size_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4014_ = ((size_t)0ULL);
v___x_4015_ = lean_usize_of_nat(v___x_4011_);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4009_, v___x_4014_, v___x_4015_, v___x_4010_);
return v___x_4016_;
}
}
else
{
size_t v___x_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = ((size_t)0ULL);
v___x_4018_ = lean_usize_of_nat(v___x_4011_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4009_, v___x_4017_, v___x_4018_, v___x_4010_);
return v___x_4019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_4020_, lean_object* v_init_4021_, lean_object* v_start_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_4020_, v_init_4021_, v_start_4022_);
lean_dec(v_start_4022_);
lean_dec_ref(v_t_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_4024_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_unreported_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4038_; 
v___x_4025_ = lean_unsigned_to_nat(32u);
v___x_4026_ = lean_mk_empty_array_with_capacity(v___x_4025_);
lean_dec_ref(v___x_4026_);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_4029_ = lean_ctor_get(v_log_4024_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_log_4024_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; lean_object* v_unused_4040_; 
v_unused_4039_ = lean_ctor_get(v_log_4024_, 2);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_log_4024_, 0);
lean_dec(v_unused_4040_);
v___x_4031_ = v_log_4024_;
v_isShared_4032_ = v_isSharedCheck_4038_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_unreported_4029_);
lean_dec(v_log_4024_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4038_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4033_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_4029_, v___x_4028_, v___x_4027_);
lean_dec_ref(v_unreported_4029_);
v___x_4034_ = l_Lean_NameSet_empty;
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 2, v___x_4034_);
lean_ctor_set(v___x_4031_, 1, v___x_4033_);
lean_ctor_set(v___x_4031_, 0, v___x_4028_);
v___x_4036_ = v___x_4031_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4037_, 2, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_4041_, lean_object* v_log_4042_, lean_object* v_f_4043_){
_start:
{
lean_object* v_unreported_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_unreported_4044_ = lean_ctor_get(v_log_4042_, 1);
lean_inc_ref(v_unreported_4044_);
lean_dec_ref(v_log_4042_);
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = l_Lean_PersistentArray_forM___redArg(v_inst_4041_, v_unreported_4044_, v_f_4043_, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_4047_, lean_object* v_inst_4048_, lean_object* v_log_4049_, lean_object* v_f_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_MessageLog_forM___redArg(v_inst_4048_, v_log_4049_, v_f_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_4052_){
_start:
{
lean_object* v_unreported_4053_; lean_object* v___x_4054_; 
v_unreported_4053_ = lean_ctor_get(v_log_4052_, 1);
v___x_4054_ = l_Lean_PersistentArray_toList___redArg(v_unreported_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_MessageLog_toList(v_log_4055_);
lean_dec_ref(v_log_4055_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4057_){
_start:
{
lean_object* v_unreported_4058_; lean_object* v___x_4059_; 
v_unreported_4058_ = lean_ctor_get(v_log_4057_, 1);
v___x_4059_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_MessageLog_toArray(v_log_4060_);
lean_dec_ref(v_log_4060_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_unsigned_to_nat(2u);
v___x_4064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v_msg_4062_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4065_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
lean_ctor_set(v___x_4067_, 1, v_msg_4065_);
v___x_4068_ = l_Lean_MessageData_nestD(v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4069_){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = l_Lean_MessageData_ofExpr(v_e_4069_);
v___x_4071_ = l_Lean_indentD(v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4072_, lean_object* v_msg_4073_){
_start:
{
lean_object* v_env_4075_; lean_object* v_mctx_4076_; lean_object* v_lctx_4077_; lean_object* v_opts_4078_; lean_object* v_currNamespace_4079_; lean_object* v_openDecls_4080_; lean_object* v___x_4081_; lean_object* v_msg_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_env_4075_ = lean_ctor_get(v_ctx_4072_, 0);
v_mctx_4076_ = lean_ctor_get(v_ctx_4072_, 1);
v_lctx_4077_ = lean_ctor_get(v_ctx_4072_, 2);
v_opts_4078_ = lean_ctor_get(v_ctx_4072_, 3);
v_currNamespace_4079_ = lean_ctor_get(v_ctx_4072_, 4);
v_openDecls_4080_ = lean_ctor_get(v_ctx_4072_, 5);
lean_inc(v_openDecls_4080_);
lean_inc(v_currNamespace_4079_);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v_currNamespace_4079_);
lean_ctor_set(v___x_4081_, 1, v_openDecls_4080_);
v_msg_4082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4082_, 0, v___x_4081_);
lean_ctor_set(v_msg_4082_, 1, v_msg_4073_);
lean_inc_ref(v_opts_4078_);
lean_inc_ref(v_lctx_4077_);
lean_inc_ref(v_mctx_4076_);
lean_inc_ref(v_env_4075_);
v___x_4083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4083_, 0, v_env_4075_);
lean_ctor_set(v___x_4083_, 1, v_mctx_4076_);
lean_ctor_set(v___x_4083_, 2, v_lctx_4077_);
lean_ctor_set(v___x_4083_, 3, v_opts_4078_);
v___x_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
v___x_4085_ = l_Lean_MessageData_format(v_msg_4082_, v___x_4084_);
v___x_4086_ = l_Std_Format_defWidth;
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = l_Std_Format_pretty(v___x_4085_, v___x_4086_, v___x_4087_, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4089_, lean_object* v_msg_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4089_, v_msg_4090_);
lean_dec_ref(v_ctx_4089_);
return v_res_4092_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4093_, lean_object* v_a_4094_, uint8_t v_b_4095_){
_start:
{
lean_object* v_str_4096_; lean_object* v_startInclusive_4097_; lean_object* v_endExclusive_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
v_str_4096_ = lean_ctor_get(v_s_4093_, 0);
v_startInclusive_4097_ = lean_ctor_get(v_s_4093_, 1);
v_endExclusive_4098_ = lean_ctor_get(v_s_4093_, 2);
v___x_4099_ = lean_nat_sub(v_endExclusive_4098_, v_startInclusive_4097_);
v___x_4100_ = lean_nat_dec_eq(v_a_4094_, v___x_4099_);
lean_dec(v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; uint32_t v___x_4102_; uint32_t v___x_4103_; uint8_t v___x_4104_; 
v___x_4101_ = lean_nat_add(v_startInclusive_4097_, v_a_4094_);
lean_dec(v_a_4094_);
v___x_4102_ = lean_string_utf8_get_fast(v_str_4096_, v___x_4101_);
v___x_4103_ = 10;
v___x_4104_ = lean_uint32_dec_eq(v___x_4102_, v___x_4103_);
if (v___x_4104_ == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_string_utf8_next_fast(v_str_4096_, v___x_4101_);
lean_dec(v___x_4101_);
v___x_4106_ = lean_nat_sub(v___x_4105_, v_startInclusive_4097_);
v_a_4094_ = v___x_4106_;
v_b_4095_ = v___x_4104_;
goto _start;
}
else
{
lean_dec(v___x_4101_);
return v___x_4104_;
}
}
else
{
lean_dec(v_a_4094_);
return v_b_4095_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4108_, lean_object* v_a_4109_, lean_object* v_b_4110_){
_start:
{
uint8_t v_b_boxed_4111_; uint8_t v_res_4112_; lean_object* v_r_4113_; 
v_b_boxed_4111_ = lean_unbox(v_b_4110_);
v_res_4112_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4108_, v_a_4109_, v_b_boxed_4111_);
lean_dec_ref(v_s_4108_);
v_r_4113_ = lean_box(v_res_4112_);
return v_r_4113_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4114_){
_start:
{
lean_object* v_searcher_4115_; uint8_t v___x_4116_; uint8_t v___x_4117_; 
v_searcher_4115_ = lean_unsigned_to_nat(0u);
v___x_4116_ = 0;
v___x_4117_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4114_, v_searcher_4115_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4118_){
_start:
{
uint8_t v_res_4119_; lean_object* v_r_4120_; 
v_res_4119_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4118_);
lean_dec_ref(v_s_4118_);
v_r_4120_ = lean_box(v_res_4119_);
return v_r_4120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4121_, lean_object* v_val_4122_, lean_object* v_a_4123_, lean_object* v_b_4124_){
_start:
{
lean_object* v_startInclusive_4125_; lean_object* v_endExclusive_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v_startInclusive_4125_ = lean_ctor_get(v___x_4121_, 1);
v_endExclusive_4126_ = lean_ctor_get(v___x_4121_, 2);
v___x_4127_ = lean_nat_sub(v_endExclusive_4126_, v_startInclusive_4125_);
v___x_4128_ = lean_nat_dec_eq(v_a_4123_, v___x_4127_);
lean_dec(v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = lean_string_utf8_next_fast(v_val_4122_, v_a_4123_);
lean_dec(v_a_4123_);
v___x_4130_ = lean_unsigned_to_nat(1u);
v___x_4131_ = lean_nat_add(v_b_4124_, v___x_4130_);
lean_dec(v_b_4124_);
v_a_4123_ = v___x_4129_;
v_b_4124_ = v___x_4131_;
goto _start;
}
else
{
lean_dec(v_a_4123_);
return v_b_4124_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4133_, lean_object* v_val_4134_, lean_object* v_a_4135_, lean_object* v_b_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4133_, v_val_4134_, v_a_4135_, v_b_4136_);
lean_dec_ref(v_val_4134_);
lean_dec_ref(v___x_4133_);
return v_res_4137_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_4142_ = l_Lean_MessageData_ofFormat(v___x_4141_);
return v___x_4142_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_4147_ = l_Lean_MessageData_ofFormat(v___x_4146_);
return v___x_4147_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4149_ = l_Lean_MessageData_ofFormat(v___x_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4150_, lean_object* v_maxInlineLength_4151_, lean_object* v_ctx_4152_){
_start:
{
lean_object* v_msg_4154_; lean_object* v___x_4155_; uint8_t v___y_4157_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v_msg_4154_ = l_Lean_MessageData_ofExpr(v_e_4150_);
lean_inc_ref(v_msg_4154_);
v___x_4155_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4152_, v_msg_4154_);
v___x_4165_ = lean_unsigned_to_nat(0u);
v___x_4166_ = lean_string_utf8_byte_size(v___x_4155_);
lean_inc_ref(v___x_4155_);
v___x_4167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4155_);
lean_ctor_set(v___x_4167_, 1, v___x_4165_);
lean_ctor_set(v___x_4167_, 2, v___x_4166_);
v___x_4168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4167_, v___x_4155_, v___x_4165_, v___x_4165_);
lean_dec_ref(v___x_4155_);
v___x_4169_ = lean_nat_dec_lt(v_maxInlineLength_4151_, v___x_4168_);
lean_dec(v___x_4168_);
if (v___x_4169_ == 0)
{
uint8_t v___x_4170_; 
v___x_4170_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4167_);
lean_dec_ref_known(v___x_4167_, 3);
v___y_4157_ = v___x_4170_;
goto v___jp_4156_;
}
else
{
lean_dec_ref_known(v___x_4167_, 3);
v___y_4157_ = v___x_4169_;
goto v___jp_4156_;
}
v___jp_4156_:
{
if (v___y_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4158_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v_msg_4154_);
v___x_4160_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4162_ = l_Lean_indentD(v_msg_4154_);
v___x_4163_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
return v___x_4164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4171_, lean_object* v_maxInlineLength_4172_, lean_object* v_ctx_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_inlineExpr___lam__0(v_e_4171_, v_maxInlineLength_4172_, v_ctx_4173_);
lean_dec_ref(v_ctx_4173_);
lean_dec(v_maxInlineLength_4172_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4176_, lean_object* v_x_4177_){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4179_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4180_ = l_Lean_MessageData_ofExpr(v_e_4176_);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4184_, lean_object* v_x_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_inlineExpr___lam__2(v_e_4184_, v_x_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4188_, lean_object* v_maxInlineLength_4189_){
_start:
{
lean_object* v___f_4190_; lean_object* v___f_4191_; lean_object* v___f_4192_; lean_object* v___x_4193_; 
lean_inc_ref_n(v_e_4188_, 2);
v___f_4190_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4190_, 0, v_e_4188_);
lean_closure_set(v___f_4190_, 1, v_maxInlineLength_4189_);
v___f_4191_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4191_, 0, v_e_4188_);
v___f_4192_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4192_, 0, v_e_4188_);
v___x_4193_ = l_Lean_MessageData_lazy(v___f_4190_, v___f_4191_, v___f_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4194_, lean_object* v_val_4195_, lean_object* v_inst_4196_, lean_object* v_R_4197_, lean_object* v_a_4198_, lean_object* v_b_4199_, lean_object* v_c_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4194_, v_val_4195_, v_a_4198_, v_b_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4202_, lean_object* v_val_4203_, lean_object* v_inst_4204_, lean_object* v_R_4205_, lean_object* v_a_4206_, lean_object* v_b_4207_, lean_object* v_c_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4202_, v_val_4203_, v_inst_4204_, v_R_4205_, v_a_4206_, v_b_4207_, v_c_4208_);
lean_dec_ref(v_val_4203_);
lean_dec_ref(v___x_4202_);
return v_res_4209_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4210_, lean_object* v_inst_4211_, lean_object* v_R_4212_, lean_object* v_a_4213_, uint8_t v_b_4214_, lean_object* v_c_4215_){
_start:
{
uint8_t v___x_4216_; 
v___x_4216_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4210_, v_a_4213_, v_b_4214_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4217_, lean_object* v_inst_4218_, lean_object* v_R_4219_, lean_object* v_a_4220_, lean_object* v_b_4221_, lean_object* v_c_4222_){
_start:
{
uint8_t v_b_boxed_4223_; uint8_t v_res_4224_; lean_object* v_r_4225_; 
v_b_boxed_4223_ = lean_unbox(v_b_4221_);
v_res_4224_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4217_, v_inst_4218_, v_R_4219_, v_a_4220_, v_b_boxed_4223_, v_c_4222_);
lean_dec_ref(v_s_4217_);
v_r_4225_ = lean_box(v_res_4224_);
return v_r_4225_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4230_ = l_Lean_MessageData_ofFormat(v___x_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4231_, lean_object* v_maxInlineLength_4232_, lean_object* v_ctx_4233_){
_start:
{
lean_object* v_msg_4235_; lean_object* v___x_4236_; uint8_t v___y_4238_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v_msg_4235_ = l_Lean_MessageData_ofExpr(v_e_4231_);
lean_inc_ref(v_msg_4235_);
v___x_4236_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4233_, v_msg_4235_);
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = lean_string_utf8_byte_size(v___x_4236_);
lean_inc_ref(v___x_4236_);
v___x_4246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4236_);
lean_ctor_set(v___x_4246_, 1, v___x_4244_);
lean_ctor_set(v___x_4246_, 2, v___x_4245_);
v___x_4247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4246_, v___x_4236_, v___x_4244_, v___x_4244_);
lean_dec_ref(v___x_4236_);
v___x_4248_ = lean_nat_dec_lt(v_maxInlineLength_4232_, v___x_4247_);
lean_dec(v___x_4247_);
if (v___x_4248_ == 0)
{
uint8_t v___x_4249_; 
v___x_4249_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4246_);
lean_dec_ref_known(v___x_4246_, 3);
v___y_4238_ = v___x_4249_;
goto v___jp_4237_;
}
else
{
lean_dec_ref_known(v___x_4246_, 3);
v___y_4238_ = v___x_4248_;
goto v___jp_4237_;
}
v___jp_4237_:
{
if (v___y_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4239_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
lean_ctor_set(v___x_4240_, 1, v_msg_4235_);
v___x_4241_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_indentD(v_msg_4235_);
return v___x_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4250_, lean_object* v_maxInlineLength_4251_, lean_object* v_ctx_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_inlineExprTrailing___lam__0(v_e_4250_, v_maxInlineLength_4251_, v_ctx_4252_);
lean_dec_ref(v_ctx_4252_);
lean_dec(v_maxInlineLength_4251_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4255_, lean_object* v_x_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4258_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4259_ = l_Lean_MessageData_ofExpr(v_e_4255_);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_inlineExprTrailing___lam__2(v_e_4263_, v_x_4264_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4267_, lean_object* v_maxInlineLength_4268_){
_start:
{
lean_object* v___f_4269_; lean_object* v___f_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; 
lean_inc_ref_n(v_e_4267_, 2);
v___f_4269_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4269_, 0, v_e_4267_);
lean_closure_set(v___f_4269_, 1, v_maxInlineLength_4268_);
v___f_4270_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4270_, 0, v_e_4267_);
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4271_, 0, v_e_4267_);
v___x_4272_ = l_Lean_MessageData_lazy(v___f_4269_, v___f_4270_, v___f_4271_);
return v___x_4272_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4277_ = l_Lean_MessageData_ofFormat(v___x_4276_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4282_ = l_Lean_MessageData_ofFormat(v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4283_){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4284_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
lean_ctor_set(v___x_4285_, 1, v_msg_4283_);
v___x_4286_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4288_, lean_object* v_inst_4289_, lean_object* v_msg_4290_){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_apply_1(v_inst_4288_, v_msg_4290_);
v___x_4292_ = lean_apply_2(v_inst_4289_, lean_box(0), v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4293_, lean_object* v_inst_4294_){
_start:
{
lean_object* v___f_4295_; 
v___f_4295_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4295_, 0, v_inst_4294_);
lean_closure_set(v___f_4295_, 1, v_inst_4293_);
return v___f_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4296_, lean_object* v_n_4297_, lean_object* v_inst_4298_, lean_object* v_inst_4299_){
_start:
{
lean_object* v___f_4300_; 
v___f_4300_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4300_, 0, v_inst_4299_);
lean_closure_set(v___f_4300_, 1, v_inst_4298_);
return v___f_4300_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4301_ = lean_unsigned_to_nat(32u);
v___x_4302_ = lean_mk_empty_array_with_capacity(v___x_4301_);
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
return v___x_4303_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4304_ = ((size_t)5ULL);
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = lean_unsigned_to_nat(32u);
v___x_4307_ = lean_mk_empty_array_with_capacity(v___x_4306_);
v___x_4308_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___x_4307_);
lean_ctor_set(v___x_4309_, 2, v___x_4305_);
lean_ctor_set(v___x_4309_, 3, v___x_4305_);
lean_ctor_set_usize(v___x_4309_, 4, v___x_4304_);
return v___x_4309_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4310_ = lean_box(1);
v___x_4311_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4312_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
lean_ctor_set(v___x_4313_, 1, v___x_4311_);
lean_ctor_set(v___x_4313_, 2, v___x_4310_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4314_, lean_object* v_msgData_4315_, lean_object* v_toPure_4316_, lean_object* v_opts_4317_){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4318_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4319_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4320_, 0, v_env_4314_);
lean_ctor_set(v___x_4320_, 1, v___x_4318_);
lean_ctor_set(v___x_4320_, 2, v___x_4319_);
lean_ctor_set(v___x_4320_, 3, v_opts_4317_);
v___x_4321_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
lean_ctor_set(v___x_4321_, 1, v_msgData_4315_);
v___x_4322_ = lean_apply_2(v_toPure_4316_, lean_box(0), v___x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4323_, lean_object* v_toPure_4324_, lean_object* v_toBind_4325_, lean_object* v_inst_4326_, lean_object* v_env_4327_){
_start:
{
lean_object* v___f_4328_; lean_object* v___x_4329_; 
v___f_4328_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4328_, 0, v_env_4327_);
lean_closure_set(v___f_4328_, 1, v_msgData_4323_);
lean_closure_set(v___f_4328_, 2, v_toPure_4324_);
v___x_4329_ = lean_apply_4(v_toBind_4325_, lean_box(0), lean_box(0), v_inst_4326_, v___f_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4330_, lean_object* v_inst_4331_, lean_object* v_inst_4332_, lean_object* v_msgData_4333_){
_start:
{
lean_object* v_toApplicative_4334_; lean_object* v_toBind_4335_; lean_object* v_getEnv_4336_; lean_object* v_toPure_4337_; lean_object* v___f_4338_; lean_object* v___x_4339_; 
v_toApplicative_4334_ = lean_ctor_get(v_inst_4330_, 0);
lean_inc_ref(v_toApplicative_4334_);
v_toBind_4335_ = lean_ctor_get(v_inst_4330_, 1);
lean_inc_n(v_toBind_4335_, 2);
lean_dec_ref(v_inst_4330_);
v_getEnv_4336_ = lean_ctor_get(v_inst_4331_, 0);
lean_inc(v_getEnv_4336_);
lean_dec_ref(v_inst_4331_);
v_toPure_4337_ = lean_ctor_get(v_toApplicative_4334_, 1);
lean_inc(v_toPure_4337_);
lean_dec_ref(v_toApplicative_4334_);
v___f_4338_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4338_, 0, v_msgData_4333_);
lean_closure_set(v___f_4338_, 1, v_toPure_4337_);
lean_closure_set(v___f_4338_, 2, v_toBind_4335_);
lean_closure_set(v___f_4338_, 3, v_inst_4332_);
v___x_4339_ = lean_apply_4(v_toBind_4335_, lean_box(0), lean_box(0), v_getEnv_4336_, v___f_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4340_, lean_object* v_inst_4341_, lean_object* v_inst_4342_, lean_object* v_inst_4343_, lean_object* v_msgData_4344_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_addMessageContextPartial___redArg(v_inst_4341_, v_inst_4342_, v_inst_4343_, v_msgData_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4346_, lean_object* v_mctx_4347_, lean_object* v_lctx_4348_, lean_object* v_msgData_4349_, lean_object* v_toPure_4350_, lean_object* v_opts_4351_){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4352_, 0, v_env_4346_);
lean_ctor_set(v___x_4352_, 1, v_mctx_4347_);
lean_ctor_set(v___x_4352_, 2, v_lctx_4348_);
lean_ctor_set(v___x_4352_, 3, v_opts_4351_);
v___x_4353_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
lean_ctor_set(v___x_4353_, 1, v_msgData_4349_);
v___x_4354_ = lean_apply_2(v_toPure_4350_, lean_box(0), v___x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4355_, lean_object* v_mctx_4356_, lean_object* v_msgData_4357_, lean_object* v_toPure_4358_, lean_object* v_toBind_4359_, lean_object* v_inst_4360_, lean_object* v_lctx_4361_){
_start:
{
lean_object* v___f_4362_; lean_object* v___x_4363_; 
v___f_4362_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4362_, 0, v_env_4355_);
lean_closure_set(v___f_4362_, 1, v_mctx_4356_);
lean_closure_set(v___f_4362_, 2, v_lctx_4361_);
lean_closure_set(v___f_4362_, 3, v_msgData_4357_);
lean_closure_set(v___f_4362_, 4, v_toPure_4358_);
v___x_4363_ = lean_apply_4(v_toBind_4359_, lean_box(0), lean_box(0), v_inst_4360_, v___f_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4364_, lean_object* v_msgData_4365_, lean_object* v_toPure_4366_, lean_object* v_toBind_4367_, lean_object* v_inst_4368_, lean_object* v_inst_4369_, lean_object* v_mctx_4370_){
_start:
{
lean_object* v___f_4371_; lean_object* v___x_4372_; 
lean_inc(v_toBind_4367_);
v___f_4371_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4371_, 0, v_env_4364_);
lean_closure_set(v___f_4371_, 1, v_mctx_4370_);
lean_closure_set(v___f_4371_, 2, v_msgData_4365_);
lean_closure_set(v___f_4371_, 3, v_toPure_4366_);
lean_closure_set(v___f_4371_, 4, v_toBind_4367_);
lean_closure_set(v___f_4371_, 5, v_inst_4368_);
v___x_4372_ = lean_apply_4(v_toBind_4367_, lean_box(0), lean_box(0), v_inst_4369_, v___f_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4373_, lean_object* v_msgData_4374_, lean_object* v_toPure_4375_, lean_object* v_toBind_4376_, lean_object* v_inst_4377_, lean_object* v_inst_4378_, lean_object* v_env_4379_){
_start:
{
lean_object* v_getMCtx_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; 
v_getMCtx_4380_ = lean_ctor_get(v_inst_4373_, 0);
lean_inc(v_getMCtx_4380_);
lean_dec_ref(v_inst_4373_);
lean_inc(v_toBind_4376_);
v___f_4381_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4381_, 0, v_env_4379_);
lean_closure_set(v___f_4381_, 1, v_msgData_4374_);
lean_closure_set(v___f_4381_, 2, v_toPure_4375_);
lean_closure_set(v___f_4381_, 3, v_toBind_4376_);
lean_closure_set(v___f_4381_, 4, v_inst_4377_);
lean_closure_set(v___f_4381_, 5, v_inst_4378_);
v___x_4382_ = lean_apply_4(v_toBind_4376_, lean_box(0), lean_box(0), v_getMCtx_4380_, v___f_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4383_, lean_object* v_inst_4384_, lean_object* v_inst_4385_, lean_object* v_inst_4386_, lean_object* v_inst_4387_, lean_object* v_msgData_4388_){
_start:
{
lean_object* v_toApplicative_4389_; lean_object* v_toBind_4390_; lean_object* v_getEnv_4391_; lean_object* v_toPure_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; 
v_toApplicative_4389_ = lean_ctor_get(v_inst_4383_, 0);
lean_inc_ref(v_toApplicative_4389_);
v_toBind_4390_ = lean_ctor_get(v_inst_4383_, 1);
lean_inc_n(v_toBind_4390_, 2);
lean_dec_ref(v_inst_4383_);
v_getEnv_4391_ = lean_ctor_get(v_inst_4384_, 0);
lean_inc(v_getEnv_4391_);
lean_dec_ref(v_inst_4384_);
v_toPure_4392_ = lean_ctor_get(v_toApplicative_4389_, 1);
lean_inc(v_toPure_4392_);
lean_dec_ref(v_toApplicative_4389_);
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4393_, 0, v_inst_4385_);
lean_closure_set(v___f_4393_, 1, v_msgData_4388_);
lean_closure_set(v___f_4393_, 2, v_toPure_4392_);
lean_closure_set(v___f_4393_, 3, v_toBind_4390_);
lean_closure_set(v___f_4393_, 4, v_inst_4387_);
lean_closure_set(v___f_4393_, 5, v_inst_4386_);
v___x_4394_ = lean_apply_4(v_toBind_4390_, lean_box(0), lean_box(0), v_getEnv_4391_, v___f_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4395_, lean_object* v_inst_4396_, lean_object* v_inst_4397_, lean_object* v_inst_4398_, lean_object* v_inst_4399_, lean_object* v_inst_4400_, lean_object* v_msgData_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_addMessageContextFull___redArg(v_inst_4396_, v_inst_4397_, v_inst_4398_, v_inst_4399_, v_inst_4400_, v_msgData_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4405_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4407_);
lean_dec_ref(v_s_4407_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4409_, lean_object* v___x_4410_, lean_object* v___x_4411_, lean_object* v_a_4412_, lean_object* v_b_4413_){
_start:
{
lean_object* v_it_4415_; lean_object* v_startInclusive_4416_; lean_object* v_endExclusive_4417_; 
if (lean_obj_tag(v_a_4412_) == 0)
{
lean_object* v_currPos_4423_; lean_object* v_searcher_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4450_; 
v_currPos_4423_ = lean_ctor_get(v_a_4412_, 0);
v_searcher_4424_ = lean_ctor_get(v_a_4412_, 1);
v_isSharedCheck_4450_ = !lean_is_exclusive(v_a_4412_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4426_ = v_a_4412_;
v_isShared_4427_ = v_isSharedCheck_4450_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_searcher_4424_);
lean_inc(v_currPos_4423_);
lean_dec(v_a_4412_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4450_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v_startInclusive_4428_; lean_object* v_endExclusive_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; 
v_startInclusive_4428_ = lean_ctor_get(v___x_4410_, 1);
v_endExclusive_4429_ = lean_ctor_get(v___x_4410_, 2);
v___x_4430_ = lean_nat_sub(v_endExclusive_4429_, v_startInclusive_4428_);
v___x_4431_ = lean_nat_dec_eq(v_searcher_4424_, v___x_4430_);
lean_dec(v___x_4430_);
if (v___x_4431_ == 0)
{
uint32_t v___x_4432_; uint32_t v___x_4433_; uint8_t v___x_4434_; 
v___x_4432_ = 10;
v___x_4433_ = lean_string_utf8_get_fast(v_str_4409_, v_searcher_4424_);
v___x_4434_ = lean_uint32_dec_eq(v___x_4433_, v___x_4432_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = lean_string_utf8_next_fast(v_str_4409_, v_searcher_4424_);
lean_dec(v_searcher_4424_);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 1, v___x_4435_);
v___x_4437_ = v___x_4426_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_currPos_4423_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
v_a_4412_ = v___x_4437_;
goto _start;
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v_slice_4443_; lean_object* v_nextIt_4445_; 
v___x_4440_ = lean_string_utf8_next_fast(v_str_4409_, v_searcher_4424_);
v___x_4441_ = lean_nat_sub(v___x_4440_, v_searcher_4424_);
v___x_4442_ = lean_nat_add(v_searcher_4424_, v___x_4441_);
lean_dec(v___x_4441_);
v_slice_4443_ = l_String_Slice_subslice_x21(v___x_4410_, v_currPos_4423_, v_searcher_4424_);
lean_inc(v___x_4442_);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 1, v___x_4442_);
lean_ctor_set(v___x_4426_, 0, v___x_4442_);
v_nextIt_4445_ = v___x_4426_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4442_);
v_nextIt_4445_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v_startInclusive_4446_; lean_object* v_endExclusive_4447_; 
v_startInclusive_4446_ = lean_ctor_get(v_slice_4443_, 0);
lean_inc(v_startInclusive_4446_);
v_endExclusive_4447_ = lean_ctor_get(v_slice_4443_, 1);
lean_inc(v_endExclusive_4447_);
lean_dec_ref(v_slice_4443_);
v_it_4415_ = v_nextIt_4445_;
v_startInclusive_4416_ = v_startInclusive_4446_;
v_endExclusive_4417_ = v_endExclusive_4447_;
goto v___jp_4414_;
}
}
}
else
{
lean_object* v___x_4449_; 
lean_del_object(v___x_4426_);
lean_dec(v_searcher_4424_);
v___x_4449_ = lean_box(1);
lean_inc(v___x_4411_);
v_it_4415_ = v___x_4449_;
v_startInclusive_4416_ = v_currPos_4423_;
v_endExclusive_4417_ = v___x_4411_;
goto v___jp_4414_;
}
}
}
else
{
lean_dec(v___x_4411_);
return v_b_4413_;
}
v___jp_4414_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4418_ = lean_string_utf8_extract_fast(v_str_4409_, v_startInclusive_4416_, v_endExclusive_4417_);
lean_dec(v_endExclusive_4417_);
lean_dec(v_startInclusive_4416_);
v___x_4419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
v___x_4420_ = l_Lean_MessageData_ofFormat(v___x_4419_);
v___x_4421_ = lean_array_push(v_b_4413_, v___x_4420_);
v_a_4412_ = v_it_4415_;
v_b_4413_ = v___x_4421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4451_, lean_object* v___x_4452_, lean_object* v___x_4453_, lean_object* v_a_4454_, lean_object* v_b_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4451_, v___x_4452_, v___x_4453_, v_a_4454_, v_b_4455_);
lean_dec_ref(v___x_4452_);
lean_dec_ref(v_str_4451_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4459_){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v_lines_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4460_ = lean_unsigned_to_nat(0u);
v___x_4461_ = lean_string_utf8_byte_size(v_str_4459_);
lean_inc_ref(v_str_4459_);
v___x_4462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4462_, 0, v_str_4459_);
lean_ctor_set(v___x_4462_, 1, v___x_4460_);
lean_ctor_set(v___x_4462_, 2, v___x_4461_);
v_lines_4463_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4462_);
v___x_4464_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4465_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4459_, v___x_4462_, v___x_4461_, v_lines_4463_, v___x_4464_);
lean_dec_ref_known(v___x_4462_, 3);
lean_dec_ref(v_str_4459_);
v___x_4466_ = lean_array_to_list(v___x_4465_);
v___x_4467_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4468_ = l_Lean_MessageData_joinSep(v___x_4466_, v___x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4469_, lean_object* v___x_4470_, lean_object* v___x_4471_, lean_object* v_inst_4472_, lean_object* v_R_4473_, lean_object* v_a_4474_, lean_object* v_b_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4469_, v___x_4470_, v___x_4471_, v_a_4474_, v_b_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4477_, lean_object* v___x_4478_, lean_object* v___x_4479_, lean_object* v_inst_4480_, lean_object* v_R_4481_, lean_object* v_a_4482_, lean_object* v_b_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4477_, v___x_4478_, v___x_4479_, v_inst_4480_, v_R_4481_, v_a_4482_, v_b_4483_);
lean_dec_ref(v___x_4478_);
lean_dec_ref(v_str_4477_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4485_){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4487_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4487_, 0, lean_box(0));
lean_closure_set(v___x_4487_, 1, lean_box(0));
lean_closure_set(v___x_4487_, 2, lean_box(0));
lean_closure_set(v___x_4487_, 3, v___x_4486_);
lean_closure_set(v___x_4487_, 4, v_inst_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4488_, lean_object* v_inst_4489_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4497_){
_start:
{
lean_object* v___f_4498_; 
v___f_4498_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_instToMessageDataTSyntax(v_k_4499_);
lean_dec(v_k_4499_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4505_, lean_object* v_as_4506_){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_box(0);
v___x_4508_ = l_List_mapTR_loop___redArg(v_inst_4505_, v_as_4506_, v___x_4507_);
v___x_4509_ = l_Lean_MessageData_ofList(v___x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4510_){
_start:
{
lean_object* v___f_4511_; 
v___f_4511_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4511_, 0, v_inst_4510_);
return v___f_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4512_, lean_object* v_inst_4513_){
_start:
{
lean_object* v___f_4514_; 
v___f_4514_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4514_, 0, v_inst_4513_);
return v___f_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4515_, lean_object* v_as_4516_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4517_ = lean_array_to_list(v_as_4516_);
v___x_4518_ = lean_box(0);
v___x_4519_ = l_List_mapTR_loop___redArg(v_inst_4515_, v___x_4517_, v___x_4518_);
v___x_4520_ = l_Lean_MessageData_ofList(v___x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4521_){
_start:
{
lean_object* v___f_4522_; 
v___f_4522_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4522_, 0, v_inst_4521_);
return v___f_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4523_, lean_object* v_inst_4524_){
_start:
{
lean_object* v___f_4525_; 
v___f_4525_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4525_, 0, v_inst_4524_);
return v___f_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4526_, lean_object* v_acc_4527_, lean_object* v_recur_4528_){
_start:
{
lean_object* v_array_4529_; lean_object* v_start_4530_; lean_object* v_stop_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4544_; 
v_array_4529_ = lean_ctor_get(v_it_4526_, 0);
v_start_4530_ = lean_ctor_get(v_it_4526_, 1);
v_stop_4531_ = lean_ctor_get(v_it_4526_, 2);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_it_4526_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4533_ = v_it_4526_;
v_isShared_4534_ = v_isSharedCheck_4544_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_stop_4531_);
lean_inc(v_start_4530_);
lean_inc(v_array_4529_);
lean_dec(v_it_4526_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4544_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
uint8_t v___x_4535_; 
v___x_4535_ = lean_nat_dec_lt(v_start_4530_, v_stop_4531_);
if (v___x_4535_ == 0)
{
lean_del_object(v___x_4533_);
lean_dec(v_stop_4531_);
lean_dec(v_start_4530_);
lean_dec_ref(v_array_4529_);
lean_dec_ref(v_recur_4528_);
return v_acc_4527_;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4539_; 
v___x_4536_ = lean_unsigned_to_nat(1u);
v___x_4537_ = lean_nat_add(v_start_4530_, v___x_4536_);
lean_inc_ref(v_array_4529_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 1, v___x_4537_);
v___x_4539_ = v___x_4533_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_array_4529_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_stop_4531_);
v___x_4539_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_array_fget(v_array_4529_, v_start_4530_);
lean_dec(v_start_4530_);
lean_dec_ref(v_array_4529_);
v___x_4541_ = lean_array_push(v_acc_4527_, v___x_4540_);
v___x_4542_ = lean_apply_3(v_recur_4528_, v___x_4539_, v___x_4541_, lean_box(0));
return v___x_4542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4547_, lean_object* v_inst_4548_, lean_object* v_as_4549_){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4550_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4551_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4547_, v_as_4549_, v___x_4550_);
v___x_4552_ = lean_array_to_list(v___x_4551_);
v___x_4553_ = lean_box(0);
v___x_4554_ = l_List_mapTR_loop___redArg(v_inst_4548_, v___x_4552_, v___x_4553_);
v___x_4555_ = l_Lean_MessageData_ofList(v___x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4557_){
_start:
{
lean_object* v___f_4558_; lean_object* v___f_4559_; 
v___f_4558_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4559_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4559_, 0, v___f_4558_);
lean_closure_set(v___f_4559_, 1, v_inst_4557_);
return v___f_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4560_, lean_object* v_inst_4561_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4561_);
return v___x_4562_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4567_ = l_Lean_MessageData_ofFormat(v___x_4566_);
return v___x_4567_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4571_ = l_Lean_MessageData_ofFormat(v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4572_, lean_object* v_x_4573_){
_start:
{
if (lean_obj_tag(v_x_4573_) == 0)
{
lean_object* v___x_4574_; 
lean_dec_ref(v_inst_4572_);
v___x_4574_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4574_;
}
else
{
lean_object* v_val_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_val_4575_ = lean_ctor_get(v_x_4573_, 0);
lean_inc(v_val_4575_);
lean_dec_ref_known(v_x_4573_, 1);
v___x_4576_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4577_ = lean_apply_1(v_inst_4572_, v_val_4575_);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4576_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4578_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
return v___x_4580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4581_){
_start:
{
lean_object* v___f_4582_; 
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4582_, 0, v_inst_4581_);
return v___f_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4583_, lean_object* v_inst_4584_){
_start:
{
lean_object* v___f_4585_; 
v___f_4585_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4585_, 0, v_inst_4584_);
return v___f_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4586_, lean_object* v_inst_4587_, lean_object* v_x_4588_){
_start:
{
lean_object* v_fst_4589_; lean_object* v_snd_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4604_; 
v_fst_4589_ = lean_ctor_get(v_x_4588_, 0);
v_snd_4590_ = lean_ctor_get(v_x_4588_, 1);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_x_4588_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4592_ = v_x_4588_;
v_isShared_4593_ = v_isSharedCheck_4604_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_snd_4590_);
lean_inc(v_fst_4589_);
lean_dec(v_x_4588_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4604_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4594_ = lean_apply_1(v_inst_4586_, v_fst_4589_);
v___x_4595_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4593_ == 0)
{
lean_ctor_set_tag(v___x_4592_, 7);
lean_ctor_set(v___x_4592_, 1, v___x_4595_);
lean_ctor_set(v___x_4592_, 0, v___x_4594_);
v___x_4597_ = v___x_4592_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4598_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = lean_apply_1(v_inst_4587_, v_snd_4590_);
v___x_4601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = l_Lean_MessageData_paren(v___x_4601_);
return v___x_4602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4605_, lean_object* v_inst_4606_){
_start:
{
lean_object* v___f_4607_; 
v___f_4607_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4607_, 0, v_inst_4605_);
lean_closure_set(v___f_4607_, 1, v_inst_4606_);
return v___f_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4608_, lean_object* v_00_u03b2_4609_, lean_object* v_inst_4610_, lean_object* v_inst_4611_){
_start:
{
lean_object* v___f_4612_; 
v___f_4612_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4612_, 0, v_inst_4610_);
lean_closure_set(v___f_4612_, 1, v_inst_4611_);
return v___f_4612_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4617_ = l_Lean_MessageData_ofFormat(v___x_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4618_){
_start:
{
if (lean_obj_tag(v_x_4618_) == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4619_;
}
else
{
lean_object* v_val_4620_; lean_object* v___x_4621_; 
v_val_4620_ = lean_ctor_get(v_x_4618_, 0);
lean_inc(v_val_4620_);
lean_dec_ref_known(v_x_4618_, 1);
v___x_4621_ = l_Lean_MessageData_ofExpr(v_val_4620_);
return v___x_4621_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4656_ = l_String_toRawSubstring_x27(v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4672_ = l_String_toRawSubstring_x27(v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4686_);
v___x_4690_ = l_Lean_Syntax_isOfKind(v_x_4686_, v___x_4689_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
lean_dec(v_x_4686_);
v___x_4691_ = lean_box(1);
v___x_4692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
lean_ctor_set(v___x_4692_, 1, v_a_4688_);
return v___x_4692_;
}
else
{
lean_object* v_quotContext_4693_; lean_object* v_currMacroScope_4694_; lean_object* v_ref_4695_; lean_object* v___x_4696_; lean_object* v_interpStr_4697_; uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v_quotContext_4693_ = lean_ctor_get(v_a_4687_, 1);
v_currMacroScope_4694_ = lean_ctor_get(v_a_4687_, 2);
v_ref_4695_ = lean_ctor_get(v_a_4687_, 5);
v___x_4696_ = lean_unsigned_to_nat(1u);
v_interpStr_4697_ = l_Lean_Syntax_getArg(v_x_4686_, v___x_4696_);
lean_dec(v_x_4686_);
v___x_4698_ = 0;
v___x_4699_ = l_Lean_SourceInfo_fromRef(v_ref_4695_, v___x_4698_);
v___x_4700_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4701_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4694_, 2);
lean_inc_n(v_quotContext_4693_, 2);
v___x_4702_ = l_Lean_addMacroScope(v_quotContext_4693_, v___x_4701_, v_currMacroScope_4694_);
v___x_4703_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4699_);
v___x_4704_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4699_);
lean_ctor_set(v___x_4704_, 1, v___x_4700_);
lean_ctor_set(v___x_4704_, 2, v___x_4702_);
lean_ctor_set(v___x_4704_, 3, v___x_4703_);
v___x_4705_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4706_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4707_ = l_Lean_addMacroScope(v_quotContext_4693_, v___x_4706_, v_currMacroScope_4694_);
v___x_4708_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4699_);
lean_ctor_set(v___x_4709_, 1, v___x_4705_);
lean_ctor_set(v___x_4709_, 2, v___x_4707_);
lean_ctor_set(v___x_4709_, 3, v___x_4708_);
lean_inc_ref(v___x_4709_);
v___x_4710_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4697_, v___x_4704_, v___x_4709_, v___x_4709_, v_a_4687_, v_a_4688_);
lean_dec(v_interpStr_4697_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_a_4712_ = lean_ctor_get(v___x_4710_, 1);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4710_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4711_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
v_a_4720_ = lean_ctor_get(v___x_4710_, 0);
v_a_4721_ = lean_ctor_get(v___x_4710_, 1);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4710_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_inc(v_a_4720_);
lean_dec(v___x_4710_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4720_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4729_, v_a_4730_, v_a_4731_);
lean_dec_ref(v_a_4730_);
return v_res_4732_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4735_ = l_Lean_stringToMessageData(v___x_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4736_){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4737_ = lean_array_to_list(v_msgs_4736_);
v___x_4738_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4739_ = l_Lean_MessageData_joinSep(v___x_4737_, v___x_4738_);
v___x_4740_ = l_Lean_indentD(v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4741_, lean_object* v_lctx_4742_, lean_object* v_opts_4743_, lean_object* v_msg_4744_){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4745_ = lean_elab_environment_of_kernel_env(v_env_4741_);
v___x_4746_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
lean_ctor_set(v___x_4747_, 2, v_lctx_4742_);
lean_ctor_set(v___x_4747_, 3, v_opts_4743_);
v___x_4748_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v_msg_4744_);
return v___x_4748_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4754_ = l_Lean_stringToMessageData(v___x_4753_);
return v___x_4754_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4757_ = l_Lean_stringToMessageData(v___x_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4758_, lean_object* v_n_4759_, lean_object* v_expectedType_4760_){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4761_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4762_ = l_Lean_MessageData_ofName(v_n_4759_);
v___x_4763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4763_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = l_Lean_indentExpr(v_givenType_4758_);
v___x_4767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4767_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = l_Lean_indentExpr(v_expectedType_4760_);
v___x_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4769_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
return v___x_4771_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4772_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4775_ = lean_box(1);
v___x_4776_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4777_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
lean_ctor_set(v___x_4778_, 1, v___x_4776_);
lean_ctor_set(v___x_4778_, 2, v___x_4775_);
return v___x_4778_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4781_ = l_Lean_stringToMessageData(v___x_4780_);
return v___x_4781_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4784_ = l_Lean_stringToMessageData(v___x_4783_);
return v___x_4784_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4787_ = l_Lean_stringToMessageData(v___x_4786_);
return v___x_4787_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4792_ = l_Lean_MessageData_ofFormat(v___x_4791_);
return v___x_4792_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4795_ = l_Lean_stringToMessageData(v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4798_ = l_Lean_stringToMessageData(v___x_4797_);
return v___x_4798_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4801_ = l_Lean_stringToMessageData(v___x_4800_);
return v___x_4801_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4804_ = l_Lean_stringToMessageData(v___x_4803_);
return v___x_4804_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4807_ = l_Lean_stringToMessageData(v___x_4806_);
return v___x_4807_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4810_ = l_Lean_stringToMessageData(v___x_4809_);
return v___x_4810_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4813_ = l_Lean_stringToMessageData(v___x_4812_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4816_ = l_Lean_stringToMessageData(v___x_4815_);
return v___x_4816_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4819_ = l_Lean_stringToMessageData(v___x_4818_);
return v___x_4819_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4821_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4822_ = l_Lean_stringToMessageData(v___x_4821_);
return v___x_4822_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4824_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4825_ = l_Lean_stringToMessageData(v___x_4824_);
return v___x_4825_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4828_ = l_Lean_stringToMessageData(v___x_4827_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4831_ = l_Lean_stringToMessageData(v___x_4830_);
return v___x_4831_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4834_ = l_Lean_stringToMessageData(v___x_4833_);
return v___x_4834_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4839_ = l_Lean_MessageData_ofFormat(v___x_4838_);
return v___x_4839_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4844_ = l_Lean_MessageData_ofFormat(v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4849_ = l_Lean_MessageData_ofFormat(v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4854_ = l_Lean_MessageData_ofFormat(v___x_4853_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4855_, lean_object* v_opts_4856_){
_start:
{
switch(lean_obj_tag(v_e_4855_))
{
case 0:
{
lean_object* v_env_4857_; lean_object* v_name_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4871_; 
v_env_4857_ = lean_ctor_get(v_e_4855_, 0);
v_name_4858_ = lean_ctor_get(v_e_4855_, 1);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_e_4855_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4860_ = v_e_4855_;
v_isShared_4861_ = v_isSharedCheck_4871_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_name_4858_);
lean_inc(v_env_4857_);
lean_dec(v_e_4855_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4871_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4862_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4863_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4864_ = l_Lean_MessageData_ofName(v_name_4858_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set_tag(v___x_4860_, 7);
lean_ctor_set(v___x_4860_, 1, v___x_4864_);
lean_ctor_set(v___x_4860_, 0, v___x_4863_);
v___x_4866_ = v___x_4860_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4867_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4857_, v___x_4862_, v_opts_4856_, v___x_4868_);
return v___x_4869_;
}
}
}
case 1:
{
lean_object* v_env_4872_; lean_object* v_name_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4887_; 
v_env_4872_ = lean_ctor_get(v_e_4855_, 0);
v_name_4873_ = lean_ctor_get(v_e_4855_, 1);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_e_4855_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4875_ = v_e_4855_;
v_isShared_4876_ = v_isSharedCheck_4887_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_name_4873_);
lean_inc(v_env_4872_);
lean_dec(v_e_4855_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4887_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4877_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4878_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4879_ = 1;
v___x_4880_ = l_Lean_MessageData_ofConstName(v_name_4873_, v___x_4879_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set_tag(v___x_4875_, 7);
lean_ctor_set(v___x_4875_, 1, v___x_4880_);
lean_ctor_set(v___x_4875_, 0, v___x_4878_);
v___x_4882_ = v___x_4875_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4878_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4883_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4872_, v___x_4877_, v_opts_4856_, v___x_4884_);
return v___x_4885_;
}
}
}
case 2:
{
lean_object* v_env_4888_; lean_object* v_decl_4889_; lean_object* v_givenType_4890_; lean_object* v___x_4891_; 
v_env_4888_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4888_);
v_decl_4889_ = lean_ctor_get(v_e_4855_, 1);
lean_inc(v_decl_4889_);
v_givenType_4890_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_givenType_4890_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4891_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4889_))
{
case 1:
{
lean_object* v_val_4892_; lean_object* v_toConstantVal_4893_; lean_object* v_name_4894_; lean_object* v_type_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v_val_4892_ = lean_ctor_get(v_decl_4889_, 0);
lean_inc_ref(v_val_4892_);
lean_dec_ref_known(v_decl_4889_, 1);
v_toConstantVal_4893_ = lean_ctor_get(v_val_4892_, 0);
lean_inc_ref(v_toConstantVal_4893_);
lean_dec_ref(v_val_4892_);
v_name_4894_ = lean_ctor_get(v_toConstantVal_4893_, 0);
lean_inc(v_name_4894_);
v_type_4895_ = lean_ctor_get(v_toConstantVal_4893_, 2);
lean_inc_ref(v_type_4895_);
lean_dec_ref(v_toConstantVal_4893_);
v___x_4896_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4890_, v_name_4894_, v_type_4895_);
v___x_4897_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4888_, v___x_4891_, v_opts_4856_, v___x_4896_);
return v___x_4897_;
}
case 2:
{
lean_object* v_val_4898_; lean_object* v_toConstantVal_4899_; lean_object* v_name_4900_; lean_object* v_type_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v_val_4898_ = lean_ctor_get(v_decl_4889_, 0);
lean_inc_ref(v_val_4898_);
lean_dec_ref_known(v_decl_4889_, 1);
v_toConstantVal_4899_ = lean_ctor_get(v_val_4898_, 0);
lean_inc_ref(v_toConstantVal_4899_);
lean_dec_ref(v_val_4898_);
v_name_4900_ = lean_ctor_get(v_toConstantVal_4899_, 0);
lean_inc(v_name_4900_);
v_type_4901_ = lean_ctor_get(v_toConstantVal_4899_, 2);
lean_inc_ref(v_type_4901_);
lean_dec_ref(v_toConstantVal_4899_);
v___x_4902_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4890_, v_name_4900_, v_type_4901_);
v___x_4903_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4888_, v___x_4891_, v_opts_4856_, v___x_4902_);
return v___x_4903_;
}
default: 
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
lean_dec_ref(v_givenType_4890_);
lean_dec(v_decl_4889_);
v___x_4904_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4905_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4888_, v___x_4891_, v_opts_4856_, v___x_4904_);
return v___x_4905_;
}
}
}
case 3:
{
lean_object* v_env_4906_; lean_object* v_name_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v_env_4906_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4906_);
v_name_4907_ = lean_ctor_get(v_e_4855_, 1);
lean_inc(v_name_4907_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4908_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4909_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4910_ = 1;
v___x_4911_ = l_Lean_MessageData_ofConstName(v_name_4907_, v___x_4910_);
v___x_4912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4909_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
v___x_4913_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4906_, v___x_4908_, v_opts_4856_, v___x_4914_);
return v___x_4915_;
}
case 4:
{
lean_object* v_env_4916_; lean_object* v_name_4917_; lean_object* v_expr_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v_env_4916_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4916_);
v_name_4917_ = lean_ctor_get(v_e_4855_, 1);
lean_inc(v_name_4917_);
v_expr_4918_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_expr_4918_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4919_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4920_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4921_ = 1;
v___x_4922_ = l_Lean_MessageData_ofConstName(v_name_4917_, v___x_4921_);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4920_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
v___x_4924_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = l_Lean_indentExpr(v_expr_4918_);
v___x_4927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
v___x_4928_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4916_, v___x_4919_, v_opts_4856_, v___x_4927_);
return v___x_4928_;
}
case 5:
{
lean_object* v_env_4929_; lean_object* v_lctx_4930_; lean_object* v_expr_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v_env_4929_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4929_);
v_lctx_4930_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4930_);
v_expr_4931_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_expr_4931_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4932_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4933_ = l_Lean_indentExpr(v_expr_4931_);
v___x_4934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4932_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4929_, v_lctx_4930_, v_opts_4856_, v___x_4934_);
return v___x_4935_;
}
case 6:
{
lean_object* v_env_4936_; lean_object* v_lctx_4937_; lean_object* v_expr_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v_env_4936_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4936_);
v_lctx_4937_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4937_);
v_expr_4938_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_expr_4938_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4939_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4940_ = l_Lean_indentExpr(v_expr_4938_);
v___x_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4939_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4936_, v_lctx_4937_, v_opts_4856_, v___x_4941_);
return v___x_4942_;
}
case 7:
{
lean_object* v_env_4943_; lean_object* v_lctx_4944_; lean_object* v_name_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_env_4943_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4943_);
v_lctx_4944_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4944_);
v_name_4945_ = lean_ctor_get(v_e_4855_, 2);
lean_inc(v_name_4945_);
lean_dec_ref_known(v_e_4855_, 5);
v___x_4946_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4947_ = l_Lean_MessageData_ofName(v_name_4945_);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4946_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4943_, v_lctx_4944_, v_opts_4856_, v___x_4950_);
return v___x_4951_;
}
case 8:
{
lean_object* v_env_4952_; lean_object* v_lctx_4953_; lean_object* v_expr_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v_env_4952_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4952_);
v_lctx_4953_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4953_);
v_expr_4954_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_expr_4954_);
lean_dec_ref_known(v_e_4855_, 4);
v___x_4955_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4956_ = l_Lean_indentExpr(v_expr_4954_);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4952_, v_lctx_4953_, v_opts_4856_, v___x_4957_);
return v___x_4958_;
}
case 9:
{
lean_object* v_env_4959_; lean_object* v_lctx_4960_; lean_object* v_app_4961_; lean_object* v_funType_4962_; lean_object* v_argType_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v_env_4959_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4959_);
v_lctx_4960_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4960_);
v_app_4961_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_app_4961_);
v_funType_4962_ = lean_ctor_get(v_e_4855_, 3);
lean_inc_ref(v_funType_4962_);
v_argType_4963_ = lean_ctor_get(v_e_4855_, 4);
lean_inc_ref(v_argType_4963_);
lean_dec_ref_known(v_e_4855_, 5);
v___x_4964_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4965_ = l_Lean_indentExpr(v_app_4961_);
v___x_4966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4964_);
lean_ctor_set(v___x_4966_, 1, v___x_4965_);
v___x_4967_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4966_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = l_Lean_indentExpr(v_argType_4963_);
v___x_4970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4968_);
lean_ctor_set(v___x_4970_, 1, v___x_4969_);
v___x_4971_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4970_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
v___x_4973_ = l_Lean_indentExpr(v_funType_4962_);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4959_, v_lctx_4960_, v_opts_4856_, v___x_4974_);
return v___x_4975_;
}
case 10:
{
lean_object* v_env_4976_; lean_object* v_lctx_4977_; lean_object* v_proj_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_env_4976_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4976_);
v_lctx_4977_ = lean_ctor_get(v_e_4855_, 1);
lean_inc_ref(v_lctx_4977_);
v_proj_4978_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_proj_4978_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4979_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4980_ = l_Lean_indentExpr(v_proj_4978_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4976_, v_lctx_4977_, v_opts_4856_, v___x_4981_);
return v___x_4982_;
}
case 11:
{
lean_object* v_env_4983_; lean_object* v_name_4984_; lean_object* v_type_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v_env_4983_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_env_4983_);
v_name_4984_ = lean_ctor_get(v_e_4855_, 1);
lean_inc(v_name_4984_);
v_type_4985_ = lean_ctor_get(v_e_4855_, 2);
lean_inc_ref(v_type_4985_);
lean_dec_ref_known(v_e_4855_, 3);
v___x_4986_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4987_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4988_ = 1;
v___x_4989_ = l_Lean_MessageData_ofConstName(v_name_4984_, v___x_4988_);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4987_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_indentExpr(v_type_4985_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4983_, v___x_4986_, v_opts_4856_, v___x_4994_);
return v___x_4995_;
}
case 12:
{
lean_object* v_msg_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref(v_opts_4856_);
v_msg_4996_ = lean_ctor_get(v_e_4855_, 0);
lean_inc_ref(v_msg_4996_);
lean_dec_ref_known(v_e_4855_, 1);
v___x_4997_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4998_ = l_Lean_stringToMessageData(v_msg_4996_);
v___x_4999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
return v___x_4999_;
}
case 13:
{
lean_object* v___x_5000_; 
lean_dec_ref(v_opts_4856_);
v___x_5000_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_5000_;
}
case 14:
{
lean_object* v___x_5001_; 
lean_dec_ref(v_opts_4856_);
v___x_5001_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_5001_;
}
case 15:
{
lean_object* v___x_5002_; 
lean_dec_ref(v_opts_4856_);
v___x_5002_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_5002_;
}
default: 
{
lean_object* v___x_5003_; 
lean_dec_ref(v_opts_4856_);
v___x_5003_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_5003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_5004_, lean_object* v_e_5005_, lean_object* v_cls_5006_){
_start:
{
lean_object* v___x_5007_; double v___x_5008_; uint8_t v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5007_ = lean_box(0);
v___x_5008_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_5009_ = 1;
v___x_5010_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_5011_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5011_, 0, v_cls_5006_);
lean_ctor_set(v___x_5011_, 1, v___x_5007_);
lean_ctor_set(v___x_5011_, 2, v___x_5010_);
lean_ctor_set_float(v___x_5011_, sizeof(void*)*3, v___x_5008_);
lean_ctor_set_float(v___x_5011_, sizeof(void*)*3 + 8, v___x_5008_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*3 + 16, v___x_5009_);
v___x_5012_ = lean_apply_1(v_inst_5004_, v_e_5005_);
v___x_5013_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_5014_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5011_);
lean_ctor_set(v___x_5014_, 1, v___x_5012_);
lean_ctor_set(v___x_5014_, 2, v___x_5013_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_5015_, lean_object* v_inst_5016_, lean_object* v_e_5017_, lean_object* v_cls_5018_){
_start:
{
lean_object* v___x_5019_; 
v___x_5019_ = l_Lean_toTraceElem___redArg(v_inst_5016_, v_e_5017_, v_cls_5018_);
return v___x_5019_;
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
