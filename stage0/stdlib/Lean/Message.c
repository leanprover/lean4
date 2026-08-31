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
lean_object* l_Lean_Environment_ofKernelEnv(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx(uint8_t v_x_92_){
_start:
{
switch(v_x_92_)
{
case 0:
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(0u);
return v___x_93_;
}
case 1:
{
lean_object* v___x_94_; 
v___x_94_ = lean_unsigned_to_nat(1u);
return v___x_94_;
}
default: 
{
lean_object* v___x_95_; 
v___x_95_ = lean_unsigned_to_nat(2u);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___boxed(lean_object* v_x_96_){
_start:
{
uint8_t v_x_boxed_97_; lean_object* v_res_98_; 
v_x_boxed_97_ = lean_unbox(v_x_96_);
v_res_98_ = l_Lean_MessageSeverity_ctorIdx(v_x_boxed_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* v_k_99_){
_start:
{
lean_inc(v_k_99_);
return v_k_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* v_k_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_MessageSeverity_ctorElim___redArg(v_k_100_);
lean_dec(v_k_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_102_, lean_object* v_ctorIdx_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_k_106_){
_start:
{
lean_inc(v_k_106_);
return v_k_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_107_, lean_object* v_ctorIdx_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_k_111_){
_start:
{
uint8_t v_t_boxed_112_; lean_object* v_res_113_; 
v_t_boxed_112_ = lean_unbox(v_t_109_);
v_res_113_ = l_Lean_MessageSeverity_ctorElim(v_motive_107_, v_ctorIdx_108_, v_t_boxed_112_, v_h_110_, v_k_111_);
lean_dec(v_k_111_);
lean_dec(v_ctorIdx_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_114_){
_start:
{
lean_inc(v_information_114_);
return v_information_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_115_);
lean_dec(v_information_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_117_, uint8_t v_t_118_, lean_object* v_h_119_, lean_object* v_information_120_){
_start:
{
lean_inc(v_information_120_);
return v_information_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_information_124_){
_start:
{
uint8_t v_t_boxed_125_; lean_object* v_res_126_; 
v_t_boxed_125_ = lean_unbox(v_t_122_);
v_res_126_ = l_Lean_MessageSeverity_information_elim(v_motive_121_, v_t_boxed_125_, v_h_123_, v_information_124_);
lean_dec(v_information_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_127_){
_start:
{
lean_inc(v_warning_127_);
return v_warning_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_128_);
lean_dec(v_warning_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_130_, uint8_t v_t_131_, lean_object* v_h_132_, lean_object* v_warning_133_){
_start:
{
lean_inc(v_warning_133_);
return v_warning_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_warning_137_){
_start:
{
uint8_t v_t_boxed_138_; lean_object* v_res_139_; 
v_t_boxed_138_ = lean_unbox(v_t_135_);
v_res_139_ = l_Lean_MessageSeverity_warning_elim(v_motive_134_, v_t_boxed_138_, v_h_136_, v_warning_137_);
lean_dec(v_warning_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* v_error_140_){
_start:
{
lean_inc(v_error_140_);
return v_error_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* v_error_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_MessageSeverity_error_elim___redArg(v_error_141_);
lean_dec(v_error_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_143_, uint8_t v_t_144_, lean_object* v_h_145_, lean_object* v_error_146_){
_start:
{
lean_inc(v_error_146_);
return v_error_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_error_150_){
_start:
{
uint8_t v_t_boxed_151_; lean_object* v_res_152_; 
v_t_boxed_151_ = lean_unbox(v_t_148_);
v_res_152_ = l_Lean_MessageSeverity_error_elim(v_motive_147_, v_t_boxed_151_, v_h_149_, v_error_150_);
lean_dec(v_error_150_);
return v_res_152_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_155_, uint8_t v_y_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = l_Lean_MessageSeverity_ctorIdx(v_x_155_);
v___x_158_ = l_Lean_MessageSeverity_ctorIdx(v_y_156_);
v___x_159_ = lean_nat_dec_eq(v___x_157_, v___x_158_);
lean_dec(v___x_158_);
lean_dec(v___x_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_160_, lean_object* v_y_161_){
_start:
{
uint8_t v_x_21__boxed_162_; uint8_t v_y_22__boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_x_21__boxed_162_ = lean_unbox(v_x_160_);
v_y_22__boxed_163_ = lean_unbox(v_y_161_);
v_res_164_ = l_Lean_instBEqMessageSeverity_beq(v_x_21__boxed_162_, v_y_22__boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_177_){
_start:
{
switch(v_x_177_)
{
case 0:
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_178_;
}
case 1:
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_179_;
}
default: 
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_181_){
_start:
{
uint8_t v_x_67__boxed_182_; lean_object* v_res_183_; 
v_x_67__boxed_182_ = lean_unbox(v_x_181_);
v_res_183_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Json_getTag_x3f(v_json_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_203_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_val_204_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_202_, 1);
v___x_205_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_206_ = lean_string_dec_eq(v_val_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_208_ = lean_string_dec_eq(v_val_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_210_ = lean_string_dec_eq(v_val_204_, v___x_209_);
lean_dec(v_val_204_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_212_;
}
}
else
{
lean_object* v___x_213_; 
lean_dec(v_val_204_);
v___x_213_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_val_204_);
v___x_214_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_217_){
_start:
{
switch(v_x_217_)
{
case 0:
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_218_;
}
case 1:
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_219_;
}
default: 
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_221_){
_start:
{
uint8_t v_x_28__boxed_222_; lean_object* v_res_223_; 
v_x_28__boxed_222_ = lean_unbox(v_x_221_);
v_res_223_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx(uint8_t v_x_226_){
_start:
{
switch(v_x_226_)
{
case 0:
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
return v___x_227_;
}
case 1:
{
lean_object* v___x_228_; 
v___x_228_ = lean_unsigned_to_nat(1u);
return v___x_228_;
}
default: 
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(2u);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___boxed(lean_object* v_x_230_){
_start:
{
uint8_t v_x_boxed_231_; lean_object* v_res_232_; 
v_x_boxed_231_ = lean_unbox(v_x_230_);
v_res_232_ = l_Lean_TraceResult_ctorIdx(v_x_boxed_231_);
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
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = l_Lean_TraceResult_ctorIdx(v_x_289_);
v___x_292_ = l_Lean_TraceResult_ctorIdx(v_y_290_);
v___x_293_ = lean_nat_dec_eq(v___x_291_, v___x_292_);
lean_dec(v___x_292_);
lean_dec(v___x_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_294_, lean_object* v_y_295_){
_start:
{
uint8_t v_x_21__boxed_296_; uint8_t v_y_22__boxed_297_; uint8_t v_res_298_; lean_object* v_r_299_; 
v_x_21__boxed_296_ = lean_unbox(v_x_294_);
v_y_22__boxed_297_ = lean_unbox(v_y_295_);
v_res_298_ = l_Lean_instBEqTraceResult_beq(v_x_21__boxed_296_, v_y_22__boxed_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(2u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_315_, lean_object* v_prec_316_){
_start:
{
lean_object* v___y_318_; lean_object* v___y_325_; lean_object* v___y_332_; 
switch(v_x_315_)
{
case 0:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(1024u);
v___x_339_ = lean_nat_dec_le(v___x_338_, v_prec_316_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_318_ = v___x_340_;
goto v___jp_317_;
}
else
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_318_ = v___x_341_;
goto v___jp_317_;
}
}
case 1:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1024u);
v___x_343_ = lean_nat_dec_le(v___x_342_, v_prec_316_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_325_ = v___x_344_;
goto v___jp_324_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_325_ = v___x_345_;
goto v___jp_324_;
}
}
default: 
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1024u);
v___x_347_ = lean_nat_dec_le(v___x_346_, v_prec_316_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_332_ = v___x_348_;
goto v___jp_331_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_332_ = v___x_349_;
goto v___jp_331_;
}
}
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_318_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_316_);
return v___x_323_;
}
v___jp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_326_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_325_);
v___x_327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_327_, 0, v___y_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = 0;
v___x_329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*1, v___x_328_);
v___x_330_ = l_Repr_addAppParen(v___x_329_, v_prec_316_);
return v___x_330_;
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_333_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_332_);
v___x_334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = 0;
v___x_336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*1, v___x_335_);
v___x_337_ = l_Repr_addAppParen(v___x_336_, v_prec_316_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_350_, lean_object* v_prec_351_){
_start:
{
uint8_t v_x_171__boxed_352_; lean_object* v_res_353_; 
v_x_171__boxed_352_ = lean_unbox(v_x_350_);
v_res_353_ = l_Lean_instReprTraceResult_repr(v_x_171__boxed_352_, v_prec_351_);
lean_dec(v_prec_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_359_){
_start:
{
switch(v_x_359_)
{
case 0:
{
lean_object* v___x_360_; 
v___x_360_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_360_;
}
case 1:
{
lean_object* v___x_361_; 
v___x_361_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_361_;
}
default: 
{
lean_object* v___x_362_; 
v___x_362_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_363_){
_start:
{
uint8_t v_x_31__boxed_364_; lean_object* v_res_365_; 
v_x_31__boxed_364_ = lean_unbox(v_x_363_);
v_res_365_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object* v_x_366_){
_start:
{
switch(lean_obj_tag(v_x_366_))
{
case 0:
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(0u);
return v___x_367_;
}
case 1:
{
lean_object* v___x_368_; 
v___x_368_ = lean_unsigned_to_nat(1u);
return v___x_368_;
}
case 2:
{
lean_object* v___x_369_; 
v___x_369_ = lean_unsigned_to_nat(2u);
return v___x_369_;
}
case 3:
{
lean_object* v___x_370_; 
v___x_370_ = lean_unsigned_to_nat(3u);
return v___x_370_;
}
case 4:
{
lean_object* v___x_371_; 
v___x_371_ = lean_unsigned_to_nat(4u);
return v___x_371_;
}
case 5:
{
lean_object* v___x_372_; 
v___x_372_ = lean_unsigned_to_nat(5u);
return v___x_372_;
}
case 6:
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(6u);
return v___x_373_;
}
case 7:
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(7u);
return v___x_374_;
}
case 8:
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(8u);
return v___x_375_;
}
case 9:
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(9u);
return v___x_376_;
}
case 10:
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(10u);
return v___x_377_;
}
default: 
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(11u);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_MessageData_ctorIdx(v_x_379_);
lean_dec_ref(v_x_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_381_, lean_object* v_k_382_){
_start:
{
switch(lean_obj_tag(v_t_381_))
{
case 0:
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v_t_381_, 0);
lean_inc_ref(v_a_383_);
lean_dec_ref_known(v_t_381_, 1);
v___x_384_ = lean_apply_1(v_k_382_, v_a_383_);
return v___x_384_;
}
case 1:
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v_t_381_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_t_381_, 1);
v___x_386_ = lean_apply_1(v_k_382_, v_a_385_);
return v___x_386_;
}
case 5:
{
lean_object* v_a_387_; lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v_t_381_, 0);
lean_inc(v_a_387_);
v_a_388_ = lean_ctor_get(v_t_381_, 1);
lean_inc_ref(v_a_388_);
lean_dec_ref_known(v_t_381_, 2);
v___x_389_ = lean_apply_2(v_k_382_, v_a_387_, v_a_388_);
return v___x_389_;
}
case 6:
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v_t_381_, 0);
lean_inc_ref(v_a_390_);
lean_dec_ref_known(v_t_381_, 1);
v___x_391_ = lean_apply_1(v_k_382_, v_a_390_);
return v___x_391_;
}
case 8:
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_392_ = lean_ctor_get(v_t_381_, 0);
lean_inc(v_a_392_);
v_a_393_ = lean_ctor_get(v_t_381_, 1);
lean_inc_ref(v_a_393_);
lean_dec_ref_known(v_t_381_, 2);
v___x_394_ = lean_apply_2(v_k_382_, v_a_392_, v_a_393_);
return v___x_394_;
}
case 9:
{
lean_object* v_data_395_; lean_object* v_msg_396_; lean_object* v_children_397_; lean_object* v___x_398_; 
v_data_395_ = lean_ctor_get(v_t_381_, 0);
lean_inc_ref(v_data_395_);
v_msg_396_ = lean_ctor_get(v_t_381_, 1);
lean_inc_ref(v_msg_396_);
v_children_397_ = lean_ctor_get(v_t_381_, 2);
lean_inc_ref(v_children_397_);
lean_dec_ref_known(v_t_381_, 3);
v___x_398_ = lean_apply_3(v_k_382_, v_data_395_, v_msg_396_, v_children_397_);
return v___x_398_;
}
case 11:
{
lean_object* v_a_399_; lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v_t_381_, 0);
lean_inc(v_a_399_);
v_a_400_ = lean_ctor_get(v_t_381_, 1);
lean_inc_ref(v_a_400_);
lean_dec_ref_known(v_t_381_, 2);
v___x_401_ = lean_apply_2(v_k_382_, v_a_399_, v_a_400_);
return v___x_401_;
}
default: 
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v_t_381_, 0);
lean_inc_ref(v_a_402_);
v_a_403_ = lean_ctor_get(v_t_381_, 1);
lean_inc_ref(v_a_403_);
lean_dec_ref(v_t_381_);
v___x_404_ = lean_apply_2(v_k_382_, v_a_402_, v_a_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_405_, lean_object* v_ctorIdx_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_k_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_MessageData_ctorElim___redArg(v_t_407_, v_k_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_411_, lean_object* v_ctorIdx_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_k_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_MessageData_ctorElim(v_motive__1_411_, v_ctorIdx_412_, v_t_413_, v_h_414_, v_k_415_);
lean_dec(v_ctorIdx_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_417_, lean_object* v_ofFormatWithInfos_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_MessageData_ctorElim___redArg(v_t_417_, v_ofFormatWithInfos_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_ofFormatWithInfos_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_MessageData_ctorElim___redArg(v_t_421_, v_ofFormatWithInfos_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_425_, lean_object* v_ofGoal_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_MessageData_ctorElim___redArg(v_t_425_, v_ofGoal_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_ofGoal_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_MessageData_ctorElim___redArg(v_t_429_, v_ofGoal_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_433_, lean_object* v_ofWidget_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_MessageData_ctorElim___redArg(v_t_433_, v_ofWidget_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_ofWidget_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_MessageData_ctorElim___redArg(v_t_437_, v_ofWidget_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_441_, lean_object* v_withContext_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_MessageData_ctorElim___redArg(v_t_441_, v_withContext_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_withContext_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_MessageData_ctorElim___redArg(v_t_445_, v_withContext_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_449_, lean_object* v_withNamingContext_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_MessageData_ctorElim___redArg(v_t_449_, v_withNamingContext_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_withNamingContext_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_MessageData_ctorElim___redArg(v_t_453_, v_withNamingContext_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_457_, lean_object* v_nest_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_MessageData_ctorElim___redArg(v_t_457_, v_nest_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_460_, lean_object* v_t_461_, lean_object* v_h_462_, lean_object* v_nest_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_MessageData_ctorElim___redArg(v_t_461_, v_nest_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_465_, lean_object* v_group_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_MessageData_ctorElim___redArg(v_t_465_, v_group_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_group_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_MessageData_ctorElim___redArg(v_t_469_, v_group_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_473_, lean_object* v_compose_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_MessageData_ctorElim___redArg(v_t_473_, v_compose_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_compose_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_MessageData_ctorElim___redArg(v_t_477_, v_compose_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_481_, lean_object* v_tagged_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_MessageData_ctorElim___redArg(v_t_481_, v_tagged_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_tagged_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_MessageData_ctorElim___redArg(v_t_485_, v_tagged_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_489_, lean_object* v_trace_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_MessageData_ctorElim___redArg(v_t_489_, v_trace_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_trace_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_MessageData_ctorElim___redArg(v_t_493_, v_trace_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_497_, lean_object* v_ofLazy_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_MessageData_ctorElim___redArg(v_t_497_, v_ofLazy_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_ofLazy_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MessageData_ctorElim___redArg(v_t_501_, v_ofLazy_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_505_, lean_object* v_ofOriginatingSyntax_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_MessageData_ctorElim___redArg(v_t_505_, v_ofOriginatingSyntax_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_ofOriginatingSyntax_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_MessageData_ctorElim___redArg(v_t_509_, v_ofOriginatingSyntax_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_box(1);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_fmt_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_528_, lean_object* v_onMissingContext_529_, lean_object* v_f_530_, lean_object* v_ctx_x3f_531_){
_start:
{
lean_object* v_msg_534_; 
if (lean_obj_tag(v_ctx_x3f_531_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_f_530_);
v___x_536_ = lean_box(0);
v___x_537_ = lean_apply_2(v_onMissingContext_529_, v___x_536_, lean_box(0));
v_msg_534_ = v___x_537_;
goto v___jp_533_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; 
lean_dec_ref(v_onMissingContext_529_);
v_val_538_ = lean_ctor_get(v_ctx_x3f_531_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v_ctx_x3f_531_, 1);
v___x_539_ = lean_apply_2(v_f_530_, v_val_538_, lean_box(0));
v_msg_534_ = v___x_539_;
goto v___jp_533_;
}
v___jp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_528_);
lean_ctor_set(v___x_535_, 1, v_msg_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_540_, lean_object* v_onMissingContext_541_, lean_object* v_f_542_, lean_object* v_ctx_x3f_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_MessageData_lazy___lam__0(v___x_540_, v_onMissingContext_541_, v_f_542_, v_ctx_x3f_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_546_, lean_object* v_hasSyntheticSorry_547_, lean_object* v_onMissingContext_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___x_551_; 
v___x_549_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_550_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_550_, 0, v___x_549_);
lean_closure_set(v___f_550_, 1, v_onMissingContext_548_);
lean_closure_set(v___f_550_, 2, v_f_546_);
v___x_551_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_551_, 0, v___f_550_);
lean_ctor_set(v___x_551_, 1, v_hasSyntheticSorry_547_);
return v___x_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_552_, lean_object* v_x_553_){
_start:
{
switch(lean_obj_tag(v_x_553_))
{
case 3:
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_554_);
lean_dec_ref_known(v_x_553_, 2);
v_x_553_ = v_a_554_;
goto _start;
}
case 4:
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_556_);
lean_dec_ref_known(v_x_553_, 2);
v_x_553_ = v_a_556_;
goto _start;
}
case 5:
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_558_);
lean_dec_ref_known(v_x_553_, 2);
v_x_553_ = v_a_558_;
goto _start;
}
case 6:
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v_x_553_, 0);
lean_inc_ref(v_a_560_);
lean_dec_ref_known(v_x_553_, 1);
v_x_553_ = v_a_560_;
goto _start;
}
case 7:
{
lean_object* v_a_562_; lean_object* v_a_563_; uint8_t v___x_564_; 
v_a_562_ = lean_ctor_get(v_x_553_, 0);
lean_inc_ref(v_a_562_);
v_a_563_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_563_);
lean_dec_ref_known(v_x_553_, 2);
lean_inc_ref(v_p_552_);
v___x_564_ = l_Lean_MessageData_hasTag(v_p_552_, v_a_562_);
if (v___x_564_ == 0)
{
v_x_553_ = v_a_563_;
goto _start;
}
else
{
lean_dec_ref(v_a_563_);
lean_dec_ref(v_p_552_);
return v___x_564_;
}
}
case 8:
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_a_566_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_a_566_);
v_a_567_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_567_);
lean_dec_ref_known(v_x_553_, 2);
lean_inc_ref(v_p_552_);
v___x_568_ = lean_apply_1(v_p_552_, v_a_566_);
v___x_569_ = lean_unbox(v___x_568_);
if (v___x_569_ == 0)
{
v_x_553_ = v_a_567_;
goto _start;
}
else
{
uint8_t v___x_571_; 
lean_dec_ref(v_a_567_);
lean_dec_ref(v_p_552_);
v___x_571_ = lean_unbox(v___x_568_);
return v___x_571_;
}
}
case 9:
{
lean_object* v_data_572_; lean_object* v_msg_573_; lean_object* v_children_574_; lean_object* v_cls_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_data_572_ = lean_ctor_get(v_x_553_, 0);
lean_inc_ref(v_data_572_);
v_msg_573_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_msg_573_);
v_children_574_ = lean_ctor_get(v_x_553_, 2);
lean_inc_ref(v_children_574_);
lean_dec_ref_known(v_x_553_, 3);
v_cls_575_ = lean_ctor_get(v_data_572_, 0);
lean_inc(v_cls_575_);
lean_dec_ref(v_data_572_);
lean_inc_ref(v_p_552_);
v___x_576_ = lean_apply_1(v_p_552_, v_cls_575_);
v___x_577_ = lean_unbox(v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; 
lean_inc_ref(v_p_552_);
v___x_578_ = l_Lean_MessageData_hasTag(v_p_552_, v_msg_573_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_array_get_size(v_children_574_);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec_ref(v_children_574_);
lean_dec_ref(v_p_552_);
return v___x_581_;
}
else
{
if (v___x_581_ == 0)
{
lean_dec_ref(v_children_574_);
lean_dec_ref(v_p_552_);
return v___x_581_;
}
else
{
size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_580_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_552_, v_children_574_, v___x_582_, v___x_583_);
lean_dec_ref(v_children_574_);
return v___x_584_;
}
}
}
else
{
lean_dec_ref(v_children_574_);
lean_dec_ref(v_p_552_);
return v___x_578_;
}
}
else
{
uint8_t v___x_585_; 
lean_dec_ref(v_children_574_);
lean_dec_ref(v_msg_573_);
lean_dec_ref(v_p_552_);
v___x_585_ = lean_unbox(v___x_576_);
return v___x_585_;
}
}
case 11:
{
lean_object* v_a_586_; 
v_a_586_ = lean_ctor_get(v_x_553_, 1);
lean_inc_ref(v_a_586_);
lean_dec_ref_known(v_x_553_, 2);
v_x_553_ = v_a_586_;
goto _start;
}
default: 
{
uint8_t v___x_588_; 
lean_dec_ref(v_x_553_);
lean_dec_ref(v_p_552_);
v___x_588_ = 0;
return v___x_588_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_589_, lean_object* v_as_590_, size_t v_i_591_, size_t v_stop_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_eq(v_i_591_, v_stop_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_uget_borrowed(v_as_590_, v_i_591_);
lean_inc(v___x_594_);
lean_inc_ref(v_p_589_);
v___x_595_ = l_Lean_MessageData_hasTag(v_p_589_, v___x_594_);
if (v___x_595_ == 0)
{
size_t v___x_596_; size_t v___x_597_; 
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_add(v_i_591_, v___x_596_);
v_i_591_ = v___x_597_;
goto _start;
}
else
{
lean_dec_ref(v_p_589_);
return v___x_595_;
}
}
else
{
uint8_t v___x_599_; 
lean_dec_ref(v_p_589_);
v___x_599_ = 0;
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_600_, lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_stop_603_){
_start:
{
size_t v_i_boxed_604_; size_t v_stop_boxed_605_; uint8_t v_res_606_; lean_object* v_r_607_; 
v_i_boxed_604_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_stop_boxed_605_ = lean_unbox_usize(v_stop_603_);
lean_dec(v_stop_603_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_600_, v_as_601_, v_i_boxed_604_, v_stop_boxed_605_);
lean_dec_ref(v_as_601_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_MessageData_hasTag(v_p_608_, v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_612_){
_start:
{
switch(lean_obj_tag(v_x_612_))
{
case 3:
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v_x_612_, 1);
v_x_612_ = v_a_613_;
goto _start;
}
case 4:
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v_x_612_, 1);
v_x_612_ = v_a_615_;
goto _start;
}
case 8:
{
lean_object* v_a_617_; 
v_a_617_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_a_617_);
return v_a_617_;
}
case 9:
{
lean_object* v_data_618_; lean_object* v_cls_619_; 
v_data_618_ = lean_ctor_get(v_x_612_, 0);
v_cls_619_ = lean_ctor_get(v_data_618_, 0);
lean_inc(v_cls_619_);
return v_cls_619_;
}
case 11:
{
lean_object* v_a_620_; 
v_a_620_ = lean_ctor_get(v_x_612_, 1);
v_x_612_ = v_a_620_;
goto _start;
}
default: 
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_MessageData_kind(v_x_623_);
lean_dec_ref(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 11)
{
lean_object* v_a_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v_a_626_ = lean_ctor_get(v_x_625_, 0);
v_a_627_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v_x_625_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_inc(v_a_626_);
lean_dec(v_x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_a_626_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_a_627_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_x_625_);
return v___x_637_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_638_){
_start:
{
switch(lean_obj_tag(v_x_638_))
{
case 3:
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v_x_638_, 1);
v_x_638_ = v_a_639_;
goto _start;
}
case 4:
{
lean_object* v_a_641_; 
v_a_641_ = lean_ctor_get(v_x_638_, 1);
v_x_638_ = v_a_641_;
goto _start;
}
case 8:
{
lean_object* v_a_643_; 
v_a_643_ = lean_ctor_get(v_x_638_, 1);
v_x_638_ = v_a_643_;
goto _start;
}
case 9:
{
uint8_t v___x_645_; 
v___x_645_ = 1;
return v___x_645_;
}
case 11:
{
lean_object* v_a_646_; 
v_a_646_ = lean_ctor_get(v_x_638_, 1);
v_x_638_ = v_a_646_;
goto _start;
}
default: 
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_MessageData_isTrace(v_x_649_);
lean_dec_ref(v_x_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
switch(lean_obj_tag(v_x_652_))
{
case 3:
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_a_654_ = lean_ctor_get(v_x_652_, 0);
v_a_655_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v_x_652_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_inc(v_a_654_);
lean_dec(v_x_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = l_Lean_MessageData_composePreservingKind(v_a_655_, v_x_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_654_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
case 4:
{
lean_object* v_a_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_a_664_ = lean_ctor_get(v_x_652_, 0);
v_a_665_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_673_ == 0)
{
v___x_667_ = v_x_652_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_inc(v_a_664_);
lean_dec(v_x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_MessageData_composePreservingKind(v_a_665_, v_x_653_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_664_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
case 8:
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_a_674_ = lean_ctor_get(v_x_652_, 0);
v_a_675_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v_x_652_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_inc(v_a_674_);
lean_dec(v_x_652_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 7);
lean_ctor_set(v___x_677_, 1, v_x_653_);
lean_ctor_set(v___x_677_, 0, v_a_675_);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_x_653_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_681_, 0, v_a_674_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
}
}
case 11:
{
lean_object* v_a_684_; lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_a_684_ = lean_ctor_get(v_x_652_, 0);
v_a_685_ = lean_ctor_get(v_x_652_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v_x_652_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_inc(v_a_684_);
lean_dec(v_x_652_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Lean_MessageData_composePreservingKind(v_a_685_, v_x_653_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_684_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
default: 
{
lean_object* v___x_694_; 
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v_x_652_);
lean_ctor_set(v___x_694_, 1, v_x_653_);
return v___x_694_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_Lean_MessageData_ofFormat(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_698_, lean_object* v_ctx_699_){
_start:
{
lean_object* v_env_700_; lean_object* v_mctx_701_; lean_object* v_lctx_702_; lean_object* v_opts_703_; lean_object* v_currNamespace_704_; lean_object* v_openDecls_705_; lean_object* v___x_706_; 
v_env_700_ = lean_ctor_get(v_ctx_699_, 0);
v_mctx_701_ = lean_ctor_get(v_ctx_699_, 1);
v_lctx_702_ = lean_ctor_get(v_ctx_699_, 2);
v_opts_703_ = lean_ctor_get(v_ctx_699_, 3);
v_currNamespace_704_ = lean_ctor_get(v_nCtx_698_, 0);
v_openDecls_705_ = lean_ctor_get(v_nCtx_698_, 1);
lean_inc(v_openDecls_705_);
lean_inc(v_currNamespace_704_);
lean_inc_ref(v_opts_703_);
lean_inc_ref(v_lctx_702_);
lean_inc_ref(v_mctx_701_);
lean_inc_ref(v_env_700_);
v___x_706_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_706_, 0, v_env_700_);
lean_ctor_set(v___x_706_, 1, v_mctx_701_);
lean_ctor_set(v___x_706_, 2, v_lctx_702_);
lean_ctor_set(v___x_706_, 3, v_opts_703_);
lean_ctor_set(v___x_706_, 4, v_currNamespace_704_);
lean_ctor_set(v___x_706_, 5, v_openDecls_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_707_, lean_object* v_ctx_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MessageData_mkPPContext(v_nCtx_707_, v_ctx_708_);
lean_dec_ref(v_ctx_708_);
lean_dec_ref(v_nCtx_707_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_712_);
lean_dec_ref(v_x_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_715_, lean_object* v_stx_716_, lean_object* v_ctx_x3f_717_){
_start:
{
lean_object* v_val_720_; 
if (lean_obj_tag(v_ctx_x3f_717_) == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_box(0);
v___x_724_ = 0;
v___x_725_ = l_Lean_Syntax_formatStx(v_stx_716_, v___x_723_, v___x_724_);
v_val_720_ = v___x_725_;
goto v___jp_719_;
}
else
{
lean_object* v_val_726_; lean_object* v___x_727_; 
v_val_726_ = lean_ctor_get(v_ctx_x3f_717_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_ctx_x3f_717_, 1);
v___x_727_ = l_Lean_ppTerm(v_val_726_, v_stx_716_);
v_val_720_ = v___x_727_;
goto v___jp_719_;
}
v___jp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l_Lean_MessageData_ofFormat(v_val_720_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_715_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_728_, lean_object* v_stx_729_, lean_object* v_ctx_x3f_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_728_, v_stx_729_, v_ctx_x3f_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_734_){
_start:
{
lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_stx_738_; lean_object* v___f_739_; lean_object* v___x_740_; 
v___f_735_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_736_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_737_ = lean_box(0);
v_stx_738_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_734_, v___x_737_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_739_, 0, v___x_736_);
lean_closure_set(v___f_739_, 1, v_stx_738_);
v___x_740_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_740_, 0, v___f_739_);
lean_ctor_set(v___x_740_, 1, v___f_735_);
return v___x_740_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_741_, lean_object* v_mctx_742_){
_start:
{
lean_object* v___x_743_; lean_object* v_fst_744_; uint8_t v___x_745_; 
v___x_743_ = l_Lean_instantiateMVarsCore(v_mctx_742_, v_e_741_);
v_fst_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_fst_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = l_Lean_Expr_hasSyntheticSorry(v_fst_744_);
lean_dec(v_fst_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_746_, lean_object* v_mctx_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_Lean_MessageData_ofExpr___lam__0(v_e_746_, v_mctx_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_750_, lean_object* v_e_751_, lean_object* v_ctx_x3f_752_){
_start:
{
lean_object* v_val_755_; 
if (lean_obj_tag(v_ctx_x3f_752_) == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_expr_dbg_to_string(v_e_751_);
lean_dec_ref(v_e_751_);
v___x_759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = lean_box(1);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v_val_755_ = v___x_761_;
goto v___jp_754_;
}
else
{
lean_object* v_val_762_; lean_object* v___x_763_; 
v_val_762_ = lean_ctor_get(v_ctx_x3f_752_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_ctx_x3f_752_, 1);
v___x_763_ = l_Lean_ppExprWithInfos(v_val_762_, v_e_751_);
v_val_755_ = v___x_763_;
goto v___jp_754_;
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_val_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_750_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_764_, lean_object* v_e_765_, lean_object* v_ctx_x3f_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_MessageData_ofExpr___lam__1(v___x_764_, v_e_765_, v_ctx_x3f_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_769_){
_start:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
lean_inc_ref(v_e_769_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_770_, 0, v_e_769_);
v___x_771_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_772_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_772_, 0, v___x_771_);
lean_closure_set(v___f_772_, 1, v_e_769_);
v___x_773_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_773_, 0, v___f_772_);
lean_ctor_set(v___x_773_, 1, v___f_770_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(0);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_MessageData_ofLevel___lam__0(v_x_776_);
lean_dec(v_x_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_778_, lean_object* v_l_779_, lean_object* v___f_780_, lean_object* v_ctx_x3f_781_){
_start:
{
lean_object* v_val_784_; 
if (lean_obj_tag(v_ctx_x3f_781_) == 0)
{
uint8_t v___x_787_; lean_object* v___x_788_; 
v___x_787_ = 1;
v___x_788_ = l_Lean_Level_format(v_l_779_, v___x_787_, v___f_780_);
v_val_784_ = v___x_788_;
goto v___jp_783_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_790_; 
lean_dec_ref(v___f_780_);
v_val_789_ = lean_ctor_get(v_ctx_x3f_781_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_ctx_x3f_781_, 1);
v___x_790_ = l_Lean_ppLevel(v_val_789_, v_l_779_);
v_val_784_ = v___x_790_;
goto v___jp_783_;
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = l_Lean_MessageData_ofFormat(v_val_784_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_778_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_791_, lean_object* v_l_792_, lean_object* v___f_793_, lean_object* v_ctx_x3f_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MessageData_ofLevel___lam__2(v___x_791_, v_l_792_, v___f_793_, v_ctx_x3f_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_798_){
_start:
{
lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; 
v___f_799_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_800_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_801_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_802_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_802_, 0, v___x_801_);
lean_closure_set(v___f_802_, 1, v_l_798_);
lean_closure_set(v___f_802_, 2, v___f_799_);
v___x_803_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_803_, 0, v___f_802_);
lean_ctor_set(v___x_803_, 1, v___f_800_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_804_){
_start:
{
uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = 1;
v___x_806_ = l_Lean_Name_toString(v_n_804_, v___x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_MessageData_ofFormat(v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_812_, lean_object* v_k_813_, uint8_t v_v_814_){
_start:
{
lean_object* v_map_815_; uint8_t v_hasTrace_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_830_; 
v_map_815_ = lean_ctor_get(v_o_812_, 0);
v_hasTrace_816_ = lean_ctor_get_uint8(v_o_812_, sizeof(void*)*1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_o_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_818_ = v_o_812_;
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_map_815_);
lean_dec(v_o_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_820_, 0, v_v_814_);
lean_inc(v_k_813_);
v___x_821_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_813_, v___x_820_, v_map_815_);
if (v_hasTrace_816_ == 0)
{
lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_825_; 
v___x_822_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_823_ = l_Lean_Name_isPrefixOf(v___x_822_, v_k_813_);
lean_dec(v_k_813_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_821_);
v___x_825_ = v___x_818_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_821_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v___x_823_);
return v___x_825_;
}
}
else
{
lean_object* v___x_828_; 
lean_dec(v_k_813_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_821_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_829_, sizeof(void*)*1, v_hasTrace_816_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_831_, lean_object* v_k_832_, lean_object* v_v_833_){
_start:
{
uint8_t v_v_boxed_834_; lean_object* v_res_835_; 
v_v_boxed_834_ = lean_unbox(v_v_833_);
v_res_835_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_831_, v_k_832_, v_v_boxed_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_841_, lean_object* v_constName_842_, uint8_t v_fullNames_843_, lean_object* v_ctx_x3f_844_){
_start:
{
lean_object* v_val_847_; lean_object* v___y_851_; 
if (lean_obj_tag(v_ctx_x3f_844_) == 0)
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = 1;
v___x_853_ = l_Lean_Name_toString(v_constName_842_, v___x_852_);
v___x_854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___x_855_ = lean_box(1);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v_val_847_ = v___x_856_;
goto v___jp_846_;
}
else
{
if (v_fullNames_843_ == 0)
{
lean_object* v_val_857_; lean_object* v___x_858_; 
v_val_857_ = lean_ctor_get(v_ctx_x3f_844_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v_ctx_x3f_844_, 1);
v___x_858_ = l_Lean_ppConstNameWithInfos(v_val_857_, v_constName_842_);
v___y_851_ = v___x_858_;
goto v___jp_850_;
}
else
{
lean_object* v_val_859_; lean_object* v_env_860_; lean_object* v_mctx_861_; lean_object* v_lctx_862_; lean_object* v_opts_863_; lean_object* v_currNamespace_864_; lean_object* v_openDecls_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_875_; 
v_val_859_ = lean_ctor_get(v_ctx_x3f_844_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_ctx_x3f_844_, 1);
v_env_860_ = lean_ctor_get(v_val_859_, 0);
v_mctx_861_ = lean_ctor_get(v_val_859_, 1);
v_lctx_862_ = lean_ctor_get(v_val_859_, 2);
v_opts_863_ = lean_ctor_get(v_val_859_, 3);
v_currNamespace_864_ = lean_ctor_get(v_val_859_, 4);
v_openDecls_865_ = lean_ctor_get(v_val_859_, 5);
v_isSharedCheck_875_ = !lean_is_exclusive(v_val_859_);
if (v_isSharedCheck_875_ == 0)
{
v___x_867_ = v_val_859_;
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_openDecls_865_);
lean_inc(v_currNamespace_864_);
lean_inc(v_opts_863_);
lean_inc(v_lctx_862_);
lean_inc(v_mctx_861_);
lean_inc(v_env_860_);
lean_dec(v_val_859_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_870_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_863_, v___x_869_, v_fullNames_843_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 3, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_env_860_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_mctx_861_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_lctx_862_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v_currNamespace_864_);
lean_ctor_set(v_reuseFailAlloc_874_, 5, v_openDecls_865_);
v___x_872_ = v_reuseFailAlloc_874_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_ppConstNameWithInfos(v___x_872_, v_constName_842_);
v___y_851_ = v___x_873_;
goto v___jp_850_;
}
}
}
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_val_847_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_841_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
v___jp_850_:
{
v_val_847_ = v___y_851_;
goto v___jp_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_876_, lean_object* v_constName_877_, lean_object* v_fullNames_878_, lean_object* v_ctx_x3f_879_, lean_object* v___y_880_){
_start:
{
uint8_t v_fullNames_boxed_881_; lean_object* v_res_882_; 
v_fullNames_boxed_881_ = lean_unbox(v_fullNames_878_);
v_res_882_ = l_Lean_MessageData_ofConstName___lam__1(v___x_876_, v_constName_877_, v_fullNames_boxed_881_, v_ctx_x3f_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_883_, uint8_t v_fullNames_884_){
_start:
{
lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
v___f_885_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_886_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_887_ = lean_box(v_fullNames_884_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_888_, 0, v___x_886_);
lean_closure_set(v___f_888_, 1, v_constName_883_);
lean_closure_set(v___f_888_, 2, v___x_887_);
v___x_889_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_889_, 0, v___f_888_);
lean_ctor_set(v___x_889_, 1, v___f_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_890_, lean_object* v_fullNames_891_){
_start:
{
uint8_t v_fullNames_boxed_892_; lean_object* v_res_893_; 
v_fullNames_boxed_892_ = lean_unbox(v_fullNames_891_);
v_res_893_ = l_Lean_MessageData_ofConstName(v_constName_890_, v_fullNames_boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_val_894_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_MessageData_withExprHover___lam__0(v_val_898_, v___y_899_);
lean_dec_ref(v___y_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_902_, lean_object* v_v_903_, lean_object* v_t_904_){
_start:
{
if (lean_obj_tag(v_t_904_) == 0)
{
lean_object* v_size_905_; lean_object* v_k_906_; lean_object* v_v_907_; lean_object* v_l_908_; lean_object* v_r_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_1190_; 
v_size_905_ = lean_ctor_get(v_t_904_, 0);
v_k_906_ = lean_ctor_get(v_t_904_, 1);
v_v_907_ = lean_ctor_get(v_t_904_, 2);
v_l_908_ = lean_ctor_get(v_t_904_, 3);
v_r_909_ = lean_ctor_get(v_t_904_, 4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_t_904_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_911_ = v_t_904_;
v_isShared_912_ = v_isSharedCheck_1190_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_r_909_);
lean_inc(v_l_908_);
lean_inc(v_v_907_);
lean_inc(v_k_906_);
lean_inc(v_size_905_);
lean_dec(v_t_904_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_1190_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; 
v___x_913_ = lean_nat_dec_lt(v_k_902_, v_k_906_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_eq(v_k_902_, v_k_906_);
if (v___x_914_ == 0)
{
lean_object* v_impl_915_; lean_object* v___x_916_; 
lean_dec(v_size_905_);
v_impl_915_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_902_, v_v_903_, v_r_909_);
v___x_916_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_908_) == 0)
{
lean_object* v_size_917_; lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_size_917_ = lean_ctor_get(v_l_908_, 0);
v_size_918_ = lean_ctor_get(v_impl_915_, 0);
lean_inc(v_size_918_);
v_k_919_ = lean_ctor_get(v_impl_915_, 1);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v_impl_915_, 2);
lean_inc(v_v_920_);
v_l_921_ = lean_ctor_get(v_impl_915_, 3);
lean_inc(v_l_921_);
v_r_922_ = lean_ctor_get(v_impl_915_, 4);
lean_inc(v_r_922_);
v___x_923_ = lean_unsigned_to_nat(3u);
v___x_924_ = lean_nat_mul(v___x_923_, v_size_917_);
v___x_925_ = lean_nat_dec_lt(v___x_924_, v_size_918_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
lean_dec(v_r_922_);
lean_dec(v_l_921_);
lean_dec(v_v_920_);
lean_dec(v_k_919_);
v___x_926_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_927_ = lean_nat_add(v___x_926_, v_size_918_);
lean_dec(v_size_918_);
lean_dec(v___x_926_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_impl_915_);
lean_ctor_set(v___x_911_, 0, v___x_927_);
v___x_929_ = v___x_911_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_l_908_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_impl_915_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_994_; 
v_isSharedCheck_994_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_impl_915_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_impl_915_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_impl_915_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_999_);
v___x_932_ = v_impl_915_;
v_isShared_933_ = v_isSharedCheck_994_;
goto v_resetjp_931_;
}
else
{
lean_dec(v_impl_915_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_994_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_size_934_; lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_l_937_; lean_object* v_r_938_; lean_object* v_size_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_size_934_ = lean_ctor_get(v_l_921_, 0);
v_k_935_ = lean_ctor_get(v_l_921_, 1);
v_v_936_ = lean_ctor_get(v_l_921_, 2);
v_l_937_ = lean_ctor_get(v_l_921_, 3);
v_r_938_ = lean_ctor_get(v_l_921_, 4);
v_size_939_ = lean_ctor_get(v_r_922_, 0);
v___x_940_ = lean_unsigned_to_nat(2u);
v___x_941_ = lean_nat_mul(v___x_940_, v_size_939_);
v___x_942_ = lean_nat_dec_lt(v_size_934_, v___x_941_);
lean_dec(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_970_; 
lean_inc(v_r_938_);
lean_inc(v_l_937_);
lean_inc(v_v_936_);
lean_inc(v_k_935_);
v_isSharedCheck_970_ = !lean_is_exclusive(v_l_921_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_971_ = lean_ctor_get(v_l_921_, 4);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_l_921_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_921_, 2);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_l_921_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_921_, 0);
lean_dec(v_unused_975_);
v___x_944_ = v_l_921_;
v_isShared_945_ = v_isSharedCheck_970_;
goto v_resetjp_943_;
}
else
{
lean_dec(v_l_921_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_970_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_960_; 
v___x_946_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_947_ = lean_nat_add(v___x_946_, v_size_918_);
lean_dec(v_size_918_);
if (lean_obj_tag(v_l_937_) == 0)
{
lean_object* v_size_968_; 
v_size_968_ = lean_ctor_get(v_l_937_, 0);
lean_inc(v_size_968_);
v___y_960_ = v_size_968_;
goto v___jp_959_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___y_960_ = v___x_969_;
goto v___jp_959_;
}
v___jp_948_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec(v___y_950_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_r_922_);
lean_ctor_set(v___x_944_, 3, v_r_938_);
lean_ctor_set(v___x_944_, 2, v_v_920_);
lean_ctor_set(v___x_944_, 1, v_k_919_);
lean_ctor_set(v___x_944_, 0, v___x_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_r_938_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_922_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v___x_954_);
lean_ctor_set(v___x_932_, 3, v___y_949_);
lean_ctor_set(v___x_932_, 2, v_v_936_);
lean_ctor_set(v___x_932_, 1, v_k_935_);
lean_ctor_set(v___x_932_, 0, v___x_947_);
v___x_956_ = v___x_932_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_935_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v___y_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_nat_add(v___x_946_, v___y_960_);
lean_dec(v___y_960_);
lean_dec(v___x_946_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_l_937_);
lean_ctor_set(v___x_911_, 0, v___x_961_);
v___x_963_ = v___x_911_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_908_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_l_937_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_nat_add(v___x_916_, v_size_939_);
if (lean_obj_tag(v_r_938_) == 0)
{
lean_object* v_size_965_; 
v_size_965_ = lean_ctor_get(v_r_938_, 0);
lean_inc(v_size_965_);
v___y_949_ = v___x_963_;
v___y_950_ = v___x_964_;
v___y_951_ = v_size_965_;
goto v___jp_948_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___y_949_ = v___x_963_;
v___y_950_ = v___x_964_;
v___y_951_ = v___x_966_;
goto v___jp_948_;
}
}
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
lean_del_object(v___x_911_);
v___x_976_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_977_ = lean_nat_add(v___x_976_, v_size_918_);
lean_dec(v_size_918_);
v___x_978_ = lean_nat_add(v___x_976_, v_size_934_);
lean_dec(v___x_976_);
lean_inc_ref(v_l_908_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v_l_921_);
lean_ctor_set(v___x_932_, 3, v_l_908_);
lean_ctor_set(v___x_932_, 2, v_v_907_);
lean_ctor_set(v___x_932_, 1, v_k_906_);
lean_ctor_set(v___x_932_, 0, v___x_978_);
v___x_980_ = v___x_932_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_908_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_l_921_);
v___x_980_ = v_reuseFailAlloc_993_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v_l_908_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_988_ = lean_ctor_get(v_l_908_, 4);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_908_, 3);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_908_, 2);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_l_908_, 1);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_908_, 0);
lean_dec(v_unused_992_);
v___x_982_ = v_l_908_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_l_908_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v_r_922_);
lean_ctor_set(v___x_982_, 3, v___x_980_);
lean_ctor_set(v___x_982_, 2, v_v_920_);
lean_ctor_set(v___x_982_, 1, v_k_919_);
lean_ctor_set(v___x_982_, 0, v___x_977_);
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_r_922_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1000_; 
v_l_1000_ = lean_ctor_get(v_impl_915_, 3);
lean_inc(v_l_1000_);
if (lean_obj_tag(v_l_1000_) == 0)
{
lean_object* v_r_1001_; lean_object* v_k_1002_; lean_object* v_v_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1026_; 
v_r_1001_ = lean_ctor_get(v_impl_915_, 4);
v_k_1002_ = lean_ctor_get(v_impl_915_, 1);
v_v_1003_ = lean_ctor_get(v_impl_915_, 2);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; 
v_unused_1027_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_1028_);
v___x_1005_ = v_impl_915_;
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_r_1001_);
lean_inc(v_v_1003_);
lean_inc(v_k_1002_);
lean_dec(v_impl_915_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_k_1007_; lean_object* v_v_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1022_; 
v_k_1007_ = lean_ctor_get(v_l_1000_, 1);
v_v_1008_ = lean_ctor_get(v_l_1000_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_l_1000_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; 
v_unused_1023_ = lean_ctor_get(v_l_1000_, 4);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_1000_, 3);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_1000_, 0);
lean_dec(v_unused_1025_);
v___x_1010_ = v_l_1000_;
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_v_1008_);
lean_inc(v_k_1007_);
lean_dec(v_l_1000_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1001_, 2);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v_r_1001_);
lean_ctor_set(v___x_1010_, 3, v_r_1001_);
lean_ctor_set(v___x_1010_, 2, v_v_907_);
lean_ctor_set(v___x_1010_, 1, v_k_906_);
lean_ctor_set(v___x_1010_, 0, v___x_916_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_r_1001_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_r_1001_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
lean_inc(v_r_1001_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 3, v_r_1001_);
lean_ctor_set(v___x_1005_, 0, v___x_916_);
v___x_1016_ = v___x_1005_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_1002_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_r_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_r_1001_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_1016_);
lean_ctor_set(v___x_911_, 3, v___x_1014_);
lean_ctor_set(v___x_911_, 2, v_v_1008_);
lean_ctor_set(v___x_911_, 1, v_k_1007_);
lean_ctor_set(v___x_911_, 0, v___x_1012_);
v___x_1018_ = v___x_911_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_object* v_r_1029_; 
v_r_1029_ = lean_ctor_get(v_impl_915_, 4);
lean_inc(v_r_1029_);
if (lean_obj_tag(v_r_1029_) == 0)
{
lean_object* v_k_1030_; lean_object* v_v_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
v_k_1030_ = lean_ctor_get(v_impl_915_, 1);
v_v_1031_ = lean_ctor_get(v_impl_915_, 2);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v_impl_915_, 4);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_1045_);
v___x_1033_ = v_impl_915_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_v_1031_);
lean_inc(v_k_1030_);
lean_dec(v_impl_915_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_unsigned_to_nat(3u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1000_);
lean_ctor_set(v___x_1033_, 2, v_v_907_);
lean_ctor_set(v___x_1033_, 1, v_k_906_);
lean_ctor_set(v___x_1033_, 0, v___x_916_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_l_1000_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_l_1000_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_r_1029_);
lean_ctor_set(v___x_911_, 3, v___x_1037_);
lean_ctor_set(v___x_911_, 2, v_v_1031_);
lean_ctor_set(v___x_911_, 1, v_k_1030_);
lean_ctor_set(v___x_911_, 0, v___x_1035_);
v___x_1039_ = v___x_911_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_1030_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_1031_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_r_1029_);
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
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(2u);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_impl_915_);
lean_ctor_set(v___x_911_, 3, v_r_1029_);
lean_ctor_set(v___x_911_, 0, v___x_1046_);
v___x_1048_ = v___x_911_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_r_1029_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_impl_915_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v_v_907_);
lean_dec(v_k_906_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 2, v_v_903_);
lean_ctor_set(v___x_911_, 1, v_k_902_);
v___x_1051_ = v___x_911_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_905_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_k_902_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_v_903_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_l_908_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_r_909_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_impl_1053_; lean_object* v___x_1054_; 
lean_dec(v_size_905_);
v_impl_1053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_902_, v_v_903_, v_l_908_);
v___x_1054_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_909_) == 0)
{
lean_object* v_size_1055_; lean_object* v_size_1056_; lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v_l_1059_; lean_object* v_r_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_size_1055_ = lean_ctor_get(v_r_909_, 0);
v_size_1056_ = lean_ctor_get(v_impl_1053_, 0);
lean_inc(v_size_1056_);
v_k_1057_ = lean_ctor_get(v_impl_1053_, 1);
lean_inc(v_k_1057_);
v_v_1058_ = lean_ctor_get(v_impl_1053_, 2);
lean_inc(v_v_1058_);
v_l_1059_ = lean_ctor_get(v_impl_1053_, 3);
lean_inc(v_l_1059_);
v_r_1060_ = lean_ctor_get(v_impl_1053_, 4);
lean_inc(v_r_1060_);
v___x_1061_ = lean_unsigned_to_nat(3u);
v___x_1062_ = lean_nat_mul(v___x_1061_, v_size_1055_);
v___x_1063_ = lean_nat_dec_lt(v___x_1062_, v_size_1056_);
lean_dec(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec(v_r_1060_);
lean_dec(v_l_1059_);
lean_dec(v_v_1058_);
lean_dec(v_k_1057_);
v___x_1064_ = lean_nat_add(v___x_1054_, v_size_1056_);
lean_dec(v_size_1056_);
v___x_1065_ = lean_nat_add(v___x_1064_, v_size_1055_);
lean_dec(v___x_1064_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 3, v_impl_1053_);
lean_ctor_set(v___x_911_, 0, v___x_1065_);
v___x_1067_ = v___x_911_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_impl_1053_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_r_909_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1134_; 
v_isSharedCheck_1134_ = !lean_is_exclusive(v_impl_1053_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1135_ = lean_ctor_get(v_impl_1053_, 4);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1053_, 3);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1053_, 2);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_impl_1053_, 1);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_impl_1053_, 0);
lean_dec(v_unused_1139_);
v___x_1070_ = v_impl_1053_;
v_isShared_1071_ = v_isSharedCheck_1134_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v_impl_1053_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1134_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_size_1072_; lean_object* v_size_1073_; lean_object* v_k_1074_; lean_object* v_v_1075_; lean_object* v_l_1076_; lean_object* v_r_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_size_1072_ = lean_ctor_get(v_l_1059_, 0);
v_size_1073_ = lean_ctor_get(v_r_1060_, 0);
v_k_1074_ = lean_ctor_get(v_r_1060_, 1);
v_v_1075_ = lean_ctor_get(v_r_1060_, 2);
v_l_1076_ = lean_ctor_get(v_r_1060_, 3);
v_r_1077_ = lean_ctor_get(v_r_1060_, 4);
v___x_1078_ = lean_unsigned_to_nat(2u);
v___x_1079_ = lean_nat_mul(v___x_1078_, v_size_1072_);
v___x_1080_ = lean_nat_dec_lt(v_size_1073_, v___x_1079_);
lean_dec(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1109_; 
lean_inc(v_r_1077_);
lean_inc(v_l_1076_);
lean_inc(v_v_1075_);
lean_inc(v_k_1074_);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1110_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_r_1060_, 2);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_r_1060_, 1);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1114_);
v___x_1082_ = v_r_1060_;
v_isShared_1083_ = v_isSharedCheck_1109_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_r_1060_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1109_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___x_1097_; lean_object* v___y_1099_; 
v___x_1084_ = lean_nat_add(v___x_1054_, v_size_1056_);
lean_dec(v_size_1056_);
v___x_1085_ = lean_nat_add(v___x_1084_, v_size_1055_);
lean_dec(v___x_1084_);
v___x_1097_ = lean_nat_add(v___x_1054_, v_size_1072_);
if (lean_obj_tag(v_l_1076_) == 0)
{
lean_object* v_size_1107_; 
v_size_1107_ = lean_ctor_get(v_l_1076_, 0);
lean_inc(v_size_1107_);
v___y_1099_ = v_size_1107_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___y_1099_ = v___x_1108_;
goto v___jp_1098_;
}
v___jp_1086_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_nat_add(v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 4, v_r_909_);
lean_ctor_set(v___x_1082_, 3, v_r_1077_);
lean_ctor_set(v___x_1082_, 2, v_v_907_);
lean_ctor_set(v___x_1082_, 1, v_k_906_);
lean_ctor_set(v___x_1082_, 0, v___x_1090_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_r_1077_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_r_909_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 4, v___x_1092_);
lean_ctor_set(v___x_1070_, 3, v___y_1087_);
lean_ctor_set(v___x_1070_, 2, v_v_1075_);
lean_ctor_set(v___x_1070_, 1, v_k_1074_);
lean_ctor_set(v___x_1070_, 0, v___x_1085_);
v___x_1094_ = v___x_1070_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1074_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1075_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v___y_1087_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
v___jp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = lean_nat_add(v___x_1097_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec(v___x_1097_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_l_1076_);
lean_ctor_set(v___x_911_, 3, v_l_1059_);
lean_ctor_set(v___x_911_, 2, v_v_1058_);
lean_ctor_set(v___x_911_, 1, v_k_1057_);
lean_ctor_set(v___x_911_, 0, v___x_1100_);
v___x_1102_ = v___x_911_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_l_1076_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_nat_add(v___x_1054_, v_size_1055_);
if (lean_obj_tag(v_r_1077_) == 0)
{
lean_object* v_size_1104_; 
v_size_1104_ = lean_ctor_get(v_r_1077_, 0);
lean_inc(v_size_1104_);
v___y_1087_ = v___x_1102_;
v___y_1088_ = v___x_1103_;
v___y_1089_ = v_size_1104_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___y_1087_ = v___x_1102_;
v___y_1088_ = v___x_1103_;
v___y_1089_ = v___x_1105_;
goto v___jp_1086_;
}
}
}
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_del_object(v___x_911_);
v___x_1115_ = lean_nat_add(v___x_1054_, v_size_1056_);
lean_dec(v_size_1056_);
v___x_1116_ = lean_nat_add(v___x_1115_, v_size_1055_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_nat_add(v___x_1054_, v_size_1055_);
v___x_1118_ = lean_nat_add(v___x_1117_, v_size_1073_);
lean_dec(v___x_1117_);
lean_inc_ref(v_r_909_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 4, v_r_909_);
lean_ctor_set(v___x_1070_, 3, v_r_1060_);
lean_ctor_set(v___x_1070_, 2, v_v_907_);
lean_ctor_set(v___x_1070_, 1, v_k_906_);
lean_ctor_set(v___x_1070_, 0, v___x_1118_);
v___x_1120_ = v___x_1070_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_r_1060_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_r_909_);
v___x_1120_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_isSharedCheck_1127_ = !lean_is_exclusive(v_r_909_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; lean_object* v_unused_1131_; lean_object* v_unused_1132_; 
v_unused_1128_ = lean_ctor_get(v_r_909_, 4);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_r_909_, 3);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_r_909_, 2);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_r_909_, 1);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_r_909_, 0);
lean_dec(v_unused_1132_);
v___x_1122_ = v_r_909_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_r_909_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v___x_1120_);
lean_ctor_set(v___x_1122_, 3, v_l_1059_);
lean_ctor_set(v___x_1122_, 2, v_v_1058_);
lean_ctor_set(v___x_1122_, 1, v_k_1057_);
lean_ctor_set(v___x_1122_, 0, v___x_1116_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v___x_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1140_; 
v_l_1140_ = lean_ctor_get(v_impl_1053_, 3);
lean_inc(v_l_1140_);
if (lean_obj_tag(v_l_1140_) == 0)
{
lean_object* v_r_1141_; lean_object* v_k_1142_; lean_object* v_v_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1154_; 
v_r_1141_ = lean_ctor_get(v_impl_1053_, 4);
v_k_1142_ = lean_ctor_get(v_impl_1053_, 1);
v_v_1143_ = lean_ctor_get(v_impl_1053_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_impl_1053_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1155_ = lean_ctor_get(v_impl_1053_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_impl_1053_, 0);
lean_dec(v_unused_1156_);
v___x_1145_ = v_impl_1053_;
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_r_1141_);
lean_inc(v_v_1143_);
lean_inc(v_k_1142_);
lean_dec(v_impl_1053_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1141_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 3, v_r_1141_);
lean_ctor_set(v___x_1145_, 2, v_v_907_);
lean_ctor_set(v___x_1145_, 1, v_k_906_);
lean_ctor_set(v___x_1145_, 0, v___x_1054_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_r_1141_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_r_1141_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_1149_);
lean_ctor_set(v___x_911_, 3, v_l_1140_);
lean_ctor_set(v___x_911_, 2, v_v_1143_);
lean_ctor_set(v___x_911_, 1, v_k_1142_);
lean_ctor_set(v___x_911_, 0, v___x_1147_);
v___x_1151_ = v___x_911_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1142_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_l_1140_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_r_1157_; 
v_r_1157_ = lean_ctor_get(v_impl_1053_, 4);
lean_inc(v_r_1157_);
if (lean_obj_tag(v_r_1157_) == 0)
{
lean_object* v_k_1158_; lean_object* v_v_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1182_; 
v_k_1158_ = lean_ctor_get(v_impl_1053_, 1);
v_v_1159_ = lean_ctor_get(v_impl_1053_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_impl_1053_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1183_ = lean_ctor_get(v_impl_1053_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_impl_1053_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_impl_1053_, 0);
lean_dec(v_unused_1185_);
v___x_1161_ = v_impl_1053_;
v_isShared_1162_ = v_isSharedCheck_1182_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_v_1159_);
lean_inc(v_k_1158_);
lean_dec(v_impl_1053_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1182_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_k_1163_; lean_object* v_v_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1178_; 
v_k_1163_ = lean_ctor_get(v_r_1157_, 1);
v_v_1164_ = lean_ctor_get(v_r_1157_, 2);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_r_1157_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1179_ = lean_ctor_get(v_r_1157_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_r_1157_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_r_1157_, 0);
lean_dec(v_unused_1181_);
v___x_1166_ = v_r_1157_;
v_isShared_1167_ = v_isSharedCheck_1178_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_v_1164_);
lean_inc(v_k_1163_);
lean_dec(v_r_1157_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1178_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_unsigned_to_nat(3u);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 4, v_l_1140_);
lean_ctor_set(v___x_1166_, 3, v_l_1140_);
lean_ctor_set(v___x_1166_, 2, v_v_1159_);
lean_ctor_set(v___x_1166_, 1, v_k_1158_);
lean_ctor_set(v___x_1166_, 0, v___x_1054_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_l_1140_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_l_1140_);
v___x_1170_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 4, v_l_1140_);
lean_ctor_set(v___x_1161_, 2, v_v_907_);
lean_ctor_set(v___x_1161_, 1, v_k_906_);
lean_ctor_set(v___x_1161_, 0, v___x_1054_);
v___x_1172_ = v___x_1161_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_l_1140_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_l_1140_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_1172_);
lean_ctor_set(v___x_911_, 3, v___x_1170_);
lean_ctor_set(v___x_911_, 2, v_v_1164_);
lean_ctor_set(v___x_911_, 1, v_k_1163_);
lean_ctor_set(v___x_911_, 0, v___x_1168_);
v___x_1174_ = v___x_911_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_k_1163_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_v_1164_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(2u);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_r_1157_);
lean_ctor_set(v___x_911_, 3, v_impl_1053_);
lean_ctor_set(v___x_911_, 0, v___x_1186_);
v___x_1188_ = v___x_911_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_impl_1053_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_r_1157_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_k_902_);
lean_ctor_set(v___x_1192_, 2, v_v_903_);
lean_ctor_set(v___x_1192_, 3, v_t_904_);
lean_ctor_set(v___x_1192_, 4, v_t_904_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1193_, lean_object* v_b_1194_){
_start:
{
if (lean_obj_tag(v_as_x27_1193_) == 0)
{
return v_b_1194_;
}
else
{
lean_object* v_head_1195_; lean_object* v_tail_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v_r_1199_; 
v_head_1195_ = lean_ctor_get(v_as_x27_1193_, 0);
v_tail_1196_ = lean_ctor_get(v_as_x27_1193_, 1);
v_fst_1197_ = lean_ctor_get(v_head_1195_, 0);
v_snd_1198_ = lean_ctor_get(v_head_1195_, 1);
lean_inc(v_snd_1198_);
lean_inc(v_fst_1197_);
v_r_1199_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1197_, v_snd_1198_, v_b_1194_);
v_as_x27_1193_ = v_tail_1196_;
v_b_1194_ = v_r_1199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1201_, lean_object* v_b_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1201_, v_b_1202_);
lean_dec(v_as_x27_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1212_, lean_object* v_expr_1213_, lean_object* v_lctx_1214_, lean_object* v_location_x3f_1215_, lean_object* v_docString_x3f_1216_, lean_object* v_mkDocString_x3f_1217_, uint8_t v_explicit_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___y_1226_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_fmt_1212_);
v___x_1221_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1222_ = lean_box(0);
v___x_1223_ = 0;
v___x_1224_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1224_, 0, v___x_1221_);
lean_ctor_set(v___x_1224_, 1, v_lctx_1214_);
lean_ctor_set(v___x_1224_, 2, v___x_1222_);
lean_ctor_set(v___x_1224_, 3, v_expr_1213_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*4, v___x_1223_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*4 + 1, v___x_1223_);
if (lean_obj_tag(v_mkDocString_x3f_1217_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1216_) == 0)
{
v___y_1226_ = v_mkDocString_x3f_1217_;
goto v___jp_1225_;
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_val_1236_ = lean_ctor_get(v_docString_x3f_1216_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_docString_x3f_1216_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1238_ = v_docString_x3f_1216_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v_docString_x3f_1216_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___f_1240_; lean_object* v___x_1242_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1240_, 0, v_val_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___f_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___f_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v___y_1226_ = v___x_1242_;
goto v___jp_1225_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1216_);
v___y_1226_ = v_mkDocString_x3f_1217_;
goto v___jp_1225_;
}
v___jp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_r_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1227_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1227_, 0, v___x_1224_);
lean_ctor_set(v___x_1227_, 1, v_location_x3f_1215_);
lean_ctor_set(v___x_1227_, 2, v___y_1226_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*3, v_explicit_1218_);
v___x_1228_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1219_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v_r_1232_ = lean_box(1);
v___x_1233_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1231_, v_r_1232_);
lean_dec_ref_known(v___x_1231_, 2);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1220_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1245_, lean_object* v_expr_1246_, lean_object* v_lctx_1247_, lean_object* v_location_x3f_1248_, lean_object* v_docString_x3f_1249_, lean_object* v_mkDocString_x3f_1250_, lean_object* v_explicit_1251_){
_start:
{
uint8_t v_explicit_boxed_1252_; lean_object* v_res_1253_; 
v_explicit_boxed_1252_ = lean_unbox(v_explicit_1251_);
v_res_1253_ = l_Lean_MessageData_withExprHover(v_fmt_1245_, v_expr_1246_, v_lctx_1247_, v_location_x3f_1248_, v_docString_x3f_1249_, v_mkDocString_x3f_1250_, v_explicit_boxed_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1254_, lean_object* v_k_1255_, lean_object* v_v_1256_, lean_object* v_t_1257_, lean_object* v_hl_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1255_, v_v_1256_, v_t_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1260_, lean_object* v_as_x27_1261_, lean_object* v_b_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1261_, v_b_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1265_, lean_object* v_as_x27_1266_, lean_object* v_b_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1265_, v_as_x27_1266_, v_b_1267_, v_a_1268_);
lean_dec(v_as_x27_1266_);
lean_dec(v_as_1265_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1270_, lean_object* v_expr_1271_, lean_object* v_location_x3f_1272_, lean_object* v_docString_x3f_1273_, lean_object* v_mkDocString_x3f_1274_, uint8_t v_explicit_1275_, lean_object* v_toPure_1276_, lean_object* v_lctx_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = l_Lean_MessageData_withExprHover(v_fmt_1270_, v_expr_1271_, v_lctx_1277_, v_location_x3f_1272_, v_docString_x3f_1273_, v_mkDocString_x3f_1274_, v_explicit_1275_);
v___x_1279_ = lean_apply_2(v_toPure_1276_, lean_box(0), v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1280_, lean_object* v_expr_1281_, lean_object* v_location_x3f_1282_, lean_object* v_docString_x3f_1283_, lean_object* v_mkDocString_x3f_1284_, lean_object* v_explicit_1285_, lean_object* v_toPure_1286_, lean_object* v_lctx_1287_){
_start:
{
uint8_t v_explicit_boxed_1288_; lean_object* v_res_1289_; 
v_explicit_boxed_1288_ = lean_unbox(v_explicit_1285_);
v_res_1289_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1280_, v_expr_1281_, v_location_x3f_1282_, v_docString_x3f_1283_, v_mkDocString_x3f_1284_, v_explicit_boxed_1288_, v_toPure_1286_, v_lctx_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_fmt_1292_, lean_object* v_expr_1293_, lean_object* v_lctx_x3f_1294_, lean_object* v_location_x3f_1295_, lean_object* v_docString_x3f_1296_, lean_object* v_mkDocString_x3f_1297_, uint8_t v_explicit_1298_){
_start:
{
lean_object* v_toApplicative_1299_; lean_object* v_toBind_1300_; lean_object* v_toPure_1301_; lean_object* v___x_1302_; lean_object* v___f_1303_; 
v_toApplicative_1299_ = lean_ctor_get(v_inst_1290_, 0);
lean_inc_ref(v_toApplicative_1299_);
v_toBind_1300_ = lean_ctor_get(v_inst_1290_, 1);
lean_inc(v_toBind_1300_);
lean_dec_ref(v_inst_1290_);
v_toPure_1301_ = lean_ctor_get(v_toApplicative_1299_, 1);
lean_inc_n(v_toPure_1301_, 2);
lean_dec_ref(v_toApplicative_1299_);
v___x_1302_ = lean_box(v_explicit_1298_);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1303_, 0, v_fmt_1292_);
lean_closure_set(v___f_1303_, 1, v_expr_1293_);
lean_closure_set(v___f_1303_, 2, v_location_x3f_1295_);
lean_closure_set(v___f_1303_, 3, v_docString_x3f_1296_);
lean_closure_set(v___f_1303_, 4, v_mkDocString_x3f_1297_);
lean_closure_set(v___f_1303_, 5, v___x_1302_);
lean_closure_set(v___f_1303_, 6, v_toPure_1301_);
if (lean_obj_tag(v_lctx_x3f_1294_) == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_toPure_1301_);
v___x_1304_ = lean_apply_4(v_toBind_1300_, lean_box(0), lean_box(0), v_inst_1291_, v___f_1303_);
return v___x_1304_;
}
else
{
lean_object* v_val_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v_inst_1291_);
v_val_1305_ = lean_ctor_get(v_lctx_x3f_1294_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v_lctx_x3f_1294_, 1);
v___x_1306_ = lean_apply_2(v_toPure_1301_, lean_box(0), v_val_1305_);
v___x_1307_ = lean_apply_4(v_toBind_1300_, lean_box(0), lean_box(0), v___x_1306_, v___f_1303_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_fmt_1310_, lean_object* v_expr_1311_, lean_object* v_lctx_x3f_1312_, lean_object* v_location_x3f_1313_, lean_object* v_docString_x3f_1314_, lean_object* v_mkDocString_x3f_1315_, lean_object* v_explicit_1316_){
_start:
{
uint8_t v_explicit_boxed_1317_; lean_object* v_res_1318_; 
v_explicit_boxed_1317_ = lean_unbox(v_explicit_1316_);
v_res_1318_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1308_, v_inst_1309_, v_fmt_1310_, v_expr_1311_, v_lctx_x3f_1312_, v_location_x3f_1313_, v_docString_x3f_1314_, v_mkDocString_x3f_1315_, v_explicit_boxed_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_fmt_1322_, lean_object* v_expr_1323_, lean_object* v_lctx_x3f_1324_, lean_object* v_location_x3f_1325_, lean_object* v_docString_x3f_1326_, lean_object* v_mkDocString_x3f_1327_, uint8_t v_explicit_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1320_, v_inst_1321_, v_fmt_1322_, v_expr_1323_, v_lctx_x3f_1324_, v_location_x3f_1325_, v_docString_x3f_1326_, v_mkDocString_x3f_1327_, v_explicit_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_fmt_1333_, lean_object* v_expr_1334_, lean_object* v_lctx_x3f_1335_, lean_object* v_location_x3f_1336_, lean_object* v_docString_x3f_1337_, lean_object* v_mkDocString_x3f_1338_, lean_object* v_explicit_1339_){
_start:
{
uint8_t v_explicit_boxed_1340_; lean_object* v_res_1341_; 
v_explicit_boxed_1340_ = lean_unbox(v_explicit_1339_);
v_res_1341_ = l_Lean_MessageData_withExprHoverM(v_m_1330_, v_inst_1331_, v_inst_1332_, v_fmt_1333_, v_expr_1334_, v_lctx_x3f_1335_, v_location_x3f_1336_, v_docString_x3f_1337_, v_mkDocString_x3f_1338_, v_explicit_boxed_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1342_, lean_object* v_display_1343_, lean_object* v_toPure_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_____do__lift_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1347_, v_userName_1342_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_inst_1346_);
lean_dec_ref(v_inst_1345_);
v___x_1349_ = l_Lean_MessageData_ofName(v_display_1343_);
v___x_1350_ = lean_apply_2(v_toPure_1344_, lean_box(0), v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_toPure_1344_);
v_val_1351_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1353_ = v___x_1348_;
v_isShared_1354_ = v_isSharedCheck_1365_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v___x_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1365_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = 1;
v___x_1356_ = l_Lean_Name_toString(v_display_1343_, v___x_1355_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 3);
lean_ctor_set(v___x_1353_, 0, v___x_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1359_ = l_Lean_LocalDecl_fvarId(v_val_1351_);
lean_dec(v_val_1351_);
v___x_1360_ = l_Lean_Expr_fvar___override(v___x_1359_);
v___x_1361_ = lean_box(0);
v___x_1362_ = 0;
v___x_1363_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1345_, v_inst_1346_, v___x_1358_, v___x_1360_, v___x_1361_, v___x_1361_, v___x_1361_, v___x_1361_, v___x_1362_);
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1366_, lean_object* v_display_1367_, lean_object* v_toPure_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_____do__lift_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1366_, v_display_1367_, v_toPure_1368_, v_inst_1369_, v_inst_1370_, v_____do__lift_1371_);
lean_dec_ref(v_____do__lift_1371_);
lean_dec(v_userName_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_userName_1375_){
_start:
{
lean_object* v_toApplicative_1376_; lean_object* v_toBind_1377_; lean_object* v_toPure_1378_; lean_object* v_display_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; 
v_toApplicative_1376_ = lean_ctor_get(v_inst_1373_, 0);
v_toBind_1377_ = lean_ctor_get(v_inst_1373_, 1);
lean_inc(v_toBind_1377_);
v_toPure_1378_ = lean_ctor_get(v_toApplicative_1376_, 1);
lean_inc(v_toPure_1378_);
lean_inc(v_userName_1375_);
v_display_1379_ = l_Lean_Name_simpMacroScopes(v_userName_1375_);
lean_inc(v_inst_1374_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1380_, 0, v_userName_1375_);
lean_closure_set(v___f_1380_, 1, v_display_1379_);
lean_closure_set(v___f_1380_, 2, v_toPure_1378_);
lean_closure_set(v___f_1380_, 3, v_inst_1373_);
lean_closure_set(v___f_1380_, 4, v_inst_1374_);
v___x_1381_ = lean_apply_4(v_toBind_1377_, lean_box(0), lean_box(0), v_inst_1374_, v___f_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_userName_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1383_, v_inst_1384_, v_userName_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1387_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
lean_ctor_set(v___x_1392_, 3, v___x_1391_);
lean_ctor_set(v___x_1392_, 4, v___x_1390_);
lean_ctor_set(v___x_1392_, 5, v___x_1390_);
lean_ctor_set(v___x_1392_, 6, v___x_1390_);
lean_ctor_set(v___x_1392_, 7, v___x_1390_);
lean_ctor_set(v___x_1392_, 8, v___x_1390_);
lean_ctor_set(v___x_1392_, 9, v___x_1390_);
lean_ctor_set(v___x_1392_, 10, v___x_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1393_, lean_object* v_a_1394_){
_start:
{
switch(lean_obj_tag(v_a_1394_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1393_) == 0)
{
lean_object* v_hasSyntheticSorry_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_hasSyntheticSorry_1395_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_hasSyntheticSorry_1395_);
lean_dec_ref_known(v_a_1394_, 2);
v___x_1396_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1397_ = lean_apply_1(v_hasSyntheticSorry_1395_, v___x_1396_);
v___x_1398_ = lean_unbox(v___x_1397_);
return v___x_1398_;
}
else
{
lean_object* v_hasSyntheticSorry_1399_; lean_object* v_val_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_hasSyntheticSorry_1399_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_hasSyntheticSorry_1399_);
lean_dec_ref_known(v_a_1394_, 2);
v_val_1400_ = lean_ctor_get(v_mctx_x3f_1393_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v_mctx_x3f_1393_, 1);
v___x_1401_ = lean_apply_1(v_hasSyntheticSorry_1399_, v_val_1400_);
v___x_1402_ = lean_unbox(v___x_1401_);
return v___x_1402_;
}
}
case 3:
{
lean_object* v_a_1403_; lean_object* v_a_1404_; lean_object* v_mctx_1405_; lean_object* v___x_1406_; 
lean_dec(v_mctx_x3f_1393_);
v_a_1403_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref(v_a_1403_);
v_a_1404_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1404_);
lean_dec_ref_known(v_a_1394_, 2);
v_mctx_1405_ = lean_ctor_get(v_a_1403_, 1);
lean_inc_ref(v_mctx_1405_);
lean_dec_ref(v_a_1403_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_mctx_1405_);
v_mctx_x3f_1393_ = v___x_1406_;
v_a_1394_ = v_a_1404_;
goto _start;
}
case 4:
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1408_);
lean_dec_ref_known(v_a_1394_, 2);
v_a_1394_ = v_a_1408_;
goto _start;
}
case 5:
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1410_);
lean_dec_ref_known(v_a_1394_, 2);
v_a_1394_ = v_a_1410_;
goto _start;
}
case 6:
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref(v_a_1412_);
lean_dec_ref_known(v_a_1394_, 1);
v_a_1394_ = v_a_1412_;
goto _start;
}
case 7:
{
lean_object* v_a_1414_; lean_object* v_a_1415_; uint8_t v___x_1416_; 
v_a_1414_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref(v_a_1414_);
v_a_1415_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1415_);
lean_dec_ref_known(v_a_1394_, 2);
lean_inc(v_mctx_x3f_1393_);
v___x_1416_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1393_, v_a_1414_);
if (v___x_1416_ == 0)
{
v_a_1394_ = v_a_1415_;
goto _start;
}
else
{
lean_dec_ref(v_a_1415_);
lean_dec(v_mctx_x3f_1393_);
return v___x_1416_;
}
}
case 8:
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1418_);
lean_dec_ref_known(v_a_1394_, 2);
v_a_1394_ = v_a_1418_;
goto _start;
}
case 11:
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_a_1420_);
lean_dec_ref_known(v_a_1394_, 2);
v_a_1394_ = v_a_1420_;
goto _start;
}
case 9:
{
lean_object* v_msg_1422_; lean_object* v_children_1423_; uint8_t v___x_1424_; 
v_msg_1422_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_msg_1422_);
v_children_1423_ = lean_ctor_get(v_a_1394_, 2);
lean_inc_ref(v_children_1423_);
lean_dec_ref_known(v_a_1394_, 3);
lean_inc(v_mctx_x3f_1393_);
v___x_1424_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1393_, v_msg_1422_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_array_get_size(v_children_1423_);
v___x_1427_ = lean_nat_dec_lt(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec_ref(v_children_1423_);
lean_dec(v_mctx_x3f_1393_);
return v___x_1427_;
}
else
{
if (v___x_1427_ == 0)
{
lean_dec_ref(v_children_1423_);
lean_dec(v_mctx_x3f_1393_);
return v___x_1427_;
}
else
{
size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1426_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1393_, v_children_1423_, v___x_1428_, v___x_1429_);
lean_dec_ref(v_children_1423_);
return v___x_1430_;
}
}
}
else
{
lean_dec_ref(v_children_1423_);
lean_dec(v_mctx_x3f_1393_);
return v___x_1424_;
}
}
default: 
{
uint8_t v___x_1431_; 
lean_dec_ref(v_a_1394_);
lean_dec(v_mctx_x3f_1393_);
v___x_1431_ = 0;
return v___x_1431_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1432_, lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_){
_start:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
lean_inc(v___x_1437_);
lean_inc(v_mctx_x3f_1432_);
v___x_1438_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1432_, v___x_1437_);
if (v___x_1438_ == 0)
{
size_t v___x_1439_; size_t v___x_1440_; 
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1434_, v___x_1439_);
v_i_1434_ = v___x_1440_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1432_);
return v___x_1438_;
}
}
else
{
uint8_t v___x_1442_; 
lean_dec(v_mctx_x3f_1432_);
v___x_1442_ = 0;
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1443_, lean_object* v_as_1444_, lean_object* v_i_1445_, lean_object* v_stop_1446_){
_start:
{
size_t v_i_boxed_1447_; size_t v_stop_boxed_1448_; uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_i_boxed_1447_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_stop_boxed_1448_ = lean_unbox_usize(v_stop_1446_);
lean_dec(v_stop_1446_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1443_, v_as_1444_, v_i_boxed_1447_, v_stop_boxed_1448_);
lean_dec_ref(v_as_1444_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1451_, lean_object* v_a_1452_){
_start:
{
uint8_t v_res_1453_; lean_object* v_r_1454_; 
v_res_1453_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1451_, v_a_1452_);
v_r_1454_ = lean_box(v_res_1453_);
return v_r_1454_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1455_){
_start:
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1456_, v_msg_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1458_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object* v_name_1461_, lean_object* v_decl_1462_, lean_object* v_ref_1463_){
_start:
{
lean_object* v_defValue_1465_; lean_object* v_descr_1466_; lean_object* v_deprecation_x3f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_defValue_1465_ = lean_ctor_get(v_decl_1462_, 0);
v_descr_1466_ = lean_ctor_get(v_decl_1462_, 1);
v_deprecation_x3f_1467_ = lean_ctor_get(v_decl_1462_, 2);
lean_inc(v_defValue_1465_);
v___x_1468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_defValue_1465_);
lean_inc(v_deprecation_x3f_1467_);
lean_inc_ref(v_descr_1466_);
lean_inc_n(v_name_1461_, 2);
v___x_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1469_, 0, v_name_1461_);
lean_ctor_set(v___x_1469_, 1, v_ref_1463_);
lean_ctor_set(v___x_1469_, 2, v___x_1468_);
lean_ctor_set(v___x_1469_, 3, v_descr_1466_);
lean_ctor_set(v___x_1469_, 4, v_deprecation_x3f_1467_);
v___x_1470_ = lean_register_option(v_name_1461_, v___x_1469_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1479_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_inc(v_defValue_1465_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_name_1461_);
lean_ctor_set(v___x_1474_, 1, v_defValue_1465_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_name_1461_);
v_a_1480_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1470_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1470_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1488_, lean_object* v_decl_1489_, lean_object* v_ref_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1488_, v_decl_1489_, v_ref_1490_);
lean_dec_ref(v_decl_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1507_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1508_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1509_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v___x_1506_, v___x_1507_, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_nat_to_int(v_a_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_box(0);
v___x_1515_ = l_instMonadBaseIO;
v___x_1516_ = l_instInhabitedOfMonad___redArg(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1807__overap_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1807__overap_1520_ = lean_panic_fn_borrowed(v___x_1519_, v_msg_1517_);
v___x_1521_ = lean_apply_1(v___x_1807__overap_1520_, lean_box(0));
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_dec(v_x_1525_);
return v_x_1526_;
}
else
{
lean_object* v_head_1528_; lean_object* v_tail_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
v_head_1528_ = lean_ctor_get(v_x_1527_, 0);
v_tail_1529_ = lean_ctor_get(v_x_1527_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v_x_1527_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_tail_1529_);
lean_inc(v_head_1528_);
lean_dec(v_x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
lean_inc(v_x_1525_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 5);
lean_ctor_set(v___x_1531_, 1, v_x_1525_);
lean_ctor_set(v___x_1531_, 0, v_x_1526_);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_x_1526_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_x_1525_);
v___x_1534_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_head_1528_);
v_x_1526_ = v___x_1535_;
v_x_1527_ = v_tail_1529_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_object* v___x_1541_; 
lean_dec(v_x_1540_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v_tail_1542_; 
v_tail_1542_ = lean_ctor_get(v_x_1539_, 1);
if (lean_obj_tag(v_tail_1542_) == 0)
{
lean_object* v_head_1543_; 
lean_dec(v_x_1540_);
v_head_1543_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_head_1543_);
lean_dec_ref_known(v_x_1539_, 2);
return v_head_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v___x_1545_; 
lean_inc(v_tail_1542_);
v_head_1544_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_head_1544_);
lean_dec_ref_known(v_x_1539_, 2);
v___x_1545_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1540_, v_head_1544_, v_tail_1542_);
return v___x_1545_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1560_; double v___x_1561_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_float_of_nat(v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
switch(lean_obj_tag(v_x_1567_))
{
case 0:
{
lean_object* v_a_1569_; lean_object* v_fmt_1570_; 
lean_dec(v_x_1566_);
lean_dec_ref(v_x_1565_);
v_a_1569_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_a_1569_);
lean_dec_ref_known(v_x_1567_, 1);
v_fmt_1570_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fmt_1570_);
lean_dec_ref(v_a_1569_);
return v_fmt_1570_;
}
case 1:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_x_1565_);
v_a_1571_ = lean_ctor_get(v_x_1567_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_x_1567_, 1);
v___x_1572_ = l_Lean_formatRawGoal(v_a_1571_);
return v___x_1572_;
}
else
{
lean_object* v_a_1573_; lean_object* v_val_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1573_ = lean_ctor_get(v_x_1567_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v_x_1567_, 1);
v_val_1574_ = lean_ctor_get(v_x_1566_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_x_1566_, 1);
v___x_1575_ = l_Lean_MessageData_mkPPContext(v_x_1565_, v_val_1574_);
lean_dec(v_val_1574_);
lean_dec_ref(v_x_1565_);
v___x_1576_ = l_Lean_ppGoal(v___x_1575_, v_a_1573_);
return v___x_1576_;
}
}
case 3:
{
lean_object* v_a_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; 
lean_dec(v_x_1566_);
v_a_1577_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_a_1577_);
v_a_1578_ = lean_ctor_get(v_x_1567_, 1);
lean_inc_ref(v_a_1578_);
lean_dec_ref_known(v_x_1567_, 2);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_a_1577_);
v_x_1566_ = v___x_1579_;
v_x_1567_ = v_a_1578_;
goto _start;
}
case 4:
{
lean_object* v_a_1581_; lean_object* v_a_1582_; 
lean_dec_ref(v_x_1565_);
v_a_1581_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_a_1581_);
v_a_1582_ = lean_ctor_get(v_x_1567_, 1);
lean_inc_ref(v_a_1582_);
lean_dec_ref_known(v_x_1567_, 2);
v_x_1565_ = v_a_1581_;
v_x_1567_ = v_a_1582_;
goto _start;
}
case 5:
{
lean_object* v_a_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1594_; 
v_a_1584_ = lean_ctor_get(v_x_1567_, 0);
v_a_1585_ = lean_ctor_get(v_x_1567_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1567_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1587_ = v_x_1567_;
v_isShared_1588_ = v_isSharedCheck_1594_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_inc(v_a_1584_);
lean_dec(v_x_1567_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1594_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = l_Lean_MessageData_formatAux(v_x_1565_, v_x_1566_, v_a_1585_);
v___x_1590_ = lean_nat_to_int(v_a_1584_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 4);
lean_ctor_set(v___x_1587_, 1, v___x_1589_);
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1589_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
case 6:
{
lean_object* v_a_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; 
v_a_1595_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_a_1595_);
lean_dec_ref_known(v_x_1567_, 1);
v___x_1596_ = l_Lean_MessageData_formatAux(v_x_1565_, v_x_1566_, v_a_1595_);
v___x_1597_ = 0;
v___x_1598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*1, v___x_1597_);
return v___x_1598_;
}
case 7:
{
lean_object* v_a_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1609_; 
v_a_1599_ = lean_ctor_get(v_x_1567_, 0);
v_a_1600_ = lean_ctor_get(v_x_1567_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1567_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1602_ = v_x_1567_;
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_inc(v_a_1599_);
lean_dec(v_x_1567_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_inc(v_x_1566_);
lean_inc_ref(v_x_1565_);
v___x_1604_ = l_Lean_MessageData_formatAux(v_x_1565_, v_x_1566_, v_a_1599_);
v___x_1605_ = l_Lean_MessageData_formatAux(v_x_1565_, v_x_1566_, v_a_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 5);
lean_ctor_set(v___x_1602_, 1, v___x_1605_);
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
case 9:
{
lean_object* v_data_1610_; lean_object* v_msg_1611_; lean_object* v_children_1612_; size_t v_sz_1613_; size_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v_cls_1629_; lean_object* v_result_x3f_1630_; double v_startTime_1631_; double v_stopTime_1632_; lean_object* v_msg_1634_; uint8_t v___x_1649_; 
v_data_1610_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_data_1610_);
v_msg_1611_ = lean_ctor_get(v_x_1567_, 1);
lean_inc_ref(v_msg_1611_);
v_children_1612_ = lean_ctor_get(v_x_1567_, 2);
lean_inc_ref(v_children_1612_);
lean_dec_ref_known(v_x_1567_, 3);
v_sz_1613_ = lean_array_size(v_children_1612_);
v___x_1614_ = ((size_t)0ULL);
lean_inc(v_x_1566_);
lean_inc_ref(v_x_1565_);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1565_, v_x_1566_, v_sz_1613_, v___x_1614_, v_children_1612_);
v_cls_1629_ = lean_ctor_get(v_data_1610_, 0);
lean_inc(v_cls_1629_);
v_result_x3f_1630_ = lean_ctor_get(v_data_1610_, 1);
lean_inc(v_result_x3f_1630_);
v_startTime_1631_ = lean_ctor_get_float(v_data_1610_, sizeof(void*)*3);
v_stopTime_1632_ = lean_ctor_get_float(v_data_1610_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1610_);
v___x_1649_ = l_Lean_Name_isAnonymous(v_cls_1629_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; double v___x_1665_; uint8_t v___x_1666_; 
v___x_1650_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1651_ = 1;
v___x_1652_ = l_Lean_Name_toString(v_cls_1629_, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1650_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1665_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1666_ = lean_float_beq(v_startTime_1631_, v___x_1665_);
if (v___x_1666_ == 0)
{
goto v___jp_1657_;
}
else
{
if (v___x_1649_ == 0)
{
v_msg_1634_ = v___x_1656_;
goto v___jp_1633_;
}
else
{
goto v___jp_1657_;
}
}
v___jp_1657_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; double v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1658_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1656_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = lean_float_sub(v_stopTime_1632_, v_startTime_1631_);
v___x_1661_ = lean_float_to_string(v___x_1660_);
v___x_1662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1659_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___x_1655_);
v_msg_1634_ = v___x_1664_;
goto v___jp_1633_;
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_result_x3f_1630_);
lean_dec(v_cls_1629_);
lean_dec_ref(v_msg_1611_);
lean_dec(v_x_1566_);
lean_dec_ref(v_x_1565_);
v___x_1667_ = lean_array_to_list(v___x_1615_);
v___x_1668_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1669_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1667_, v___x_1668_);
return v___x_1669_;
}
v___jp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1619_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___y_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v___y_1618_);
v___x_1623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_array_to_list(v___x_1615_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1627_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1621_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
return v___x_1628_;
}
v___jp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_MessageData_formatAux(v_x_1565_, v_x_1566_, v_msg_1611_);
if (lean_obj_tag(v_result_x3f_1630_) == 0)
{
v___y_1617_ = v_msg_1634_;
v___y_1618_ = v___x_1635_;
goto v___jp_1616_;
}
else
{
lean_object* v_val_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1648_; 
v_val_1636_ = lean_ctor_get(v_result_x3f_1630_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_result_x3f_1630_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1638_ = v_result_x3f_1630_;
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_val_1636_);
lean_dec(v_result_x3f_1630_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_unbox(v_val_1636_);
lean_dec(v_val_1636_);
v___x_1641_ = l_Lean_TraceResult_toEmoji(v___x_1640_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 3);
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1643_ = v___x_1638_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1635_);
v___y_1617_ = v_msg_1634_;
v___y_1618_ = v___x_1646_;
goto v___jp_1616_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1670_; lean_object* v___x_1671_; lean_object* v___y_1673_; 
v_f_1670_ = lean_ctor_get(v_x_1567_, 0);
lean_inc_ref(v_f_1670_);
lean_dec_ref_known(v_x_1567_, 2);
v___x_1671_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_box(0);
v___y_1673_ = v___x_1689_;
goto v___jp_1672_;
}
else
{
lean_object* v_val_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_val_1690_ = lean_ctor_get(v_x_1566_, 0);
v___x_1691_ = l_Lean_MessageData_mkPPContext(v_x_1565_, v_val_1690_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
v___y_1673_ = v___x_1692_;
goto v___jp_1672_;
}
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_apply_2(v_f_1670_, v___y_1673_, lean_box(0));
v___x_1675_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1674_, v___x_1671_);
if (lean_obj_tag(v___x_1675_) == 1)
{
lean_object* v_val_1676_; 
lean_dec(v___x_1674_);
v_val_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v_x_1567_ = v_val_1676_;
goto _start;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v___x_1675_);
lean_dec(v_x_1566_);
lean_dec_ref(v_x_1565_);
v___x_1678_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1679_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1680_ = lean_unsigned_to_nat(409u);
v___x_1681_ = lean_unsigned_to_nat(8u);
v___x_1682_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1683_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1674_);
lean_dec(v___x_1674_);
v___x_1684_ = 1;
v___x_1685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1683_, v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1682_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_mkPanicMessageWithDecl(v___x_1678_, v___x_1679_, v___x_1680_, v___x_1681_, v___x_1686_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1687_);
return v___x_1688_;
}
}
}
default: 
{
lean_object* v_a_1693_; 
v_a_1693_ = lean_ctor_get(v_x_1567_, 1);
lean_inc_ref(v_a_1693_);
lean_dec_ref(v_x_1567_);
v_x_1567_ = v_a_1693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1695_, lean_object* v_x_1696_, size_t v_sz_1697_, size_t v_i_1698_, lean_object* v_bs_1699_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1698_, v_sz_1697_);
if (v___x_1701_ == 0)
{
lean_dec(v_x_1696_);
lean_dec_ref(v_x_1695_);
return v_bs_1699_;
}
else
{
lean_object* v_v_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v_bs_x27_1705_; size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v_v_1702_ = lean_array_uget_borrowed(v_bs_1699_, v_i_1698_);
lean_inc(v_v_1702_);
lean_inc(v_x_1696_);
lean_inc_ref(v_x_1695_);
v___x_1703_ = l_Lean_MessageData_formatAux(v_x_1695_, v_x_1696_, v_v_1702_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v_bs_x27_1705_ = lean_array_uset(v_bs_1699_, v_i_1698_, v___x_1704_);
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_add(v_i_1698_, v___x_1706_);
v___x_1708_ = lean_array_uset(v_bs_x27_1705_, v_i_1698_, v___x_1703_);
v_i_1698_ = v___x_1707_;
v_bs_1699_ = v___x_1708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_, lean_object* v___y_1715_){
_start:
{
size_t v_sz_boxed_1716_; size_t v_i_boxed_1717_; lean_object* v_res_1718_; 
v_sz_boxed_1716_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1717_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1710_, v_x_1711_, v_sz_boxed_1716_, v_i_boxed_1717_, v_bs_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_MessageData_formatAux(v_x_1719_, v_x_1720_, v_x_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1727_, lean_object* v_ctx_x3f_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1731_ = l_Lean_MessageData_formatAux(v___x_1730_, v_ctx_x3f_1728_, v_msgData_1727_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1732_, lean_object* v_ctx_x3f_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_MessageData_format(v_msgData_1732_, v_ctx_x3f_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_MessageData_format(v_msgData_1736_, v___x_1738_);
v___x_1740_ = l_Std_Format_defWidth;
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = l_Std_Format_pretty(v___x_1739_, v___x_1740_, v___x_1741_, v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_MessageData_toString(v_msgData_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1746_);
lean_ctor_set(v___x_1748_, 1, v_a_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_s_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1776_ = l_Lean_MessageData_ofFormat(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1777_){
_start:
{
if (lean_obj_tag(v_o_1777_) == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1778_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1780_; 
v_val_1779_ = lean_ctor_get(v_o_1777_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v_o_1777_, 1);
v___x_1780_ = l_Lean_MessageData_ofExpr(v_val_1779_);
return v___x_1780_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1789_ = l_Lean_MessageData_ofFormat(v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1790_, lean_object* v_i_1791_, lean_object* v_acc_1792_){
_start:
{
lean_object* v___y_1794_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = lean_array_get_size(v_es_1790_);
v___x_1799_ = lean_nat_dec_lt(v_i_1791_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_i_1791_);
v___x_1800_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_acc_1792_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
return v___x_1801_;
}
else
{
lean_object* v_e_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_e_1802_ = lean_array_fget_borrowed(v_es_1790_, v_i_1791_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_nat_dec_eq(v_i_1791_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_acc_1792_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
lean_inc(v_e_1802_);
v___x_1807_ = l_Lean_MessageData_ofExpr(v_e_1802_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___y_1794_ = v___x_1808_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_inc(v_e_1802_);
v___x_1809_ = l_Lean_MessageData_ofExpr(v_e_1802_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_acc_1792_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___y_1794_ = v___x_1810_;
goto v___jp_1793_;
}
}
v___jp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(1u);
v___x_1796_ = lean_nat_add(v_i_1791_, v___x_1795_);
lean_dec(v_i_1791_);
v_i_1791_ = v___x_1796_;
v_acc_1792_ = v___y_1794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1811_, lean_object* v_i_1812_, lean_object* v_acc_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1811_, v_i_1812_, v_acc_1813_);
lean_dec_ref(v_es_1811_);
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1819_ = l_Lean_MessageData_ofFormat(v___x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1823_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1820_, v___x_1821_, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1824_);
lean_dec_ref(v_es_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1828_, lean_object* v_f_1829_, lean_object* v_r_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1831_ = lean_string_length(v_l_1828_);
v___x_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_l_1828_);
v___x_1833_ = l_Lean_MessageData_ofFormat(v___x_1832_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_f_1829_);
v___x_1835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_r_1830_);
v___x_1836_ = l_Lean_MessageData_ofFormat(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1831_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1842_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1843_ = l_Lean_MessageData_bracket(v___x_1841_, v_f_1840_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1846_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1847_ = l_Lean_MessageData_bracket(v___x_1845_, v_f_1844_, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
if (lean_obj_tag(v_x_1848_) == 0)
{
lean_object* v___x_1850_; 
lean_dec_ref(v_x_1849_);
v___x_1850_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1850_;
}
else
{
lean_object* v_tail_1851_; 
v_tail_1851_ = lean_ctor_get(v_x_1848_, 1);
if (lean_obj_tag(v_tail_1851_) == 0)
{
lean_object* v_head_1852_; 
lean_dec_ref(v_x_1849_);
v_head_1852_ = lean_ctor_get(v_x_1848_, 0);
lean_inc(v_head_1852_);
lean_dec_ref_known(v_x_1848_, 2);
return v_head_1852_;
}
else
{
lean_object* v_head_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
lean_inc(v_tail_1851_);
v_head_1853_ = lean_ctor_get(v_x_1848_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1848_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_x_1848_, 1);
lean_dec(v_unused_1863_);
v___x_1855_ = v_x_1848_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_head_1853_);
lean_dec(v_x_1848_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
lean_inc_ref(v_x_1849_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 7);
lean_ctor_set(v___x_1855_, 1, v_x_1849_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_head_1853_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_x_1849_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = l_Lean_MessageData_joinSep(v_tail_1851_, v_x_1849_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
return v___x_1860_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1868_ = l_Lean_MessageData_ofFormat(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1873_ = l_Lean_MessageData_ofFormat(v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_box(1);
v___x_1875_ = l_Lean_MessageData_ofFormat(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1877_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1882_ = l_Lean_MessageData_joinSep(v_x_1879_, v___x_1881_);
v___x_1883_ = l_Lean_MessageData_sbracket(v___x_1882_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_array_to_list(v_msgs_1884_);
v___x_1886_ = l_Lean_MessageData_ofList(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1891_ = l_Lean_MessageData_ofFormat(v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1896_ = l_Lean_MessageData_ofFormat(v___x_1895_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1901_ = l_Lean_MessageData_ofFormat(v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1902_){
_start:
{
if (lean_obj_tag(v_xs_1902_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1903_;
}
else
{
lean_object* v_tail_1904_; 
v_tail_1904_ = lean_ctor_get(v_xs_1902_, 1);
lean_inc(v_tail_1904_);
if (lean_obj_tag(v_tail_1904_) == 0)
{
lean_object* v_head_1905_; 
v_head_1905_ = lean_ctor_get(v_xs_1902_, 0);
lean_inc(v_head_1905_);
lean_dec_ref_known(v_xs_1902_, 2);
return v_head_1905_;
}
else
{
lean_object* v_tail_1906_; 
v_tail_1906_ = lean_ctor_get(v_tail_1904_, 1);
if (lean_obj_tag(v_tail_1906_) == 0)
{
lean_object* v_head_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1924_; 
v_head_1907_ = lean_ctor_get(v_xs_1902_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_xs_1902_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_xs_1902_, 1);
lean_dec(v_unused_1925_);
v___x_1909_ = v_xs_1902_;
v_isShared_1910_ = v_isSharedCheck_1924_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_head_1907_);
lean_dec(v_xs_1902_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1924_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_head_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1922_; 
v_head_1911_ = lean_ctor_get(v_tail_1904_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_tail_1904_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_tail_1904_, 1);
lean_dec(v_unused_1923_);
v___x_1913_ = v_tail_1904_;
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_head_1911_);
lean_dec(v_tail_1904_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 7);
lean_ctor_set(v___x_1913_, 1, v___x_1915_);
lean_ctor_set(v___x_1913_, 0, v_head_1907_);
v___x_1917_ = v___x_1913_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_head_1907_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1919_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 7);
lean_ctor_set(v___x_1909_, 1, v_head_1911_);
lean_ctor_set(v___x_1909_, 0, v___x_1917_);
v___x_1919_ = v___x_1909_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_head_1911_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
else
{
lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1949_; 
v_isSharedCheck_1949_ = !lean_is_exclusive(v_tail_1904_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1950_ = lean_ctor_get(v_tail_1904_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_tail_1904_, 0);
lean_dec(v_unused_1951_);
v___x_1927_ = v_tail_1904_;
v_isShared_1928_ = v_isSharedCheck_1949_;
goto v_resetjp_1926_;
}
else
{
lean_dec(v_tail_1904_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1949_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1929_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1902_);
v___x_1930_ = lean_array_mk(v_xs_1902_);
v___x_1931_ = lean_array_pop(v___x_1930_);
v___x_1932_ = lean_array_to_list(v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1934_ = l_Lean_MessageData_joinSep(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1928_ == 0)
{
lean_ctor_set_tag(v___x_1927_, 7);
lean_ctor_set(v___x_1927_, 1, v___x_1935_);
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1937_ = v___x_1927_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v___x_1938_ = l_List_getLast_x21___redArg(v___x_1929_, v_xs_1902_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_xs_1902_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; 
v_unused_1946_ = lean_ctor_get(v_xs_1902_, 1);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_xs_1902_, 0);
lean_dec(v_unused_1947_);
v___x_1940_ = v_xs_1902_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v_xs_1902_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
lean_ctor_set(v___x_1940_, 0, v___x_1937_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
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
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1956_ = l_Lean_MessageData_ofFormat(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1961_ = l_Lean_MessageData_ofFormat(v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1962_){
_start:
{
if (lean_obj_tag(v_xs_1962_) == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1963_;
}
else
{
lean_object* v_tail_1964_; 
v_tail_1964_ = lean_ctor_get(v_xs_1962_, 1);
lean_inc(v_tail_1964_);
if (lean_obj_tag(v_tail_1964_) == 0)
{
lean_object* v_head_1965_; 
v_head_1965_ = lean_ctor_get(v_xs_1962_, 0);
lean_inc(v_head_1965_);
lean_dec_ref_known(v_xs_1962_, 2);
return v_head_1965_;
}
else
{
lean_object* v_tail_1966_; 
v_tail_1966_ = lean_ctor_get(v_tail_1964_, 1);
if (lean_obj_tag(v_tail_1966_) == 0)
{
lean_object* v_head_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1984_; 
v_head_1967_ = lean_ctor_get(v_xs_1962_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_xs_1962_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_xs_1962_, 1);
lean_dec(v_unused_1985_);
v___x_1969_ = v_xs_1962_;
v_isShared_1970_ = v_isSharedCheck_1984_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_head_1967_);
lean_dec(v_xs_1962_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1984_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_head_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1982_; 
v_head_1971_ = lean_ctor_get(v_tail_1964_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_tail_1964_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_tail_1964_, 1);
lean_dec(v_unused_1983_);
v___x_1973_ = v_tail_1964_;
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_head_1971_);
lean_dec(v_tail_1964_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 7);
lean_ctor_set(v___x_1973_, 1, v___x_1975_);
lean_ctor_set(v___x_1973_, 0, v_head_1967_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_head_1967_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 7);
lean_ctor_set(v___x_1969_, 1, v_head_1971_);
lean_ctor_set(v___x_1969_, 0, v___x_1977_);
v___x_1979_ = v___x_1969_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_head_1971_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2009_; 
v_isSharedCheck_2009_ = !lean_is_exclusive(v_tail_1964_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2010_ = lean_ctor_get(v_tail_1964_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_tail_1964_, 0);
lean_dec(v_unused_2011_);
v___x_1987_ = v_tail_1964_;
v_isShared_1988_ = v_isSharedCheck_2009_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_tail_1964_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2009_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1989_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1962_);
v___x_1990_ = lean_array_mk(v_xs_1962_);
v___x_1991_ = lean_array_pop(v___x_1990_);
v___x_1992_ = lean_array_to_list(v___x_1991_);
v___x_1993_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1994_ = l_Lean_MessageData_joinSep(v___x_1992_, v___x_1993_);
v___x_1995_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 7);
lean_ctor_set(v___x_1987_, 1, v___x_1995_);
lean_ctor_set(v___x_1987_, 0, v___x_1994_);
v___x_1997_ = v___x_1987_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v___x_1998_ = l_List_getLast_x21___redArg(v___x_1989_, v_xs_1962_);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_xs_1962_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; lean_object* v_unused_2007_; 
v_unused_2006_ = lean_ctor_get(v_xs_1962_, 1);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_xs_1962_, 0);
lean_dec(v_unused_2007_);
v___x_2000_ = v_xs_1962_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_xs_1962_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 7);
lean_ctor_set(v___x_2000_, 1, v___x_1998_);
lean_ctor_set(v___x_2000_, 0, v___x_1997_);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
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
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2018_ = l_Lean_MessageData_ofFormat(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2020_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v_note_2022_);
return v___x_2024_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2029_ = l_Lean_MessageData_ofFormat(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2031_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v_hint_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2039_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2040_ = lean_box(0);
v___x_2041_ = l_List_mapTR_loop___redArg(v___x_2039_, v_es_2038_, v___x_2040_);
v___x_2042_ = l_Lean_MessageData_ofList(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2045_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2047_ = l_Lean_instInhabitedPosition_default;
v___x_2048_ = lean_box(0);
v___x_2049_ = 0;
v___x_2050_ = 2;
v___x_2051_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2051_, 0, v___x_2046_);
lean_ctor_set(v___x_2051_, 1, v___x_2047_);
lean_ctor_set(v___x_2051_, 2, v___x_2048_);
lean_ctor_set(v___x_2051_, 3, v___x_2046_);
lean_ctor_set(v___x_2051_, 4, v_inst_2045_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*5, v___x_2049_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*5 + 1, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*5 + 2, v___x_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2052_, lean_object* v_inst_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2057_, lean_object* v_inst_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v_fileName_2074_; lean_object* v_pos_2075_; lean_object* v_endPos_2076_; uint8_t v_keepFullRange_2077_; uint8_t v_severity_2078_; uint8_t v_isSilent_2079_; lean_object* v_caption_2080_; lean_object* v_data_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_fileName_2074_ = lean_ctor_get(v_x_2073_, 0);
lean_inc_ref(v_fileName_2074_);
v_pos_2075_ = lean_ctor_get(v_x_2073_, 1);
lean_inc_ref(v_pos_2075_);
v_endPos_2076_ = lean_ctor_get(v_x_2073_, 2);
lean_inc(v_endPos_2076_);
v_keepFullRange_2077_ = lean_ctor_get_uint8(v_x_2073_, sizeof(void*)*5);
v_severity_2078_ = lean_ctor_get_uint8(v_x_2073_, sizeof(void*)*5 + 1);
v_isSilent_2079_ = lean_ctor_get_uint8(v_x_2073_, sizeof(void*)*5 + 2);
v_caption_2080_ = lean_ctor_get(v_x_2073_, 3);
lean_inc_ref(v_caption_2080_);
v_data_2081_ = lean_ctor_get(v_x_2073_, 4);
lean_inc(v_data_2081_);
lean_dec_ref(v_x_2073_);
v___x_2082_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2083_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_fileName_2074_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2089_ = l_Lean_instToJsonPosition_toJson(v_pos_2075_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2086_);
v___x_2092_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2093_ = l_Lean_Option_toJson___redArg(v___x_2082_, v_endPos_2076_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___x_2086_);
v___x_2096_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2097_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2097_, 0, v_keepFullRange_2077_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2086_);
v___x_2100_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2101_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2078_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2086_);
v___x_2104_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2105_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2105_, 0, v_isSilent_2079_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2086_);
v___x_2108_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_caption_2080_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2086_);
v___x_2112_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2113_ = lean_apply_1(v_inst_2072_, v_data_2081_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2086_);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2086_);
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2111_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2107_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2103_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2099_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2095_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2091_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2087_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2125_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2126_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2124_, v___x_2123_, v___x_2125_);
v___x_2127_ = l_Lean_Json_mkObj(v___x_2126_);
lean_dec(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2128_, lean_object* v_inst_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2129_, v_x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2133_, 0, lean_box(0));
lean_closure_set(v___x_2133_, 1, v_inst_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2134_, lean_object* v_inst_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2136_, 0, lean_box(0));
lean_closure_set(v___x_2136_, 1, v_inst_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = 1;
v___x_2143_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2147_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2148_ = lean_string_append(v___x_2147_, v___x_2146_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = 1;
v___x_2152_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2152_, v___x_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2155_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2156_ = lean_string_append(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2159_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2160_ = lean_string_append(v___x_2159_, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = 1;
v___x_2167_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2170_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2171_ = lean_string_append(v___x_2170_, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2173_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2174_ = lean_string_append(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = 1;
v___x_2178_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2181_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2182_ = lean_string_append(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2184_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2185_ = lean_string_append(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = 1;
v___x_2190_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2191_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2190_, v___x_2189_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2193_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2194_ = lean_string_append(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2196_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2197_ = lean_string_append(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = 1;
v___x_2201_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2202_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2204_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2205_ = lean_string_append(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2207_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2208_ = lean_string_append(v___x_2207_, v___x_2206_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = 1;
v___x_2212_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2213_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2215_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2216_ = lean_string_append(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2218_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2219_ = lean_string_append(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = 1;
v___x_2223_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2224_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2226_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2227_ = lean_string_append(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2229_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2230_ = lean_string_append(v___x_2229_, v___x_2228_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = 1;
v___x_2234_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2235_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2234_, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2237_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2238_ = lean_string_append(v___x_2237_, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2240_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2241_ = lean_string_append(v___x_2240_, v___x_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2242_, lean_object* v_json_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2245_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2243_);
v___x_2246_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2244_, v___x_2245_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
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
v___x_2251_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
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
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
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
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2265_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2266_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2267_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2268_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2243_);
v___x_2269_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2266_, v___x_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2279_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2279_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2274_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2275_ = lean_string_append(v___x_2274_, v_a_2270_);
lean_dec(v_a_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2275_);
v___x_2277_ = v___x_2272_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
else
{
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2280_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2269_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2269_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 0);
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2288_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2289_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2243_);
v___x_2290_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2267_, v___x_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2295_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2296_ = lean_string_append(v___x_2295_, v_a_2291_);
lean_dec(v_a_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2296_);
v___x_2298_ = v___x_2293_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2301_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2290_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2290_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 0);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2309_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2310_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2311_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2243_);
v___x_2312_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2310_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2318_ = lean_string_append(v___x_2317_, v_a_2313_);
lean_dec(v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
else
{
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2323_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2312_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2312_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 0);
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2331_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2332_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2333_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2243_);
v___x_2334_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2332_, v___x_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2340_ = lean_string_append(v___x_2339_, v_a_2335_);
lean_dec(v_a_2335_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2340_);
v___x_2342_ = v___x_2337_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2345_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2334_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2334_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 0);
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2354_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2243_);
v___x_2355_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2310_, v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2365_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2365_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2360_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2361_ = lean_string_append(v___x_2360_, v_a_2356_);
lean_dec(v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2361_);
v___x_2363_ = v___x_2358_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2366_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2355_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2355_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 0);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_a_2374_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2375_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2243_);
v___x_2376_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v___x_2244_, v___x_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_a_2374_);
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2381_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2382_ = lean_string_append(v___x_2381_, v_a_2377_);
lean_dec(v_a_2377_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
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
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2374_);
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
lean_dec(v_json_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2387_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2376_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2376_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 0);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2396_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2397_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2243_, v_inst_2242_, v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_a_2395_);
lean_dec(v_a_2374_);
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2407_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2403_ = lean_string_append(v___x_2402_, v_a_2398_);
lean_dec(v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2403_);
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_a_2395_);
lean_dec(v_a_2374_);
lean_dec(v_a_2353_);
lean_dec(v_a_2331_);
lean_dec(v_a_2309_);
lean_dec(v_a_2288_);
lean_dec(v_a_2265_);
v_a_2408_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2397_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2397_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 0);
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2427_; 
v_a_2416_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2418_ = v___x_2397_;
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2397_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; uint8_t v___x_2421_; uint8_t v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2425_; 
v___x_2420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2420_, 0, v_a_2265_);
lean_ctor_set(v___x_2420_, 1, v_a_2288_);
lean_ctor_set(v___x_2420_, 2, v_a_2309_);
lean_ctor_set(v___x_2420_, 3, v_a_2395_);
lean_ctor_set(v___x_2420_, 4, v_a_2416_);
v___x_2421_ = lean_unbox(v_a_2331_);
lean_dec(v_a_2331_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*5, v___x_2421_);
v___x_2422_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*5 + 1, v___x_2422_);
v___x_2423_ = lean_unbox(v_a_2374_);
lean_dec(v_a_2374_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*5 + 2, v___x_2423_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2425_ = v___x_2418_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2428_, lean_object* v_inst_2429_, lean_object* v_json_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2429_, v_json_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2433_, 0, lean_box(0));
lean_closure_set(v___x_2433_, 1, v_inst_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2434_, lean_object* v_inst_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2436_, 0, lean_box(0));
lean_closure_set(v___x_2436_, 1, v_inst_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2437_){
_start:
{
if (lean_obj_tag(v_x_2437_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_box(0);
return v___x_2438_;
}
else
{
lean_object* v_val_2439_; lean_object* v___x_2440_; 
v_val_2439_ = lean_ctor_get(v_x_2437_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v_x_2437_, 1);
v___x_2440_ = l_Lean_instToJsonPosition_toJson(v_val_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
if (lean_obj_tag(v_a_2441_) == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_array_to_list(v_a_2442_);
return v___x_2443_;
}
else
{
lean_object* v_head_2444_; lean_object* v_tail_2445_; lean_object* v___x_2446_; 
v_head_2444_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_head_2444_);
v_tail_2445_ = lean_ctor_get(v_a_2441_, 1);
lean_inc(v_tail_2445_);
lean_dec_ref_known(v_a_2441_, 2);
v___x_2446_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2442_, v_head_2444_);
v_a_2441_ = v_tail_2445_;
v_a_2442_ = v___x_2446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2449_){
_start:
{
lean_object* v_toBaseMessage_2450_; lean_object* v_kind_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2516_; 
v_toBaseMessage_2450_ = lean_ctor_get(v_x_2449_, 0);
v_kind_2451_ = lean_ctor_get(v_x_2449_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_x_2449_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2453_ = v_x_2449_;
v_isShared_2454_ = v_isSharedCheck_2516_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_kind_2451_);
lean_inc(v_toBaseMessage_2450_);
lean_dec(v_x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2516_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_fileName_2455_; lean_object* v_pos_2456_; lean_object* v_endPos_2457_; uint8_t v_keepFullRange_2458_; uint8_t v_severity_2459_; uint8_t v_isSilent_2460_; lean_object* v_caption_2461_; lean_object* v_data_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v_fileName_2455_ = lean_ctor_get(v_toBaseMessage_2450_, 0);
lean_inc_ref(v_fileName_2455_);
v_pos_2456_ = lean_ctor_get(v_toBaseMessage_2450_, 1);
lean_inc_ref(v_pos_2456_);
v_endPos_2457_ = lean_ctor_get(v_toBaseMessage_2450_, 2);
lean_inc(v_endPos_2457_);
v_keepFullRange_2458_ = lean_ctor_get_uint8(v_toBaseMessage_2450_, sizeof(void*)*5);
v_severity_2459_ = lean_ctor_get_uint8(v_toBaseMessage_2450_, sizeof(void*)*5 + 1);
v_isSilent_2460_ = lean_ctor_get_uint8(v_toBaseMessage_2450_, sizeof(void*)*5 + 2);
v_caption_2461_ = lean_ctor_get(v_toBaseMessage_2450_, 3);
lean_inc_ref(v_caption_2461_);
v_data_2462_ = lean_ctor_get(v_toBaseMessage_2450_, 4);
lean_inc(v_data_2462_);
lean_dec_ref(v_toBaseMessage_2450_);
v___x_2463_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_fileName_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___x_2464_);
lean_ctor_set(v___x_2453_, 0, v___x_2463_);
v___x_2466_ = v___x_2453_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2470_ = l_Lean_instToJsonPosition_toJson(v_pos_2456_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v___x_2467_);
v___x_2473_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2474_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2457_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2467_);
v___x_2477_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2478_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2478_, 0, v_keepFullRange_2458_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2467_);
v___x_2481_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2482_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2459_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2467_);
v___x_2485_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2486_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2486_, 0, v_isSilent_2460_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2467_);
v___x_2489_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_caption_2461_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2467_);
v___x_2493_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_data_2462_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v___x_2467_);
v___x_2497_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2498_ = 1;
v___x_2499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2451_, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2497_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2467_);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2467_);
v___x_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2496_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2492_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2488_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2484_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2480_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2476_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2472_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2468_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2513_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2511_, v___x_2512_);
v___x_2514_ = l_Lean_Json_mkObj(v___x_2513_);
lean_dec(v___x_2513_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2519_, lean_object* v_k_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = l_Lean_Json_getObjValD(v_j_2519_, v_k_2520_);
v___x_2522_ = l_Lean_Json_getStr_x3f(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2523_, lean_object* v_k_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2523_, v_k_2524_);
lean_dec_ref(v_k_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2526_, lean_object* v_k_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = l_Lean_Json_getObjValD(v_j_2526_, v_k_2527_);
v___x_2529_ = l_Lean_instFromJsonPosition_fromJson(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2530_, lean_object* v_k_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2530_, v_k_2531_);
lean_dec_ref(v_k_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2533_, lean_object* v_k_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = l_Lean_Json_getObjValD(v_j_2533_, v_k_2534_);
v___x_2536_ = l_Lean_Json_getBool_x3f(v___x_2535_);
lean_dec(v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2537_, lean_object* v_k_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2537_, v_k_2538_);
lean_dec_ref(v_k_2538_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2540_, lean_object* v_k_2541_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = l_Lean_Json_getObjValD(v_j_2540_, v_k_2541_);
v___x_2543_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2544_, lean_object* v_k_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2544_, v_k_2545_);
lean_dec_ref(v_k_2545_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2547_, lean_object* v_k_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = l_Lean_Json_getObjValD(v_j_2547_, v_k_2548_);
v___x_2550_ = l_Lean_Name_fromJson_x3f(v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2551_, lean_object* v_k_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2551_, v_k_2552_);
lean_dec_ref(v_k_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2556_){
_start:
{
if (lean_obj_tag(v_x_2556_) == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_instFromJsonPosition_fromJson(v_x_2556_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
v_a_2567_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v___x_2558_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2558_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2576_, lean_object* v_k_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = l_Lean_Json_getObjValD(v_j_2576_, v_k_2577_);
v___x_2579_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2580_, lean_object* v_k_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2580_, v_k_2581_);
lean_dec_ref(v_k_2581_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = 1;
v___x_2588_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2589_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2588_, v___x_2587_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2591_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2592_ = lean_string_append(v___x_2591_, v___x_2590_);
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2594_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2595_ = lean_string_append(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2597_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2598_ = lean_string_append(v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2600_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2601_ = lean_string_append(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2603_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2604_ = lean_string_append(v___x_2603_, v___x_2602_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2606_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2607_ = lean_string_append(v___x_2606_, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2609_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2610_ = lean_string_append(v___x_2609_, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2612_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2613_ = lean_string_append(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2615_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2616_ = lean_string_append(v___x_2615_, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2618_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2619_ = lean_string_append(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2621_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2622_ = lean_string_append(v___x_2621_, v___x_2620_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2624_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2625_ = lean_string_append(v___x_2624_, v___x_2623_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2627_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2628_ = lean_string_append(v___x_2627_, v___x_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2630_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2631_ = lean_string_append(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2633_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2634_ = lean_string_append(v___x_2633_, v___x_2632_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2636_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2637_ = lean_string_append(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2639_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2640_ = lean_string_append(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = 1;
v___x_2644_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2644_, v___x_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2647_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2648_ = lean_string_append(v___x_2647_, v___x_2646_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2650_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2651_ = lean_string_append(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2652_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2652_);
v___x_2654_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2652_, v___x_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_json_2652_);
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2664_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2664_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2660_ = lean_string_append(v___x_2659_, v_a_2655_);
lean_dec(v_a_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2660_);
v___x_2662_ = v___x_2657_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_json_2652_);
v_a_2665_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2654_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2654_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 0);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2674_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2652_);
v___x_2675_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2652_, v___x_2674_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2681_ = lean_string_append(v___x_2680_, v_a_2676_);
lean_dec(v_a_2676_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
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
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2686_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2675_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2675_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 0);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_a_2694_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2695_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2652_);
v___x_2696_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2652_, v___x_2695_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2701_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2702_ = lean_string_append(v___x_2701_, v_a_2697_);
lean_dec(v_a_2697_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2702_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
else
{
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2707_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2696_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2696_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 0);
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2715_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2716_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2652_);
v___x_2717_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2652_, v___x_2716_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2723_ = lean_string_append(v___x_2722_, v_a_2718_);
lean_dec(v_a_2718_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2723_);
v___x_2725_ = v___x_2720_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
else
{
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2728_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2717_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2717_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 0);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2737_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2652_);
v___x_2738_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2652_, v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2743_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2744_ = lean_string_append(v___x_2743_, v_a_2739_);
lean_dec(v_a_2739_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2744_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
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
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2749_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2738_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2738_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 0);
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2758_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2652_);
v___x_2759_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2652_, v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2764_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2765_ = lean_string_append(v___x_2764_, v_a_2760_);
lean_dec(v_a_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2765_);
v___x_2767_ = v___x_2762_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2770_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2759_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2759_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 0);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2778_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2779_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2652_);
v___x_2780_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2652_, v___x_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2786_ = lean_string_append(v___x_2785_, v_a_2781_);
lean_dec(v_a_2781_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2791_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2780_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2780_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_a_2799_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2800_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2652_);
v___x_2801_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2652_, v___x_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2799_);
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2806_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2807_ = lean_string_append(v___x_2806_, v_a_2802_);
lean_dec(v_a_2802_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2807_);
v___x_2809_ = v___x_2804_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2799_);
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
lean_dec(v_json_2652_);
v_a_2812_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2801_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2801_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 0);
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2821_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2822_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2652_, v___x_2821_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2820_);
lean_dec(v_a_2799_);
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2832_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2832_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2827_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2828_ = lean_string_append(v___x_2827_, v_a_2823_);
lean_dec(v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2828_);
v___x_2830_ = v___x_2825_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2820_);
lean_dec(v_a_2799_);
lean_dec(v_a_2778_);
lean_dec(v_a_2757_);
lean_dec(v_a_2736_);
lean_dec(v_a_2715_);
lean_dec(v_a_2694_);
lean_dec(v_a_2673_);
v_a_2833_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2822_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2822_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set_tag(v___x_2835_, 0);
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2853_; 
v_a_2841_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2843_ = v___x_2822_;
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2822_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; uint8_t v___x_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2845_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2845_, 0, v_a_2673_);
lean_ctor_set(v___x_2845_, 1, v_a_2694_);
lean_ctor_set(v___x_2845_, 2, v_a_2715_);
lean_ctor_set(v___x_2845_, 3, v_a_2799_);
lean_ctor_set(v___x_2845_, 4, v_a_2820_);
v___x_2846_ = lean_unbox(v_a_2736_);
lean_dec(v_a_2736_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*5, v___x_2846_);
v___x_2847_ = lean_unbox(v_a_2757_);
lean_dec(v_a_2757_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*5 + 1, v___x_2847_);
v___x_2848_ = lean_unbox(v_a_2778_);
lean_dec(v_a_2778_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*5 + 2, v___x_2848_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2845_);
lean_ctor_set(v___x_2849_, 1, v_a_2841_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2849_);
v___x_2851_ = v___x_2843_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2860_ = l_Lean_Name_str___override(v_errorName_2858_, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2861_, lean_object* v_name_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = l_Lean_kindOfErrorName(v_name_2862_);
v___x_2864_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_msg_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2866_){
_start:
{
switch(lean_obj_tag(v_a_2866_))
{
case 0:
{
return v_a_2866_;
}
case 1:
{
lean_object* v_pre_2867_; lean_object* v_str_2868_; lean_object* v_p_x27_2869_; uint8_t v___y_2871_; uint8_t v___x_2874_; 
v_pre_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_pre_2867_);
v_str_2868_ = lean_ctor_get(v_a_2866_, 1);
lean_inc_ref(v_str_2868_);
lean_dec_ref_known(v_a_2866_, 2);
v_p_x27_2869_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2867_);
v___x_2874_ = l_Lean_Name_isAnonymous(v_p_x27_2869_);
if (v___x_2874_ == 0)
{
v___y_2871_ = v___x_2874_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2876_ = lean_string_dec_eq(v_str_2868_, v___x_2875_);
v___y_2871_ = v___x_2876_;
goto v___jp_2870_;
}
v___jp_2870_:
{
if (v___y_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Name_str___override(v_p_x27_2869_, v_str_2868_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; 
lean_dec(v_p_x27_2869_);
lean_dec_ref(v_str_2868_);
v___x_2873_ = lean_box(0);
return v___x_2873_;
}
}
}
default: 
{
lean_object* v_pre_2877_; lean_object* v_i_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_pre_2877_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_pre_2877_);
v_i_2878_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_i_2878_);
lean_dec_ref_known(v_a_2866_, 2);
v___x_2879_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2877_);
v___x_2880_ = l_Lean_Name_num___override(v___x_2879_, v_i_2878_);
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2881_){
_start:
{
switch(lean_obj_tag(v_x_2881_))
{
case 3:
{
lean_object* v_a_2882_; lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2891_; 
v_a_2882_ = lean_ctor_get(v_x_2881_, 0);
v_a_2883_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2885_ = v_x_2881_;
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_inc(v_a_2882_);
lean_dec(v_x_2881_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = l_Lean_MessageData_stripNestedTags(v_a_2883_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2887_);
v___x_2889_ = v___x_2885_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2882_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
case 4:
{
lean_object* v_a_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2901_; 
v_a_2892_ = lean_ctor_get(v_x_2881_, 0);
v_a_2893_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2895_ = v_x_2881_;
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_inc(v_a_2892_);
lean_dec(v_x_2881_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = l_Lean_MessageData_stripNestedTags(v_a_2893_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v___x_2897_);
v___x_2899_ = v___x_2895_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2892_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
case 8:
{
lean_object* v_a_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2911_; 
v_a_2902_ = lean_ctor_get(v_x_2881_, 0);
v_a_2903_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2905_ = v_x_2881_;
v_isShared_2906_ = v_isSharedCheck_2911_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_inc(v_a_2902_);
lean_dec(v_x_2881_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2911_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2902_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_a_2903_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
case 11:
{
lean_object* v_a_2912_; lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2921_; 
v_a_2912_ = lean_ctor_get(v_x_2881_, 0);
v_a_2913_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2915_ = v_x_2881_;
v_isShared_2916_ = v_isSharedCheck_2921_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_inc(v_a_2912_);
lean_dec(v_x_2881_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2921_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2917_ = l_Lean_MessageData_stripNestedTags(v_a_2913_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2917_);
v___x_2919_ = v___x_2915_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2912_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
default: 
{
return v_x_2881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 1)
{
lean_object* v_pre_2923_; lean_object* v_str_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_pre_2923_ = lean_ctor_get(v_x_2922_, 0);
v_str_2924_ = lean_ctor_get(v_x_2922_, 1);
v___x_2925_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2926_ = lean_string_dec_eq(v_str_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_box(0);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; 
lean_inc(v_pre_2923_);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_pre_2923_);
return v___x_2928_;
}
}
else
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_box(0);
return v___x_2929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_errorNameOfKind_x3f(v_x_2930_);
lean_dec(v_x_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2932_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = l_Lean_MessageData_kind(v_msg_2932_);
v___x_2934_ = l_Lean_errorNameOfKind_x3f(v___x_2933_);
lean_dec(v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_MessageData_errorName_x3f(v_msg_2935_);
lean_dec_ref(v_msg_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2937_){
_start:
{
lean_object* v_data_2938_; lean_object* v___x_2939_; 
v_data_2938_ = lean_ctor_get(v_msg_2937_, 4);
v___x_2939_ = l_Lean_MessageData_errorName_x3f(v_data_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Message_errorName_x3f(v_msg_2940_);
lean_dec_ref(v_msg_2940_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2942_){
_start:
{
lean_object* v_toBaseMessage_2943_; lean_object* v_fileName_2944_; lean_object* v_pos_2945_; lean_object* v_endPos_2946_; uint8_t v_keepFullRange_2947_; uint8_t v_severity_2948_; uint8_t v_isSilent_2949_; lean_object* v_caption_2950_; lean_object* v_data_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2960_; 
v_toBaseMessage_2943_ = lean_ctor_get(v_msg_2942_, 0);
lean_inc_ref(v_toBaseMessage_2943_);
lean_dec_ref(v_msg_2942_);
v_fileName_2944_ = lean_ctor_get(v_toBaseMessage_2943_, 0);
v_pos_2945_ = lean_ctor_get(v_toBaseMessage_2943_, 1);
v_endPos_2946_ = lean_ctor_get(v_toBaseMessage_2943_, 2);
v_keepFullRange_2947_ = lean_ctor_get_uint8(v_toBaseMessage_2943_, sizeof(void*)*5);
v_severity_2948_ = lean_ctor_get_uint8(v_toBaseMessage_2943_, sizeof(void*)*5 + 1);
v_isSilent_2949_ = lean_ctor_get_uint8(v_toBaseMessage_2943_, sizeof(void*)*5 + 2);
v_caption_2950_ = lean_ctor_get(v_toBaseMessage_2943_, 3);
v_data_2951_ = lean_ctor_get(v_toBaseMessage_2943_, 4);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_toBaseMessage_2943_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2953_ = v_toBaseMessage_2943_;
v_isShared_2954_ = v_isSharedCheck_2960_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_data_2951_);
lean_inc(v_caption_2950_);
lean_inc(v_endPos_2946_);
lean_inc(v_pos_2945_);
lean_inc(v_fileName_2944_);
lean_dec(v_toBaseMessage_2943_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2960_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_data_2951_);
v___x_2956_ = l_Lean_MessageData_ofFormat(v___x_2955_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 4, v___x_2956_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_fileName_2944_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_pos_2945_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_endPos_2946_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v_caption_2950_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v___x_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*5, v_keepFullRange_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*5 + 1, v_severity_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*5 + 2, v_isSilent_2949_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2966_, uint8_t v_includeEndPos_2967_){
_start:
{
lean_object* v___y_2969_; lean_object* v___y_2973_; uint32_t v___y_2974_; lean_object* v_str_2978_; lean_object* v_toBaseMessage_2990_; lean_object* v_kind_2991_; lean_object* v_fileName_2992_; lean_object* v_pos_2993_; lean_object* v_endPos_2994_; uint8_t v_severity_2995_; lean_object* v_caption_2996_; lean_object* v_data_2997_; lean_object* v___y_2999_; lean_object* v_str_3000_; lean_object* v___y_3008_; 
v_toBaseMessage_2990_ = lean_ctor_get(v_msg_2966_, 0);
lean_inc_ref(v_toBaseMessage_2990_);
v_kind_2991_ = lean_ctor_get(v_msg_2966_, 1);
lean_inc(v_kind_2991_);
lean_dec_ref(v_msg_2966_);
v_fileName_2992_ = lean_ctor_get(v_toBaseMessage_2990_, 0);
lean_inc_ref(v_fileName_2992_);
v_pos_2993_ = lean_ctor_get(v_toBaseMessage_2990_, 1);
lean_inc_ref(v_pos_2993_);
v_endPos_2994_ = lean_ctor_get(v_toBaseMessage_2990_, 2);
lean_inc(v_endPos_2994_);
v_severity_2995_ = lean_ctor_get_uint8(v_toBaseMessage_2990_, sizeof(void*)*5 + 1);
v_caption_2996_ = lean_ctor_get(v_toBaseMessage_2990_, 3);
lean_inc_ref(v_caption_2996_);
v_data_2997_ = lean_ctor_get(v_toBaseMessage_2990_, 4);
lean_inc(v_data_2997_);
lean_dec_ref(v_toBaseMessage_2990_);
if (v_includeEndPos_2967_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_endPos_2994_);
v___x_3014_ = lean_box(0);
v___y_3008_ = v___x_3014_;
goto v___jp_3007_;
}
else
{
v___y_3008_ = v_endPos_2994_;
goto v___jp_3007_;
}
v___jp_2968_:
{
lean_object* v___x_2970_; lean_object* v_str_2971_; 
v___x_2970_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2971_ = lean_string_append(v___y_2969_, v___x_2970_);
return v_str_2971_;
}
v___jp_2972_:
{
uint32_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 10;
v___x_2976_ = lean_uint32_dec_eq(v___y_2974_, v___x_2975_);
if (v___x_2976_ == 0)
{
v___y_2969_ = v___y_2973_;
goto v___jp_2968_;
}
else
{
return v___y_2973_;
}
}
v___jp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2979_ = lean_string_utf8_byte_size(v_str_2978_);
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = lean_nat_dec_eq(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_inc_ref(v_str_2978_);
v___x_2982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2982_, 0, v_str_2978_);
lean_ctor_set(v___x_2982_, 1, v___x_2980_);
lean_ctor_set(v___x_2982_, 2, v___x_2979_);
v___x_2983_ = l_String_Slice_Pos_prev_x3f(v___x_2982_, v___x_2979_);
if (lean_obj_tag(v___x_2983_) == 0)
{
uint32_t v___x_2984_; 
lean_dec_ref_known(v___x_2982_, 3);
v___x_2984_ = 65;
v___y_2973_ = v_str_2978_;
v___y_2974_ = v___x_2984_;
goto v___jp_2972_;
}
else
{
lean_object* v_val_2985_; lean_object* v___x_2986_; 
v_val_2985_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2985_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2986_ = l_String_Slice_Pos_get_x3f(v___x_2982_, v_val_2985_);
lean_dec(v_val_2985_);
lean_dec_ref_known(v___x_2982_, 3);
if (lean_obj_tag(v___x_2986_) == 0)
{
uint32_t v___x_2987_; 
v___x_2987_ = 65;
v___y_2973_ = v_str_2978_;
v___y_2974_ = v___x_2987_;
goto v___jp_2972_;
}
else
{
lean_object* v_val_2988_; uint32_t v___x_2989_; 
v_val_2988_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2989_ = lean_unbox_uint32(v_val_2988_);
lean_dec(v_val_2988_);
v___y_2973_ = v_str_2978_;
v___y_2974_ = v___x_2989_;
goto v___jp_2972_;
}
}
}
else
{
v___y_2969_ = v_str_2978_;
goto v___jp_2968_;
}
}
v___jp_2998_:
{
switch(v_severity_2995_)
{
case 0:
{
lean_dec(v___y_2999_);
lean_dec_ref(v_pos_2993_);
lean_dec_ref(v_fileName_2992_);
lean_dec(v_kind_2991_);
v_str_2978_ = v_str_3000_;
goto v___jp_2977_;
}
case 1:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_str_3003_; 
v___x_3001_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3002_ = l_Lean_errorNameOfKind_x3f(v_kind_2991_);
lean_dec(v_kind_2991_);
v_str_3003_ = l_Lean_mkErrorStringWithPos(v_fileName_2992_, v_pos_2993_, v_str_3000_, v___y_2999_, v___x_3001_, v___x_3002_);
lean_dec_ref(v_str_3000_);
v_str_2978_ = v_str_3003_;
goto v___jp_2977_;
}
default: 
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v_str_3006_; 
v___x_3004_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3005_ = l_Lean_errorNameOfKind_x3f(v_kind_2991_);
lean_dec(v_kind_2991_);
v_str_3006_ = l_Lean_mkErrorStringWithPos(v_fileName_2992_, v_pos_2993_, v_str_3000_, v___y_2999_, v___x_3004_, v___x_3005_);
lean_dec_ref(v_str_3000_);
v_str_2978_ = v_str_3006_;
goto v___jp_2977_;
}
}
}
v___jp_3007_:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3010_ = lean_string_dec_eq(v_caption_2996_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v_str_3013_; 
v___x_3011_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3012_ = lean_string_append(v_caption_2996_, v___x_3011_);
v_str_3013_ = lean_string_append(v___x_3012_, v_data_2997_);
lean_dec(v_data_2997_);
v___y_2999_ = v___y_3008_;
v_str_3000_ = v_str_3013_;
goto v___jp_2998_;
}
else
{
lean_dec_ref(v_caption_2996_);
v___y_2999_ = v___y_3008_;
v_str_3000_ = v_data_2997_;
goto v___jp_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3015_, lean_object* v_includeEndPos_3016_){
_start:
{
uint8_t v_includeEndPos_boxed_3017_; lean_object* v_res_3018_; 
v_includeEndPos_boxed_3017_ = lean_unbox(v_includeEndPos_3016_);
v_res_3018_ = l_Lean_SerialMessage_toString(v_msg_3015_, v_includeEndPos_boxed_3017_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3019_){
_start:
{
uint8_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = 0;
v___x_3021_ = l_Lean_SerialMessage_toString(v_msg_3019_, v___x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3024_){
_start:
{
lean_object* v_data_3025_; lean_object* v___x_3026_; 
v_data_3025_ = lean_ctor_get(v_msg_3024_, 4);
v___x_3026_ = l_Lean_MessageData_kind(v_data_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Message_kind(v_msg_3027_);
lean_dec_ref(v_msg_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3029_){
_start:
{
lean_object* v_data_3030_; uint8_t v___x_3031_; 
v_data_3030_ = lean_ctor_get(v_msg_3029_, 4);
v___x_3031_ = l_Lean_MessageData_isTrace(v_data_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3032_){
_start:
{
uint8_t v_res_3033_; lean_object* v_r_3034_; 
v_res_3033_ = l_Lean_Message_isTrace(v_msg_3032_);
lean_dec_ref(v_msg_3032_);
v_r_3034_ = lean_box(v_res_3033_);
return v_r_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3035_){
_start:
{
lean_object* v_fileName_3037_; lean_object* v_pos_3038_; lean_object* v_endPos_3039_; uint8_t v_keepFullRange_3040_; uint8_t v_severity_3041_; uint8_t v_isSilent_3042_; lean_object* v_caption_3043_; lean_object* v_data_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3054_; 
v_fileName_3037_ = lean_ctor_get(v_msg_3035_, 0);
v_pos_3038_ = lean_ctor_get(v_msg_3035_, 1);
v_endPos_3039_ = lean_ctor_get(v_msg_3035_, 2);
v_keepFullRange_3040_ = lean_ctor_get_uint8(v_msg_3035_, sizeof(void*)*5);
v_severity_3041_ = lean_ctor_get_uint8(v_msg_3035_, sizeof(void*)*5 + 1);
v_isSilent_3042_ = lean_ctor_get_uint8(v_msg_3035_, sizeof(void*)*5 + 2);
v_caption_3043_ = lean_ctor_get(v_msg_3035_, 3);
v_data_3044_ = lean_ctor_get(v_msg_3035_, 4);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_msg_3035_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3046_ = v_msg_3035_;
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_data_3044_);
lean_inc(v_caption_3043_);
lean_inc(v_endPos_3039_);
lean_inc(v_pos_3038_);
lean_inc(v_fileName_3037_);
lean_dec(v_msg_3035_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_inc(v_data_3044_);
v___x_3048_ = l_Lean_MessageData_toString(v_data_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 4, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_fileName_3037_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_pos_3038_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_endPos_3039_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_caption_3043_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v___x_3048_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*5, v_keepFullRange_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*5 + 1, v_severity_3041_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*5 + 2, v_isSilent_3042_);
v___x_3050_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = l_Lean_MessageData_kind(v_data_3044_);
lean_dec(v_data_3044_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Message_serialize(v_msg_3055_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3058_, uint8_t v_includeEndPos_3059_){
_start:
{
lean_object* v_fileName_3061_; lean_object* v_pos_3062_; lean_object* v_endPos_3063_; uint8_t v_severity_3064_; lean_object* v_caption_3065_; lean_object* v_data_3066_; lean_object* v___x_3067_; lean_object* v___y_3069_; lean_object* v___y_3073_; uint32_t v___y_3074_; lean_object* v_str_3078_; lean_object* v___x_3090_; lean_object* v___y_3092_; lean_object* v_str_3093_; lean_object* v___y_3101_; 
v_fileName_3061_ = lean_ctor_get(v_msg_3058_, 0);
lean_inc_ref(v_fileName_3061_);
v_pos_3062_ = lean_ctor_get(v_msg_3058_, 1);
lean_inc_ref(v_pos_3062_);
v_endPos_3063_ = lean_ctor_get(v_msg_3058_, 2);
lean_inc(v_endPos_3063_);
v_severity_3064_ = lean_ctor_get_uint8(v_msg_3058_, sizeof(void*)*5 + 1);
v_caption_3065_ = lean_ctor_get(v_msg_3058_, 3);
lean_inc_ref(v_caption_3065_);
v_data_3066_ = lean_ctor_get(v_msg_3058_, 4);
lean_inc_n(v_data_3066_, 2);
lean_dec_ref(v_msg_3058_);
v___x_3067_ = l_Lean_MessageData_toString(v_data_3066_);
v___x_3090_ = l_Lean_MessageData_kind(v_data_3066_);
lean_dec(v_data_3066_);
if (v_includeEndPos_3059_ == 0)
{
lean_object* v___x_3107_; 
lean_dec(v_endPos_3063_);
v___x_3107_ = lean_box(0);
v___y_3101_ = v___x_3107_;
goto v___jp_3100_;
}
else
{
v___y_3101_ = v_endPos_3063_;
goto v___jp_3100_;
}
v___jp_3068_:
{
lean_object* v___x_3070_; lean_object* v_str_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3071_ = lean_string_append(v___y_3069_, v___x_3070_);
return v_str_3071_;
}
v___jp_3072_:
{
uint32_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = 10;
v___x_3076_ = lean_uint32_dec_eq(v___y_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
v___y_3069_ = v___y_3073_;
goto v___jp_3068_;
}
else
{
return v___y_3073_;
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
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3084_;
goto v___jp_3072_;
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
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3087_;
goto v___jp_3072_;
}
else
{
lean_object* v_val_3088_; uint32_t v___x_3089_; 
v_val_3088_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_val_3088_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3089_ = lean_unbox_uint32(v_val_3088_);
lean_dec(v_val_3088_);
v___y_3073_ = v_str_3078_;
v___y_3074_ = v___x_3089_;
goto v___jp_3072_;
}
}
}
else
{
v___y_3069_ = v_str_3078_;
goto v___jp_3068_;
}
}
v___jp_3091_:
{
switch(v_severity_3064_)
{
case 0:
{
lean_dec(v___y_3092_);
lean_dec(v___x_3090_);
lean_dec_ref(v_pos_3062_);
lean_dec_ref(v_fileName_3061_);
v_str_3078_ = v_str_3093_;
goto v___jp_3077_;
}
case 1:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_str_3096_; 
v___x_3094_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3095_ = l_Lean_errorNameOfKind_x3f(v___x_3090_);
lean_dec(v___x_3090_);
v_str_3096_ = l_Lean_mkErrorStringWithPos(v_fileName_3061_, v_pos_3062_, v_str_3093_, v___y_3092_, v___x_3094_, v___x_3095_);
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
v_str_3099_ = l_Lean_mkErrorStringWithPos(v_fileName_3061_, v_pos_3062_, v_str_3093_, v___y_3092_, v___x_3097_, v___x_3098_);
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
v___x_3103_ = lean_string_dec_eq(v_caption_3065_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_str_3106_; 
v___x_3104_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3105_ = lean_string_append(v_caption_3065_, v___x_3104_);
v_str_3106_ = lean_string_append(v___x_3105_, v___x_3067_);
lean_dec_ref(v___x_3067_);
v___y_3092_ = v___y_3101_;
v_str_3093_ = v_str_3106_;
goto v___jp_3091_;
}
else
{
lean_dec_ref(v_caption_3065_);
v___y_3092_ = v___y_3101_;
v_str_3093_ = v___x_3067_;
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
lean_object* v___x_3303_; uint8_t v_severity_3304_; 
v___x_3303_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v_severity_3304_ = lean_ctor_get_uint8(v___x_3303_, sizeof(void*)*5 + 1);
if (v_severity_3304_ == 2)
{
uint8_t v___x_3305_; 
v___x_3305_ = 1;
return v___x_3305_;
}
else
{
size_t v___x_3306_; size_t v___x_3307_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3300_, v___x_3306_);
v_i_3300_ = v___x_3307_;
goto _start;
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
return v___x_3358_;
}
else
{
if (v___x_3358_ == 0)
{
return v___x_3358_;
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
uint8_t v___x_1809__boxed_3381_; size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; uint8_t v_res_3384_; lean_object* v_r_3385_; 
v___x_1809__boxed_3381_ = lean_unbox(v___x_3377_);
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3381_, v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_);
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
uint8_t v___x_1826__boxed_3417_; size_t v_i_boxed_3418_; size_t v_stop_boxed_3419_; uint8_t v_res_3420_; lean_object* v_r_3421_; 
v___x_1826__boxed_3417_ = lean_unbox(v___x_3413_);
v_i_boxed_3418_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_stop_boxed_3419_ = lean_unbox_usize(v_stop_3416_);
lean_dec(v_stop_3416_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3417_, v_as_3414_, v_i_boxed_3418_, v_stop_boxed_3419_);
lean_dec_ref(v_as_3414_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3422_, lean_object* v_x_3423_){
_start:
{
uint8_t v___x_1834__boxed_3424_; uint8_t v_res_3425_; lean_object* v_r_3426_; 
v___x_1834__boxed_3424_ = lean_unbox(v___x_3422_);
v_res_3425_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3424_, v_x_3423_);
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
return v___x_3434_;
}
else
{
if (v___x_3434_ == 0)
{
return v___x_3434_;
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
uint8_t v___x_1877__boxed_3440_; uint8_t v_res_3441_; lean_object* v_r_3442_; 
v___x_1877__boxed_3440_ = lean_unbox(v___x_3438_);
v_res_3441_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3440_, v_t_3439_);
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
size_t v___x_3720_; size_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = lean_usize_of_nat(v___x_3718_);
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3716_, v___x_3720_, v___x_3721_, v_x_3715_);
return v___x_3722_;
}
}
else
{
lean_object* v_vs_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v_vs_3723_ = lean_ctor_get(v_x_3714_, 0);
v___x_3724_ = lean_unsigned_to_nat(0u);
v___x_3725_ = lean_array_get_size(v_vs_3723_);
v___x_3726_ = lean_nat_dec_lt(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
return v_x_3715_;
}
else
{
size_t v___x_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((size_t)0ULL);
v___x_3728_ = lean_usize_of_nat(v___x_3725_);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3723_, v___x_3727_, v___x_3728_, v_x_3715_);
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3730_, size_t v_i_3731_, size_t v_stop_3732_, lean_object* v_b_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_usize_dec_eq(v_i_3731_, v_stop_3732_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3736_; size_t v___x_3737_; size_t v___x_3738_; 
v___x_3735_ = lean_array_uget_borrowed(v_as_3730_, v_i_3731_);
v___x_3736_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3735_, v_b_3733_);
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3731_, v___x_3737_);
v_i_3731_ = v___x_3738_;
v_b_3733_ = v___x_3736_;
goto _start;
}
else
{
return v_b_3733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3740_, lean_object* v_i_3741_, lean_object* v_stop_3742_, lean_object* v_b_3743_){
_start:
{
size_t v_i_boxed_3744_; size_t v_stop_boxed_3745_; lean_object* v_res_3746_; 
v_i_boxed_3744_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_stop_boxed_3745_ = lean_unbox_usize(v_stop_3742_);
lean_dec(v_stop_3742_);
v_res_3746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3740_, v_i_boxed_3744_, v_stop_boxed_3745_, v_b_3743_);
lean_dec_ref(v_as_3740_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3747_, lean_object* v_x_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3747_, v_x_3748_);
lean_dec_ref(v_x_3747_);
return v_res_3749_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3751_, size_t v_x_3752_, size_t v_x_3753_, lean_object* v_x_3754_){
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
v___x_3766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3759_, v___x_3763_, v___x_3765_, v_x_3754_);
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
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3755_, v___x_3771_, v___x_3772_, v___x_3766_);
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
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3774_, v___x_3778_, v___x_3779_, v_x_3754_);
return v___x_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_){
_start:
{
size_t v_x_1152__boxed_3785_; size_t v_x_1153__boxed_3786_; lean_object* v_res_3787_; 
v_x_1152__boxed_3785_ = lean_unbox_usize(v_x_3782_);
lean_dec(v_x_3782_);
v_x_1153__boxed_3786_ = lean_unbox_usize(v_x_3783_);
lean_dec(v_x_3783_);
v_res_3787_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3781_, v_x_1152__boxed_3785_, v_x_1153__boxed_3786_, v_x_3784_);
lean_dec_ref(v_x_3781_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3788_, lean_object* v_init_3789_, lean_object* v_start_3790_){
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
v___x_3799_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3793_, v___x_3798_, v_shift_3795_, v_init_3789_);
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
v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3794_, v___x_3802_, v___x_3803_, v___x_3799_);
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
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3794_, v___x_3808_, v___x_3809_, v_init_3789_);
return v___x_3810_;
}
}
}
else
{
lean_object* v_root_3811_; lean_object* v_tail_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_root_3811_ = lean_ctor_get(v_t_3788_, 0);
v_tail_3812_ = lean_ctor_get(v_t_3788_, 1);
v___x_3813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3811_, v_init_3789_);
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
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3812_, v___x_3816_, v___x_3817_, v___x_3813_);
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3819_, lean_object* v_init_3820_, lean_object* v_start_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3819_, v_init_3820_, v_start_3821_);
lean_dec(v_start_3821_);
lean_dec_ref(v_t_3819_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3823_){
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
v___x_3832_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3828_, v___x_3827_, v___x_3826_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3840_, size_t v_i_3841_, size_t v_stop_3842_, lean_object* v_b_3843_){
_start:
{
lean_object* v___y_3845_; uint8_t v___x_3849_; 
v___x_3849_ = lean_usize_dec_eq(v_i_3841_, v_stop_3842_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; uint8_t v_severity_3851_; 
v___x_3850_ = lean_array_uget_borrowed(v_as_3840_, v_i_3841_);
v_severity_3851_ = lean_ctor_get_uint8(v___x_3850_, sizeof(void*)*5 + 1);
if (v_severity_3851_ == 1)
{
lean_object* v___x_3852_; 
lean_inc(v___x_3850_);
v___x_3852_ = l_Lean_PersistentArray_push___redArg(v_b_3843_, v___x_3850_);
v___y_3845_ = v___x_3852_;
goto v___jp_3844_;
}
else
{
v___y_3845_ = v_b_3843_;
goto v___jp_3844_;
}
}
else
{
return v_b_3843_;
}
v___jp_3844_:
{
size_t v___x_3846_; size_t v___x_3847_; 
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3841_, v___x_3846_);
v_i_3841_ = v___x_3847_;
v_b_3843_ = v___y_3845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3853_, lean_object* v_i_3854_, lean_object* v_stop_3855_, lean_object* v_b_3856_){
_start:
{
size_t v_i_boxed_3857_; size_t v_stop_boxed_3858_; lean_object* v_res_3859_; 
v_i_boxed_3857_ = lean_unbox_usize(v_i_3854_);
lean_dec(v_i_3854_);
v_stop_boxed_3858_ = lean_unbox_usize(v_stop_3855_);
lean_dec(v_stop_3855_);
v_res_3859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3853_, v_i_boxed_3857_, v_stop_boxed_3858_, v_b_3856_);
lean_dec_ref(v_as_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3860_, lean_object* v_x_3861_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 0)
{
lean_object* v_cs_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v_cs_3862_ = lean_ctor_get(v_x_3860_, 0);
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = lean_array_get_size(v_cs_3862_);
v___x_3865_ = lean_nat_dec_lt(v___x_3863_, v___x_3864_);
if (v___x_3865_ == 0)
{
return v_x_3861_;
}
else
{
size_t v___x_3866_; size_t v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = ((size_t)0ULL);
v___x_3867_ = lean_usize_of_nat(v___x_3864_);
v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3862_, v___x_3866_, v___x_3867_, v_x_3861_);
return v___x_3868_;
}
}
else
{
lean_object* v_vs_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_vs_3869_ = lean_ctor_get(v_x_3860_, 0);
v___x_3870_ = lean_unsigned_to_nat(0u);
v___x_3871_ = lean_array_get_size(v_vs_3869_);
v___x_3872_ = lean_nat_dec_lt(v___x_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
return v_x_3861_;
}
else
{
size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = lean_usize_of_nat(v___x_3871_);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3869_, v___x_3873_, v___x_3874_, v_x_3861_);
return v___x_3875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3876_, size_t v_i_3877_, size_t v_stop_3878_, lean_object* v_b_3879_){
_start:
{
uint8_t v___x_3880_; 
v___x_3880_ = lean_usize_dec_eq(v_i_3877_, v_stop_3878_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; size_t v___x_3883_; size_t v___x_3884_; 
v___x_3881_ = lean_array_uget_borrowed(v_as_3876_, v_i_3877_);
v___x_3882_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3881_, v_b_3879_);
v___x_3883_ = ((size_t)1ULL);
v___x_3884_ = lean_usize_add(v_i_3877_, v___x_3883_);
v_i_3877_ = v___x_3884_;
v_b_3879_ = v___x_3882_;
goto _start;
}
else
{
return v_b_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3886_, lean_object* v_i_3887_, lean_object* v_stop_3888_, lean_object* v_b_3889_){
_start:
{
size_t v_i_boxed_3890_; size_t v_stop_boxed_3891_; lean_object* v_res_3892_; 
v_i_boxed_3890_ = lean_unbox_usize(v_i_3887_);
lean_dec(v_i_3887_);
v_stop_boxed_3891_ = lean_unbox_usize(v_stop_3888_);
lean_dec(v_stop_3888_);
v_res_3892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3886_, v_i_boxed_3890_, v_stop_boxed_3891_, v_b_3889_);
lean_dec_ref(v_as_3886_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3893_, v_x_3894_);
lean_dec_ref(v_x_3893_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3896_, size_t v_x_3897_, size_t v_x_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 0)
{
lean_object* v_cs_3900_; lean_object* v___x_3901_; size_t v___x_3902_; lean_object* v_j_3903_; lean_object* v___x_3904_; size_t v___x_3905_; size_t v___x_3906_; size_t v___x_3907_; size_t v___x_3908_; size_t v___x_3909_; size_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v_cs_3900_ = lean_ctor_get(v_x_3896_, 0);
v___x_3901_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3902_ = lean_usize_shift_right(v_x_3897_, v_x_3898_);
v_j_3903_ = lean_usize_to_nat(v___x_3902_);
v___x_3904_ = lean_array_get_borrowed(v___x_3901_, v_cs_3900_, v_j_3903_);
v___x_3905_ = ((size_t)1ULL);
v___x_3906_ = lean_usize_shift_left(v___x_3905_, v_x_3898_);
v___x_3907_ = lean_usize_sub(v___x_3906_, v___x_3905_);
v___x_3908_ = lean_usize_land(v_x_3897_, v___x_3907_);
v___x_3909_ = ((size_t)5ULL);
v___x_3910_ = lean_usize_sub(v_x_3898_, v___x_3909_);
v___x_3911_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3904_, v___x_3908_, v___x_3910_, v_x_3899_);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = lean_nat_add(v_j_3903_, v___x_3912_);
lean_dec(v_j_3903_);
v___x_3914_ = lean_array_get_size(v_cs_3900_);
v___x_3915_ = lean_nat_dec_lt(v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_dec(v___x_3913_);
return v___x_3911_;
}
else
{
size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_usize_of_nat(v___x_3913_);
lean_dec(v___x_3913_);
v___x_3917_ = lean_usize_of_nat(v___x_3914_);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3900_, v___x_3916_, v___x_3917_, v___x_3911_);
return v___x_3918_;
}
}
else
{
lean_object* v_vs_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; 
v_vs_3919_ = lean_ctor_get(v_x_3896_, 0);
v___x_3920_ = lean_usize_to_nat(v_x_3897_);
v___x_3921_ = lean_array_get_size(v_vs_3919_);
v___x_3922_ = lean_nat_dec_lt(v___x_3920_, v___x_3921_);
if (v___x_3922_ == 0)
{
lean_dec(v___x_3920_);
return v_x_3899_;
}
else
{
size_t v___x_3923_; size_t v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_usize_of_nat(v___x_3920_);
lean_dec(v___x_3920_);
v___x_3924_ = lean_usize_of_nat(v___x_3921_);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3919_, v___x_3923_, v___x_3924_, v_x_3899_);
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_, lean_object* v_x_3929_){
_start:
{
size_t v_x_1151__boxed_3930_; size_t v_x_1152__boxed_3931_; lean_object* v_res_3932_; 
v_x_1151__boxed_3930_ = lean_unbox_usize(v_x_3927_);
lean_dec(v_x_3927_);
v_x_1152__boxed_3931_ = lean_unbox_usize(v_x_3928_);
lean_dec(v_x_3928_);
v_res_3932_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3926_, v_x_1151__boxed_3930_, v_x_1152__boxed_3931_, v_x_3929_);
lean_dec_ref(v_x_3926_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3933_, lean_object* v_init_3934_, lean_object* v_start_3935_){
_start:
{
lean_object* v___x_3936_; uint8_t v___x_3937_; 
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = lean_nat_dec_eq(v_start_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v_root_3938_; lean_object* v_tail_3939_; size_t v_shift_3940_; lean_object* v_tailOff_3941_; uint8_t v___x_3942_; 
v_root_3938_ = lean_ctor_get(v_t_3933_, 0);
v_tail_3939_ = lean_ctor_get(v_t_3933_, 1);
v_shift_3940_ = lean_ctor_get_usize(v_t_3933_, 4);
v_tailOff_3941_ = lean_ctor_get(v_t_3933_, 3);
v___x_3942_ = lean_nat_dec_le(v_tailOff_3941_, v_start_3935_);
if (v___x_3942_ == 0)
{
size_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3943_ = lean_usize_of_nat(v_start_3935_);
v___x_3944_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3938_, v___x_3943_, v_shift_3940_, v_init_3934_);
v___x_3945_ = lean_array_get_size(v_tail_3939_);
v___x_3946_ = lean_nat_dec_lt(v___x_3936_, v___x_3945_);
if (v___x_3946_ == 0)
{
return v___x_3944_;
}
else
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((size_t)0ULL);
v___x_3948_ = lean_usize_of_nat(v___x_3945_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3939_, v___x_3947_, v___x_3948_, v___x_3944_);
return v___x_3949_;
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3950_ = lean_nat_sub(v_start_3935_, v_tailOff_3941_);
v___x_3951_ = lean_array_get_size(v_tail_3939_);
v___x_3952_ = lean_nat_dec_lt(v___x_3950_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_dec(v___x_3950_);
return v_init_3934_;
}
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_usize_of_nat(v___x_3950_);
lean_dec(v___x_3950_);
v___x_3954_ = lean_usize_of_nat(v___x_3951_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3939_, v___x_3953_, v___x_3954_, v_init_3934_);
return v___x_3955_;
}
}
}
else
{
lean_object* v_root_3956_; lean_object* v_tail_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_root_3956_ = lean_ctor_get(v_t_3933_, 0);
v_tail_3957_ = lean_ctor_get(v_t_3933_, 1);
v___x_3958_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3956_, v_init_3934_);
v___x_3959_ = lean_array_get_size(v_tail_3957_);
v___x_3960_ = lean_nat_dec_lt(v___x_3936_, v___x_3959_);
if (v___x_3960_ == 0)
{
return v___x_3958_;
}
else
{
size_t v___x_3961_; size_t v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = lean_usize_of_nat(v___x_3959_);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3957_, v___x_3961_, v___x_3962_, v___x_3958_);
return v___x_3963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3964_, lean_object* v_init_3965_, lean_object* v_start_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3964_, v_init_3965_, v_start_3966_);
lean_dec(v_start_3966_);
lean_dec_ref(v_t_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3968_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v_unreported_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3982_; 
v___x_3969_ = lean_unsigned_to_nat(32u);
v___x_3970_ = lean_mk_empty_array_with_capacity(v___x_3969_);
lean_dec_ref(v___x_3970_);
v___x_3971_ = lean_unsigned_to_nat(0u);
v___x_3972_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3973_ = lean_ctor_get(v_log_3968_, 1);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_log_3968_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; lean_object* v_unused_3984_; 
v_unused_3983_ = lean_ctor_get(v_log_3968_, 2);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_log_3968_, 0);
lean_dec(v_unused_3984_);
v___x_3975_ = v_log_3968_;
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_unreported_3973_);
lean_dec(v_log_3968_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3977_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3973_, v___x_3972_, v___x_3971_);
lean_dec_ref(v_unreported_3973_);
v___x_3978_ = l_Lean_NameSet_empty;
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 2, v___x_3978_);
lean_ctor_set(v___x_3975_, 1, v___x_3977_);
lean_ctor_set(v___x_3975_, 0, v___x_3972_);
v___x_3980_ = v___x_3975_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3985_, lean_object* v_log_3986_, lean_object* v_f_3987_){
_start:
{
lean_object* v_unreported_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_unreported_3988_ = lean_ctor_get(v_log_3986_, 1);
lean_inc_ref(v_unreported_3988_);
lean_dec_ref(v_log_3986_);
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = l_Lean_PersistentArray_forM___redArg(v_inst_3985_, v_unreported_3988_, v_f_3987_, v___x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3991_, lean_object* v_inst_3992_, lean_object* v_log_3993_, lean_object* v_f_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_MessageLog_forM___redArg(v_inst_3992_, v_log_3993_, v_f_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3996_){
_start:
{
lean_object* v_unreported_3997_; lean_object* v___x_3998_; 
v_unreported_3997_ = lean_ctor_get(v_log_3996_, 1);
v___x_3998_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_MessageLog_toList(v_log_3999_);
lean_dec_ref(v_log_3999_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4001_){
_start:
{
lean_object* v_unreported_4002_; lean_object* v___x_4003_; 
v_unreported_4002_ = lean_ctor_get(v_log_4001_, 1);
v___x_4003_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_MessageLog_toArray(v_log_4004_);
lean_dec_ref(v_log_4004_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4006_){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_unsigned_to_nat(2u);
v___x_4008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v_msg_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4009_){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
lean_ctor_set(v___x_4011_, 1, v_msg_4009_);
v___x_4012_ = l_Lean_MessageData_nestD(v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4013_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = l_Lean_MessageData_ofExpr(v_e_4013_);
v___x_4015_ = l_Lean_indentD(v___x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4016_, lean_object* v_msg_4017_){
_start:
{
lean_object* v_env_4019_; lean_object* v_mctx_4020_; lean_object* v_lctx_4021_; lean_object* v_opts_4022_; lean_object* v_currNamespace_4023_; lean_object* v_openDecls_4024_; lean_object* v___x_4025_; lean_object* v_msg_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_env_4019_ = lean_ctor_get(v_ctx_4016_, 0);
v_mctx_4020_ = lean_ctor_get(v_ctx_4016_, 1);
v_lctx_4021_ = lean_ctor_get(v_ctx_4016_, 2);
v_opts_4022_ = lean_ctor_get(v_ctx_4016_, 3);
v_currNamespace_4023_ = lean_ctor_get(v_ctx_4016_, 4);
v_openDecls_4024_ = lean_ctor_get(v_ctx_4016_, 5);
lean_inc(v_openDecls_4024_);
lean_inc(v_currNamespace_4023_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v_currNamespace_4023_);
lean_ctor_set(v___x_4025_, 1, v_openDecls_4024_);
v_msg_4026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4026_, 0, v___x_4025_);
lean_ctor_set(v_msg_4026_, 1, v_msg_4017_);
lean_inc_ref(v_opts_4022_);
lean_inc_ref(v_lctx_4021_);
lean_inc_ref(v_mctx_4020_);
lean_inc_ref(v_env_4019_);
v___x_4027_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4027_, 0, v_env_4019_);
lean_ctor_set(v___x_4027_, 1, v_mctx_4020_);
lean_ctor_set(v___x_4027_, 2, v_lctx_4021_);
lean_ctor_set(v___x_4027_, 3, v_opts_4022_);
v___x_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
v___x_4029_ = l_Lean_MessageData_format(v_msg_4026_, v___x_4028_);
v___x_4030_ = l_Std_Format_defWidth;
v___x_4031_ = lean_unsigned_to_nat(0u);
v___x_4032_ = l_Std_Format_pretty(v___x_4029_, v___x_4030_, v___x_4031_, v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4033_, lean_object* v_msg_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4033_, v_msg_4034_);
lean_dec_ref(v_ctx_4033_);
return v_res_4036_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4037_, lean_object* v_a_4038_, uint8_t v_b_4039_){
_start:
{
lean_object* v_str_4040_; lean_object* v_startInclusive_4041_; lean_object* v_endExclusive_4042_; lean_object* v___x_4043_; uint8_t v_decide_4044_; 
v_str_4040_ = lean_ctor_get(v_s_4037_, 0);
v_startInclusive_4041_ = lean_ctor_get(v_s_4037_, 1);
v_endExclusive_4042_ = lean_ctor_get(v_s_4037_, 2);
v___x_4043_ = lean_nat_sub(v_endExclusive_4042_, v_startInclusive_4041_);
v_decide_4044_ = lean_nat_dec_eq(v_a_4038_, v___x_4043_);
lean_dec(v___x_4043_);
if (v_decide_4044_ == 0)
{
lean_object* v___x_4045_; uint32_t v___x_4046_; uint32_t v___x_4047_; uint8_t v___x_4048_; 
v___x_4045_ = lean_nat_add(v_startInclusive_4041_, v_a_4038_);
lean_dec(v_a_4038_);
v___x_4046_ = lean_string_utf8_get_fast(v_str_4040_, v___x_4045_);
v___x_4047_ = 10;
v___x_4048_ = lean_uint32_dec_eq(v___x_4046_, v___x_4047_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_string_utf8_next_fast(v_str_4040_, v___x_4045_);
lean_dec(v___x_4045_);
v___x_4050_ = lean_nat_sub(v___x_4049_, v_startInclusive_4041_);
v_a_4038_ = v___x_4050_;
v_b_4039_ = v___x_4048_;
goto _start;
}
else
{
lean_dec(v___x_4045_);
return v___x_4048_;
}
}
else
{
lean_dec(v_a_4038_);
return v_b_4039_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4052_, lean_object* v_a_4053_, lean_object* v_b_4054_){
_start:
{
uint8_t v_b_boxed_4055_; uint8_t v_res_4056_; lean_object* v_r_4057_; 
v_b_boxed_4055_ = lean_unbox(v_b_4054_);
v_res_4056_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4052_, v_a_4053_, v_b_boxed_4055_);
lean_dec_ref(v_s_4052_);
v_r_4057_ = lean_box(v_res_4056_);
return v_r_4057_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4058_){
_start:
{
lean_object* v_searcher_4059_; uint8_t v___x_4060_; uint8_t v___x_4061_; 
v_searcher_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = 0;
v___x_4061_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4058_, v_searcher_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4062_){
_start:
{
uint8_t v_res_4063_; lean_object* v_r_4064_; 
v_res_4063_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4062_);
lean_dec_ref(v_s_4062_);
v_r_4064_ = lean_box(v_res_4063_);
return v_r_4064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4065_, lean_object* v_val_4066_, lean_object* v_a_4067_, lean_object* v_b_4068_){
_start:
{
uint8_t v_decide_4069_; 
v_decide_4069_ = lean_nat_dec_eq(v_a_4067_, v___x_4065_);
if (v_decide_4069_ == 0)
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = lean_string_utf8_next_fast(v_val_4066_, v_a_4067_);
lean_dec(v_a_4067_);
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_add(v_b_4068_, v___x_4071_);
lean_dec(v_b_4068_);
v_a_4067_ = v___x_4070_;
v_b_4068_ = v___x_4072_;
goto _start;
}
else
{
lean_dec(v_a_4067_);
return v_b_4068_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4074_, lean_object* v_val_4075_, lean_object* v_a_4076_, lean_object* v_b_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4074_, v_val_4075_, v_a_4076_, v_b_4077_);
lean_dec_ref(v_val_4075_);
lean_dec(v___x_4074_);
return v_res_4078_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4080_ = l_Lean_MessageData_ofFormat(v___x_4079_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_4085_ = l_Lean_MessageData_ofFormat(v___x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_4090_ = l_Lean_MessageData_ofFormat(v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4091_, lean_object* v_maxInlineLength_4092_, lean_object* v_ctx_4093_){
_start:
{
lean_object* v_msg_4095_; lean_object* v___x_4096_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_msg_4095_ = l_Lean_MessageData_ofExpr(v_e_4091_);
lean_inc_ref(v_msg_4095_);
v___x_4096_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4093_, v_msg_4095_);
v___x_4101_ = lean_unsigned_to_nat(0u);
v___x_4102_ = lean_string_utf8_byte_size(v___x_4096_);
lean_inc_ref(v___x_4096_);
v___x_4103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4096_);
lean_ctor_set(v___x_4103_, 1, v___x_4101_);
lean_ctor_set(v___x_4103_, 2, v___x_4102_);
v___x_4104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4102_, v___x_4096_, v___x_4101_, v___x_4101_);
lean_dec_ref(v___x_4096_);
v___x_4105_ = lean_nat_dec_lt(v_maxInlineLength_4092_, v___x_4104_);
lean_dec(v___x_4104_);
if (v___x_4105_ == 0)
{
uint8_t v___x_4106_; 
v___x_4106_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4103_);
lean_dec_ref_known(v___x_4103_, 3);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4107_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set(v___x_4108_, 1, v_msg_4095_);
v___x_4109_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
return v___x_4110_;
}
else
{
goto v___jp_4097_;
}
}
else
{
lean_dec_ref_known(v___x_4103_, 3);
goto v___jp_4097_;
}
v___jp_4097_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = l_Lean_indentD(v_msg_4095_);
v___x_4099_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
return v___x_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4111_, lean_object* v_maxInlineLength_4112_, lean_object* v_ctx_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_inlineExpr___lam__0(v_e_4111_, v_maxInlineLength_4112_, v_ctx_4113_);
lean_dec_ref(v_ctx_4113_);
lean_dec(v_maxInlineLength_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4116_, lean_object* v_x_4117_){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4119_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4120_ = l_Lean_MessageData_ofExpr(v_e_4116_);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_inlineExpr___lam__2(v_e_4124_, v_x_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4128_, lean_object* v_maxInlineLength_4129_){
_start:
{
lean_object* v___f_4130_; lean_object* v___f_4131_; lean_object* v___f_4132_; lean_object* v___x_4133_; 
lean_inc_ref_n(v_e_4128_, 2);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4130_, 0, v_e_4128_);
lean_closure_set(v___f_4130_, 1, v_maxInlineLength_4129_);
v___f_4131_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4131_, 0, v_e_4128_);
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4132_, 0, v_e_4128_);
v___x_4133_ = l_Lean_MessageData_lazy(v___f_4130_, v___f_4131_, v___f_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4134_, lean_object* v___x_4135_, lean_object* v_val_4136_, lean_object* v_inst_4137_, lean_object* v_R_4138_, lean_object* v_a_4139_, lean_object* v_b_4140_, lean_object* v_c_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4134_, v_val_4136_, v_a_4139_, v_b_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4143_, lean_object* v___x_4144_, lean_object* v_val_4145_, lean_object* v_inst_4146_, lean_object* v_R_4147_, lean_object* v_a_4148_, lean_object* v_b_4149_, lean_object* v_c_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4143_, v___x_4144_, v_val_4145_, v_inst_4146_, v_R_4147_, v_a_4148_, v_b_4149_, v_c_4150_);
lean_dec_ref(v_val_4145_);
lean_dec_ref(v___x_4144_);
lean_dec(v___x_4143_);
return v_res_4151_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4152_, lean_object* v_inst_4153_, lean_object* v_R_4154_, lean_object* v_a_4155_, uint8_t v_b_4156_, lean_object* v_c_4157_){
_start:
{
uint8_t v___x_4158_; 
v___x_4158_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4152_, v_a_4155_, v_b_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4159_, lean_object* v_inst_4160_, lean_object* v_R_4161_, lean_object* v_a_4162_, lean_object* v_b_4163_, lean_object* v_c_4164_){
_start:
{
uint8_t v_b_boxed_4165_; uint8_t v_res_4166_; lean_object* v_r_4167_; 
v_b_boxed_4165_ = lean_unbox(v_b_4163_);
v_res_4166_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4159_, v_inst_4160_, v_R_4161_, v_a_4162_, v_b_boxed_4165_, v_c_4164_);
lean_dec_ref(v_s_4159_);
v_r_4167_ = lean_box(v_res_4166_);
return v_r_4167_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4172_ = l_Lean_MessageData_ofFormat(v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4173_, lean_object* v_maxInlineLength_4174_, lean_object* v_ctx_4175_){
_start:
{
lean_object* v_msg_4177_; lean_object* v___x_4178_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_msg_4177_ = l_Lean_MessageData_ofExpr(v_e_4173_);
lean_inc_ref(v_msg_4177_);
v___x_4178_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4175_, v_msg_4177_);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = lean_string_utf8_byte_size(v___x_4178_);
lean_inc_ref(v___x_4178_);
v___x_4183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4178_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
v___x_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4182_, v___x_4178_, v___x_4181_, v___x_4181_);
lean_dec_ref(v___x_4178_);
v___x_4185_ = lean_nat_dec_lt(v_maxInlineLength_4174_, v___x_4184_);
lean_dec(v___x_4184_);
if (v___x_4185_ == 0)
{
uint8_t v___x_4186_; 
v___x_4186_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4183_);
lean_dec_ref_known(v___x_4183_, 3);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4187_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
lean_ctor_set(v___x_4188_, 1, v_msg_4177_);
v___x_4189_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4188_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
return v___x_4190_;
}
else
{
goto v___jp_4179_;
}
}
else
{
lean_dec_ref_known(v___x_4183_, 3);
goto v___jp_4179_;
}
v___jp_4179_:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_indentD(v_msg_4177_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4191_, lean_object* v_maxInlineLength_4192_, lean_object* v_ctx_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_inlineExprTrailing___lam__0(v_e_4191_, v_maxInlineLength_4192_, v_ctx_4193_);
lean_dec_ref(v_ctx_4193_);
lean_dec(v_maxInlineLength_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4199_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4200_ = l_Lean_MessageData_ofExpr(v_e_4196_);
v___x_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_inlineExprTrailing___lam__2(v_e_4204_, v_x_4205_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4208_, lean_object* v_maxInlineLength_4209_){
_start:
{
lean_object* v___f_4210_; lean_object* v___f_4211_; lean_object* v___f_4212_; lean_object* v___x_4213_; 
lean_inc_ref_n(v_e_4208_, 2);
v___f_4210_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4210_, 0, v_e_4208_);
lean_closure_set(v___f_4210_, 1, v_maxInlineLength_4209_);
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4211_, 0, v_e_4208_);
v___f_4212_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4212_, 0, v_e_4208_);
v___x_4213_ = l_Lean_MessageData_lazy(v___f_4210_, v___f_4211_, v___f_4212_);
return v___x_4213_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4218_ = l_Lean_MessageData_ofFormat(v___x_4217_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4223_ = l_Lean_MessageData_ofFormat(v___x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4224_){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
lean_ctor_set(v___x_4226_, 1, v_msg_4224_);
v___x_4227_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4226_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_msg_4231_){
_start:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_apply_1(v_inst_4229_, v_msg_4231_);
v___x_4233_ = lean_apply_2(v_inst_4230_, lean_box(0), v___x_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4234_, lean_object* v_inst_4235_){
_start:
{
lean_object* v___f_4236_; 
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4236_, 0, v_inst_4235_);
lean_closure_set(v___f_4236_, 1, v_inst_4234_);
return v___f_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4237_, lean_object* v_n_4238_, lean_object* v_inst_4239_, lean_object* v_inst_4240_){
_start:
{
lean_object* v___f_4241_; 
v___f_4241_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4241_, 0, v_inst_4240_);
lean_closure_set(v___f_4241_, 1, v_inst_4239_);
return v___f_4241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = lean_unsigned_to_nat(32u);
v___x_4243_ = lean_mk_empty_array_with_capacity(v___x_4242_);
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
return v___x_4244_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4245_ = ((size_t)5ULL);
v___x_4246_ = lean_unsigned_to_nat(0u);
v___x_4247_ = lean_unsigned_to_nat(32u);
v___x_4248_ = lean_mk_empty_array_with_capacity(v___x_4247_);
v___x_4249_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4250_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
lean_ctor_set(v___x_4250_, 1, v___x_4248_);
lean_ctor_set(v___x_4250_, 2, v___x_4246_);
lean_ctor_set(v___x_4250_, 3, v___x_4246_);
lean_ctor_set_usize(v___x_4250_, 4, v___x_4245_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4251_ = lean_box(1);
v___x_4252_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4253_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
lean_ctor_set(v___x_4254_, 1, v___x_4252_);
lean_ctor_set(v___x_4254_, 2, v___x_4251_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4255_, lean_object* v_msgData_4256_, lean_object* v_toPure_4257_, lean_object* v_opts_4258_){
_start:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4259_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4260_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4261_, 0, v_env_4255_);
lean_ctor_set(v___x_4261_, 1, v___x_4259_);
lean_ctor_set(v___x_4261_, 2, v___x_4260_);
lean_ctor_set(v___x_4261_, 3, v_opts_4258_);
v___x_4262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
lean_ctor_set(v___x_4262_, 1, v_msgData_4256_);
v___x_4263_ = lean_apply_2(v_toPure_4257_, lean_box(0), v___x_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4264_, lean_object* v_toPure_4265_, lean_object* v_toBind_4266_, lean_object* v_inst_4267_, lean_object* v_env_4268_){
_start:
{
lean_object* v___f_4269_; lean_object* v___x_4270_; 
v___f_4269_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4269_, 0, v_env_4268_);
lean_closure_set(v___f_4269_, 1, v_msgData_4264_);
lean_closure_set(v___f_4269_, 2, v_toPure_4265_);
v___x_4270_ = lean_apply_4(v_toBind_4266_, lean_box(0), lean_box(0), v_inst_4267_, v___f_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4271_, lean_object* v_inst_4272_, lean_object* v_inst_4273_, lean_object* v_msgData_4274_){
_start:
{
lean_object* v_toApplicative_4275_; lean_object* v_toBind_4276_; lean_object* v_getEnv_4277_; lean_object* v_toPure_4278_; lean_object* v___f_4279_; lean_object* v___x_4280_; 
v_toApplicative_4275_ = lean_ctor_get(v_inst_4271_, 0);
lean_inc_ref(v_toApplicative_4275_);
v_toBind_4276_ = lean_ctor_get(v_inst_4271_, 1);
lean_inc_n(v_toBind_4276_, 2);
lean_dec_ref(v_inst_4271_);
v_getEnv_4277_ = lean_ctor_get(v_inst_4272_, 0);
lean_inc(v_getEnv_4277_);
lean_dec_ref(v_inst_4272_);
v_toPure_4278_ = lean_ctor_get(v_toApplicative_4275_, 1);
lean_inc(v_toPure_4278_);
lean_dec_ref(v_toApplicative_4275_);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4279_, 0, v_msgData_4274_);
lean_closure_set(v___f_4279_, 1, v_toPure_4278_);
lean_closure_set(v___f_4279_, 2, v_toBind_4276_);
lean_closure_set(v___f_4279_, 3, v_inst_4273_);
v___x_4280_ = lean_apply_4(v_toBind_4276_, lean_box(0), lean_box(0), v_getEnv_4277_, v___f_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4281_, lean_object* v_inst_4282_, lean_object* v_inst_4283_, lean_object* v_inst_4284_, lean_object* v_msgData_4285_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Lean_addMessageContextPartial___redArg(v_inst_4282_, v_inst_4283_, v_inst_4284_, v_msgData_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4287_, lean_object* v_mctx_4288_, lean_object* v_lctx_4289_, lean_object* v_msgData_4290_, lean_object* v_toPure_4291_, lean_object* v_opts_4292_){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4293_, 0, v_env_4287_);
lean_ctor_set(v___x_4293_, 1, v_mctx_4288_);
lean_ctor_set(v___x_4293_, 2, v_lctx_4289_);
lean_ctor_set(v___x_4293_, 3, v_opts_4292_);
v___x_4294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v_msgData_4290_);
v___x_4295_ = lean_apply_2(v_toPure_4291_, lean_box(0), v___x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4296_, lean_object* v_mctx_4297_, lean_object* v_msgData_4298_, lean_object* v_toPure_4299_, lean_object* v_toBind_4300_, lean_object* v_inst_4301_, lean_object* v_lctx_4302_){
_start:
{
lean_object* v___f_4303_; lean_object* v___x_4304_; 
v___f_4303_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4303_, 0, v_env_4296_);
lean_closure_set(v___f_4303_, 1, v_mctx_4297_);
lean_closure_set(v___f_4303_, 2, v_lctx_4302_);
lean_closure_set(v___f_4303_, 3, v_msgData_4298_);
lean_closure_set(v___f_4303_, 4, v_toPure_4299_);
v___x_4304_ = lean_apply_4(v_toBind_4300_, lean_box(0), lean_box(0), v_inst_4301_, v___f_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4305_, lean_object* v_msgData_4306_, lean_object* v_toPure_4307_, lean_object* v_toBind_4308_, lean_object* v_inst_4309_, lean_object* v_inst_4310_, lean_object* v_mctx_4311_){
_start:
{
lean_object* v___f_4312_; lean_object* v___x_4313_; 
lean_inc(v_toBind_4308_);
v___f_4312_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4312_, 0, v_env_4305_);
lean_closure_set(v___f_4312_, 1, v_mctx_4311_);
lean_closure_set(v___f_4312_, 2, v_msgData_4306_);
lean_closure_set(v___f_4312_, 3, v_toPure_4307_);
lean_closure_set(v___f_4312_, 4, v_toBind_4308_);
lean_closure_set(v___f_4312_, 5, v_inst_4309_);
v___x_4313_ = lean_apply_4(v_toBind_4308_, lean_box(0), lean_box(0), v_inst_4310_, v___f_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4314_, lean_object* v_msgData_4315_, lean_object* v_toPure_4316_, lean_object* v_toBind_4317_, lean_object* v_inst_4318_, lean_object* v_inst_4319_, lean_object* v_env_4320_){
_start:
{
lean_object* v_getMCtx_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
v_getMCtx_4321_ = lean_ctor_get(v_inst_4314_, 0);
lean_inc(v_getMCtx_4321_);
lean_dec_ref(v_inst_4314_);
lean_inc(v_toBind_4317_);
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4322_, 0, v_env_4320_);
lean_closure_set(v___f_4322_, 1, v_msgData_4315_);
lean_closure_set(v___f_4322_, 2, v_toPure_4316_);
lean_closure_set(v___f_4322_, 3, v_toBind_4317_);
lean_closure_set(v___f_4322_, 4, v_inst_4318_);
lean_closure_set(v___f_4322_, 5, v_inst_4319_);
v___x_4323_ = lean_apply_4(v_toBind_4317_, lean_box(0), lean_box(0), v_getMCtx_4321_, v___f_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4324_, lean_object* v_inst_4325_, lean_object* v_inst_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_, lean_object* v_msgData_4329_){
_start:
{
lean_object* v_toApplicative_4330_; lean_object* v_toBind_4331_; lean_object* v_getEnv_4332_; lean_object* v_toPure_4333_; lean_object* v___f_4334_; lean_object* v___x_4335_; 
v_toApplicative_4330_ = lean_ctor_get(v_inst_4324_, 0);
lean_inc_ref(v_toApplicative_4330_);
v_toBind_4331_ = lean_ctor_get(v_inst_4324_, 1);
lean_inc_n(v_toBind_4331_, 2);
lean_dec_ref(v_inst_4324_);
v_getEnv_4332_ = lean_ctor_get(v_inst_4325_, 0);
lean_inc(v_getEnv_4332_);
lean_dec_ref(v_inst_4325_);
v_toPure_4333_ = lean_ctor_get(v_toApplicative_4330_, 1);
lean_inc(v_toPure_4333_);
lean_dec_ref(v_toApplicative_4330_);
v___f_4334_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4334_, 0, v_inst_4326_);
lean_closure_set(v___f_4334_, 1, v_msgData_4329_);
lean_closure_set(v___f_4334_, 2, v_toPure_4333_);
lean_closure_set(v___f_4334_, 3, v_toBind_4331_);
lean_closure_set(v___f_4334_, 4, v_inst_4328_);
lean_closure_set(v___f_4334_, 5, v_inst_4327_);
v___x_4335_ = lean_apply_4(v_toBind_4331_, lean_box(0), lean_box(0), v_getEnv_4332_, v___f_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4336_, lean_object* v_inst_4337_, lean_object* v_inst_4338_, lean_object* v_inst_4339_, lean_object* v_inst_4340_, lean_object* v_inst_4341_, lean_object* v_msgData_4342_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_addMessageContextFull___redArg(v_inst_4337_, v_inst_4338_, v_inst_4339_, v_inst_4340_, v_inst_4341_, v_msgData_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4348_);
lean_dec_ref(v_s_4348_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4350_, lean_object* v___x_4351_, lean_object* v___x_4352_, lean_object* v_a_4353_, lean_object* v_b_4354_){
_start:
{
lean_object* v_it_4356_; lean_object* v_startInclusive_4357_; lean_object* v_endExclusive_4358_; 
if (lean_obj_tag(v_a_4353_) == 0)
{
lean_object* v_currPos_4364_; lean_object* v_searcher_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4388_; 
v_currPos_4364_ = lean_ctor_get(v_a_4353_, 0);
v_searcher_4365_ = lean_ctor_get(v_a_4353_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_a_4353_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4367_ = v_a_4353_;
v_isShared_4368_ = v_isSharedCheck_4388_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_searcher_4365_);
lean_inc(v_currPos_4364_);
lean_dec(v_a_4353_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4388_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
uint8_t v_decide_4369_; 
v_decide_4369_ = lean_nat_dec_eq(v_searcher_4365_, v___x_4352_);
if (v_decide_4369_ == 0)
{
uint32_t v___x_4370_; uint32_t v___x_4371_; uint8_t v___x_4372_; 
v___x_4370_ = 10;
v___x_4371_ = lean_string_utf8_get_fast(v_str_4350_, v_searcher_4365_);
v___x_4372_ = lean_uint32_dec_eq(v___x_4371_, v___x_4370_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4373_ = lean_string_utf8_next_fast(v_str_4350_, v_searcher_4365_);
lean_dec(v_searcher_4365_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 1, v___x_4373_);
v___x_4375_ = v___x_4367_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_currPos_4364_);
lean_ctor_set(v_reuseFailAlloc_4377_, 1, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
v_a_4353_ = v___x_4375_;
goto _start;
}
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v_slice_4381_; lean_object* v_nextIt_4383_; 
v___x_4378_ = lean_string_utf8_next_fast(v_str_4350_, v_searcher_4365_);
v___x_4379_ = lean_nat_sub(v___x_4378_, v_searcher_4365_);
v___x_4380_ = lean_nat_add(v_searcher_4365_, v___x_4379_);
lean_dec(v___x_4379_);
v_slice_4381_ = l_String_Slice_subslice_x21(v___x_4351_, v_currPos_4364_, v_searcher_4365_);
lean_inc(v___x_4380_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 1, v___x_4380_);
lean_ctor_set(v___x_4367_, 0, v___x_4380_);
v_nextIt_4383_ = v___x_4367_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v___x_4380_);
v_nextIt_4383_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v_startInclusive_4384_; lean_object* v_endExclusive_4385_; 
v_startInclusive_4384_ = lean_ctor_get(v_slice_4381_, 0);
lean_inc(v_startInclusive_4384_);
v_endExclusive_4385_ = lean_ctor_get(v_slice_4381_, 1);
lean_inc(v_endExclusive_4385_);
lean_dec_ref(v_slice_4381_);
v_it_4356_ = v_nextIt_4383_;
v_startInclusive_4357_ = v_startInclusive_4384_;
v_endExclusive_4358_ = v_endExclusive_4385_;
goto v___jp_4355_;
}
}
}
else
{
lean_object* v___x_4387_; 
lean_del_object(v___x_4367_);
lean_dec(v_searcher_4365_);
v___x_4387_ = lean_box(1);
lean_inc(v___x_4352_);
v_it_4356_ = v___x_4387_;
v_startInclusive_4357_ = v_currPos_4364_;
v_endExclusive_4358_ = v___x_4352_;
goto v___jp_4355_;
}
}
}
else
{
lean_dec(v___x_4352_);
return v_b_4354_;
}
v___jp_4355_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4359_ = lean_string_utf8_extract_fast(v_str_4350_, v_startInclusive_4357_, v_endExclusive_4358_);
lean_dec(v_endExclusive_4358_);
lean_dec(v_startInclusive_4357_);
v___x_4360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
v___x_4361_ = l_Lean_MessageData_ofFormat(v___x_4360_);
v___x_4362_ = lean_array_push(v_b_4354_, v___x_4361_);
v_a_4353_ = v_it_4356_;
v_b_4354_ = v___x_4362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4389_, lean_object* v___x_4390_, lean_object* v___x_4391_, lean_object* v_a_4392_, lean_object* v_b_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4389_, v___x_4390_, v___x_4391_, v_a_4392_, v_b_4393_);
lean_dec_ref(v___x_4390_);
lean_dec_ref(v_str_4389_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4397_){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v_lines_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = lean_string_utf8_byte_size(v_str_4397_);
lean_inc_ref(v_str_4397_);
v___x_4400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4400_, 0, v_str_4397_);
lean_ctor_set(v___x_4400_, 1, v___x_4398_);
lean_ctor_set(v___x_4400_, 2, v___x_4399_);
v_lines_4401_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4400_);
v___x_4402_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4403_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4397_, v___x_4400_, v___x_4399_, v_lines_4401_, v___x_4402_);
lean_dec_ref_known(v___x_4400_, 3);
lean_dec_ref(v_str_4397_);
v___x_4404_ = lean_array_to_list(v___x_4403_);
v___x_4405_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4406_ = l_Lean_MessageData_joinSep(v___x_4404_, v___x_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4407_, lean_object* v___x_4408_, lean_object* v___x_4409_, lean_object* v_inst_4410_, lean_object* v_R_4411_, lean_object* v_a_4412_, lean_object* v_b_4413_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4407_, v___x_4408_, v___x_4409_, v_a_4412_, v_b_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4415_, lean_object* v___x_4416_, lean_object* v___x_4417_, lean_object* v_inst_4418_, lean_object* v_R_4419_, lean_object* v_a_4420_, lean_object* v_b_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4415_, v___x_4416_, v___x_4417_, v_inst_4418_, v_R_4419_, v_a_4420_, v_b_4421_);
lean_dec_ref(v___x_4416_);
lean_dec_ref(v_str_4415_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4423_){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4425_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4425_, 0, lean_box(0));
lean_closure_set(v___x_4425_, 1, lean_box(0));
lean_closure_set(v___x_4425_, 2, lean_box(0));
lean_closure_set(v___x_4425_, 3, v___x_4424_);
lean_closure_set(v___x_4425_, 4, v_inst_4423_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4426_, lean_object* v_inst_4427_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4435_){
_start:
{
lean_object* v___f_4436_; 
v___f_4436_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_instToMessageDataTSyntax(v_k_4437_);
lean_dec(v_k_4437_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4443_, lean_object* v_as_4444_){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4445_ = lean_box(0);
v___x_4446_ = l_List_mapTR_loop___redArg(v_inst_4443_, v_as_4444_, v___x_4445_);
v___x_4447_ = l_Lean_MessageData_ofList(v___x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4448_){
_start:
{
lean_object* v___f_4449_; 
v___f_4449_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4449_, 0, v_inst_4448_);
return v___f_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4450_, lean_object* v_inst_4451_){
_start:
{
lean_object* v___f_4452_; 
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4452_, 0, v_inst_4451_);
return v___f_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4453_, lean_object* v_as_4454_){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4455_ = lean_array_to_list(v_as_4454_);
v___x_4456_ = lean_box(0);
v___x_4457_ = l_List_mapTR_loop___redArg(v_inst_4453_, v___x_4455_, v___x_4456_);
v___x_4458_ = l_Lean_MessageData_ofList(v___x_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4459_){
_start:
{
lean_object* v___f_4460_; 
v___f_4460_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4460_, 0, v_inst_4459_);
return v___f_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4461_, lean_object* v_inst_4462_){
_start:
{
lean_object* v___f_4463_; 
v___f_4463_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4463_, 0, v_inst_4462_);
return v___f_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4464_, lean_object* v_acc_4465_, lean_object* v_recur_4466_){
_start:
{
lean_object* v_array_4467_; lean_object* v_start_4468_; lean_object* v_stop_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4482_; 
v_array_4467_ = lean_ctor_get(v_it_4464_, 0);
v_start_4468_ = lean_ctor_get(v_it_4464_, 1);
v_stop_4469_ = lean_ctor_get(v_it_4464_, 2);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_it_4464_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4471_ = v_it_4464_;
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_stop_4469_);
lean_inc(v_start_4468_);
lean_inc(v_array_4467_);
lean_dec(v_it_4464_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
uint8_t v___x_4473_; 
v___x_4473_ = lean_nat_dec_lt(v_start_4468_, v_stop_4469_);
if (v___x_4473_ == 0)
{
lean_del_object(v___x_4471_);
lean_dec(v_stop_4469_);
lean_dec(v_start_4468_);
lean_dec_ref(v_array_4467_);
lean_dec_ref(v_recur_4466_);
return v_acc_4465_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4474_ = lean_unsigned_to_nat(1u);
v___x_4475_ = lean_nat_add(v_start_4468_, v___x_4474_);
lean_inc_ref(v_array_4467_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 1, v___x_4475_);
v___x_4477_ = v___x_4471_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_array_4467_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_stop_4469_);
v___x_4477_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_array_fget(v_array_4467_, v_start_4468_);
lean_dec(v_start_4468_);
lean_dec_ref(v_array_4467_);
v___x_4479_ = lean_array_push(v_acc_4465_, v___x_4478_);
v___x_4480_ = lean_apply_3(v_recur_4466_, v___x_4477_, v___x_4479_, lean_box(0));
return v___x_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4485_, lean_object* v_inst_4486_, lean_object* v_as_4487_){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4488_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4489_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4485_, v_as_4487_, v___x_4488_);
v___x_4490_ = lean_array_to_list(v___x_4489_);
v___x_4491_ = lean_box(0);
v___x_4492_ = l_List_mapTR_loop___redArg(v_inst_4486_, v___x_4490_, v___x_4491_);
v___x_4493_ = l_Lean_MessageData_ofList(v___x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4495_){
_start:
{
lean_object* v___f_4496_; lean_object* v___f_4497_; 
v___f_4496_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4497_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4497_, 0, v___f_4496_);
lean_closure_set(v___f_4497_, 1, v_inst_4495_);
return v___f_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4498_, lean_object* v_inst_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4499_);
return v___x_4500_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4505_ = l_Lean_MessageData_ofFormat(v___x_4504_);
return v___x_4505_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4508_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4509_ = l_Lean_MessageData_ofFormat(v___x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4510_, lean_object* v_x_4511_){
_start:
{
if (lean_obj_tag(v_x_4511_) == 0)
{
lean_object* v___x_4512_; 
lean_dec_ref(v_inst_4510_);
v___x_4512_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4512_;
}
else
{
lean_object* v_val_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_val_4513_ = lean_ctor_get(v_x_4511_, 0);
lean_inc(v_val_4513_);
lean_dec_ref_known(v_x_4511_, 1);
v___x_4514_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4515_ = lean_apply_1(v_inst_4510_, v_val_4513_);
v___x_4516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
v___x_4517_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4516_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4519_){
_start:
{
lean_object* v___f_4520_; 
v___f_4520_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4520_, 0, v_inst_4519_);
return v___f_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4521_, lean_object* v_inst_4522_){
_start:
{
lean_object* v___f_4523_; 
v___f_4523_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4523_, 0, v_inst_4522_);
return v___f_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4524_, lean_object* v_inst_4525_, lean_object* v_x_4526_){
_start:
{
lean_object* v_fst_4527_; lean_object* v_snd_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4542_; 
v_fst_4527_ = lean_ctor_get(v_x_4526_, 0);
v_snd_4528_ = lean_ctor_get(v_x_4526_, 1);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_x_4526_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4530_ = v_x_4526_;
v_isShared_4531_ = v_isSharedCheck_4542_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_snd_4528_);
lean_inc(v_fst_4527_);
lean_dec(v_x_4526_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4542_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
v___x_4532_ = lean_apply_1(v_inst_4524_, v_fst_4527_);
v___x_4533_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4531_ == 0)
{
lean_ctor_set_tag(v___x_4530_, 7);
lean_ctor_set(v___x_4530_, 1, v___x_4533_);
lean_ctor_set(v___x_4530_, 0, v___x_4532_);
v___x_4535_ = v___x_4530_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v___x_4533_);
v___x_4535_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4536_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4535_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
v___x_4538_ = lean_apply_1(v_inst_4525_, v_snd_4528_);
v___x_4539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = l_Lean_MessageData_paren(v___x_4539_);
return v___x_4540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4543_, lean_object* v_inst_4544_){
_start:
{
lean_object* v___f_4545_; 
v___f_4545_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4545_, 0, v_inst_4543_);
lean_closure_set(v___f_4545_, 1, v_inst_4544_);
return v___f_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4546_, lean_object* v_00_u03b2_4547_, lean_object* v_inst_4548_, lean_object* v_inst_4549_){
_start:
{
lean_object* v___f_4550_; 
v___f_4550_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4550_, 0, v_inst_4548_);
lean_closure_set(v___f_4550_, 1, v_inst_4549_);
return v___f_4550_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4555_ = l_Lean_MessageData_ofFormat(v___x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4556_){
_start:
{
if (lean_obj_tag(v_x_4556_) == 0)
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4557_;
}
else
{
lean_object* v_val_4558_; lean_object* v___x_4559_; 
v_val_4558_ = lean_ctor_get(v_x_4556_, 0);
lean_inc(v_val_4558_);
lean_dec_ref_known(v_x_4556_, 1);
v___x_4559_ = l_Lean_MessageData_ofExpr(v_val_4558_);
return v___x_4559_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4594_ = l_String_toRawSubstring_x27(v___x_4593_);
return v___x_4594_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4610_ = l_String_toRawSubstring_x27(v___x_4609_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4627_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4624_);
v___x_4628_ = l_Lean_Syntax_isOfKind(v_x_4624_, v___x_4627_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
lean_dec(v_x_4624_);
v___x_4629_ = lean_box(1);
v___x_4630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
lean_ctor_set(v___x_4630_, 1, v_a_4626_);
return v___x_4630_;
}
else
{
lean_object* v_quotContext_4631_; lean_object* v_currMacroScope_4632_; lean_object* v_ref_4633_; lean_object* v___x_4634_; lean_object* v_interpStr_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_quotContext_4631_ = lean_ctor_get(v_a_4625_, 1);
v_currMacroScope_4632_ = lean_ctor_get(v_a_4625_, 2);
v_ref_4633_ = lean_ctor_get(v_a_4625_, 5);
v___x_4634_ = lean_unsigned_to_nat(1u);
v_interpStr_4635_ = l_Lean_Syntax_getArg(v_x_4624_, v___x_4634_);
lean_dec(v_x_4624_);
v___x_4636_ = 0;
v___x_4637_ = l_Lean_SourceInfo_fromRef(v_ref_4633_, v___x_4636_);
v___x_4638_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4639_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4632_, 2);
lean_inc_n(v_quotContext_4631_, 2);
v___x_4640_ = l_Lean_addMacroScope(v_quotContext_4631_, v___x_4639_, v_currMacroScope_4632_);
v___x_4641_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4637_);
v___x_4642_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4637_);
lean_ctor_set(v___x_4642_, 1, v___x_4638_);
lean_ctor_set(v___x_4642_, 2, v___x_4640_);
lean_ctor_set(v___x_4642_, 3, v___x_4641_);
v___x_4643_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4644_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4645_ = l_Lean_addMacroScope(v_quotContext_4631_, v___x_4644_, v_currMacroScope_4632_);
v___x_4646_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4647_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4637_);
lean_ctor_set(v___x_4647_, 1, v___x_4643_);
lean_ctor_set(v___x_4647_, 2, v___x_4645_);
lean_ctor_set(v___x_4647_, 3, v___x_4646_);
lean_inc_ref(v___x_4647_);
v___x_4648_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4635_, v___x_4642_, v___x_4647_, v___x_4647_, v_a_4625_, v_a_4626_);
lean_dec(v_interpStr_4635_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_a_4650_ = lean_ctor_get(v___x_4648_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4648_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4649_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
v_a_4658_ = lean_ctor_get(v___x_4648_, 0);
v_a_4659_ = lean_ctor_get(v___x_4648_, 1);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4648_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_inc(v_a_4658_);
lean_dec(v___x_4648_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4658_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4667_, v_a_4668_, v_a_4669_);
lean_dec_ref(v_a_4668_);
return v_res_4670_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4673_ = l_Lean_stringToMessageData(v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4674_){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4675_ = lean_array_to_list(v_msgs_4674_);
v___x_4676_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4677_ = l_Lean_MessageData_joinSep(v___x_4675_, v___x_4676_);
v___x_4678_ = l_Lean_indentD(v___x_4677_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4679_, lean_object* v_lctx_4680_, lean_object* v_opts_4681_, lean_object* v_msg_4682_){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4683_ = l_Lean_Environment_ofKernelEnv(v_env_4679_);
v___x_4684_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4683_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
lean_ctor_set(v___x_4685_, 2, v_lctx_4680_);
lean_ctor_set(v___x_4685_, 3, v_opts_4681_);
v___x_4686_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
lean_ctor_set(v___x_4686_, 1, v_msg_4682_);
return v___x_4686_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4689_ = l_Lean_stringToMessageData(v___x_4688_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4692_ = l_Lean_stringToMessageData(v___x_4691_);
return v___x_4692_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4695_ = l_Lean_stringToMessageData(v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4696_, lean_object* v_n_4697_, lean_object* v_expectedType_4698_){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4699_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4700_ = l_Lean_MessageData_ofName(v_n_4697_);
v___x_4701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4699_);
lean_ctor_set(v___x_4701_, 1, v___x_4700_);
v___x_4702_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4701_);
lean_ctor_set(v___x_4703_, 1, v___x_4702_);
v___x_4704_ = l_Lean_indentExpr(v_givenType_4696_);
v___x_4705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4703_);
lean_ctor_set(v___x_4705_, 1, v___x_4704_);
v___x_4706_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4705_);
lean_ctor_set(v___x_4707_, 1, v___x_4706_);
v___x_4708_ = l_Lean_indentExpr(v_expectedType_4698_);
v___x_4709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4707_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
return v___x_4709_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4710_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
return v___x_4712_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4713_ = lean_box(1);
v___x_4714_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4715_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
lean_ctor_set(v___x_4716_, 1, v___x_4714_);
lean_ctor_set(v___x_4716_, 2, v___x_4713_);
return v___x_4716_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4719_ = l_Lean_stringToMessageData(v___x_4718_);
return v___x_4719_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4722_ = l_Lean_stringToMessageData(v___x_4721_);
return v___x_4722_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4725_ = l_Lean_stringToMessageData(v___x_4724_);
return v___x_4725_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4730_ = l_Lean_MessageData_ofFormat(v___x_4729_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4733_ = l_Lean_stringToMessageData(v___x_4732_);
return v___x_4733_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4735_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4736_ = l_Lean_stringToMessageData(v___x_4735_);
return v___x_4736_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4739_ = l_Lean_stringToMessageData(v___x_4738_);
return v___x_4739_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4741_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4742_ = l_Lean_stringToMessageData(v___x_4741_);
return v___x_4742_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4745_ = l_Lean_stringToMessageData(v___x_4744_);
return v___x_4745_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4748_ = l_Lean_stringToMessageData(v___x_4747_);
return v___x_4748_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4754_ = l_Lean_stringToMessageData(v___x_4753_);
return v___x_4754_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4757_ = l_Lean_stringToMessageData(v___x_4756_);
return v___x_4757_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4760_ = l_Lean_stringToMessageData(v___x_4759_);
return v___x_4760_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4763_ = l_Lean_stringToMessageData(v___x_4762_);
return v___x_4763_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4766_ = l_Lean_stringToMessageData(v___x_4765_);
return v___x_4766_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4768_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4769_ = l_Lean_stringToMessageData(v___x_4768_);
return v___x_4769_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4772_ = l_Lean_stringToMessageData(v___x_4771_);
return v___x_4772_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4777_ = l_Lean_MessageData_ofFormat(v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4782_ = l_Lean_MessageData_ofFormat(v___x_4781_);
return v___x_4782_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4787_ = l_Lean_MessageData_ofFormat(v___x_4786_);
return v___x_4787_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4792_ = l_Lean_MessageData_ofFormat(v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4793_, lean_object* v_opts_4794_){
_start:
{
switch(lean_obj_tag(v_e_4793_))
{
case 0:
{
lean_object* v_env_4795_; lean_object* v_name_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4809_; 
v_env_4795_ = lean_ctor_get(v_e_4793_, 0);
v_name_4796_ = lean_ctor_get(v_e_4793_, 1);
v_isSharedCheck_4809_ = !lean_is_exclusive(v_e_4793_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4798_ = v_e_4793_;
v_isShared_4799_ = v_isSharedCheck_4809_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_name_4796_);
lean_inc(v_env_4795_);
lean_dec(v_e_4793_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4809_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4800_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4801_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4802_ = l_Lean_MessageData_ofName(v_name_4796_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set_tag(v___x_4798_, 7);
lean_ctor_set(v___x_4798_, 1, v___x_4802_);
lean_ctor_set(v___x_4798_, 0, v___x_4801_);
v___x_4804_ = v___x_4798_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4805_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4804_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4795_, v___x_4800_, v_opts_4794_, v___x_4806_);
return v___x_4807_;
}
}
}
case 1:
{
lean_object* v_env_4810_; lean_object* v_name_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4825_; 
v_env_4810_ = lean_ctor_get(v_e_4793_, 0);
v_name_4811_ = lean_ctor_get(v_e_4793_, 1);
v_isSharedCheck_4825_ = !lean_is_exclusive(v_e_4793_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4813_ = v_e_4793_;
v_isShared_4814_ = v_isSharedCheck_4825_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_name_4811_);
lean_inc(v_env_4810_);
lean_dec(v_e_4793_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4825_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4815_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4816_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4817_ = 1;
v___x_4818_ = l_Lean_MessageData_ofConstName(v_name_4811_, v___x_4817_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set_tag(v___x_4813_, 7);
lean_ctor_set(v___x_4813_, 1, v___x_4818_);
lean_ctor_set(v___x_4813_, 0, v___x_4816_);
v___x_4820_ = v___x_4813_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4810_, v___x_4815_, v_opts_4794_, v___x_4822_);
return v___x_4823_;
}
}
}
case 2:
{
lean_object* v_env_4826_; lean_object* v_decl_4827_; lean_object* v_givenType_4828_; lean_object* v___x_4829_; 
v_env_4826_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4826_);
v_decl_4827_ = lean_ctor_get(v_e_4793_, 1);
lean_inc(v_decl_4827_);
v_givenType_4828_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_givenType_4828_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4829_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4827_))
{
case 1:
{
lean_object* v_val_4830_; lean_object* v_toConstantVal_4831_; lean_object* v_name_4832_; lean_object* v_type_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v_val_4830_ = lean_ctor_get(v_decl_4827_, 0);
lean_inc_ref(v_val_4830_);
lean_dec_ref_known(v_decl_4827_, 1);
v_toConstantVal_4831_ = lean_ctor_get(v_val_4830_, 0);
lean_inc_ref(v_toConstantVal_4831_);
lean_dec_ref(v_val_4830_);
v_name_4832_ = lean_ctor_get(v_toConstantVal_4831_, 0);
lean_inc(v_name_4832_);
v_type_4833_ = lean_ctor_get(v_toConstantVal_4831_, 2);
lean_inc_ref(v_type_4833_);
lean_dec_ref(v_toConstantVal_4831_);
v___x_4834_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4828_, v_name_4832_, v_type_4833_);
v___x_4835_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4826_, v___x_4829_, v_opts_4794_, v___x_4834_);
return v___x_4835_;
}
case 2:
{
lean_object* v_val_4836_; lean_object* v_toConstantVal_4837_; lean_object* v_name_4838_; lean_object* v_type_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_val_4836_ = lean_ctor_get(v_decl_4827_, 0);
lean_inc_ref(v_val_4836_);
lean_dec_ref_known(v_decl_4827_, 1);
v_toConstantVal_4837_ = lean_ctor_get(v_val_4836_, 0);
lean_inc_ref(v_toConstantVal_4837_);
lean_dec_ref(v_val_4836_);
v_name_4838_ = lean_ctor_get(v_toConstantVal_4837_, 0);
lean_inc(v_name_4838_);
v_type_4839_ = lean_ctor_get(v_toConstantVal_4837_, 2);
lean_inc_ref(v_type_4839_);
lean_dec_ref(v_toConstantVal_4837_);
v___x_4840_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4828_, v_name_4838_, v_type_4839_);
v___x_4841_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4826_, v___x_4829_, v_opts_4794_, v___x_4840_);
return v___x_4841_;
}
default: 
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref(v_givenType_4828_);
lean_dec(v_decl_4827_);
v___x_4842_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4843_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4826_, v___x_4829_, v_opts_4794_, v___x_4842_);
return v___x_4843_;
}
}
}
case 3:
{
lean_object* v_env_4844_; lean_object* v_name_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v_env_4844_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4844_);
v_name_4845_ = lean_ctor_get(v_e_4793_, 1);
lean_inc(v_name_4845_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4846_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4847_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4848_ = 1;
v___x_4849_ = l_Lean_MessageData_ofConstName(v_name_4845_, v___x_4848_);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4847_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4844_, v___x_4846_, v_opts_4794_, v___x_4852_);
return v___x_4853_;
}
case 4:
{
lean_object* v_env_4854_; lean_object* v_name_4855_; lean_object* v_expr_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_env_4854_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4854_);
v_name_4855_ = lean_ctor_get(v_e_4793_, 1);
lean_inc(v_name_4855_);
v_expr_4856_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_expr_4856_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4857_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4858_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4859_ = 1;
v___x_4860_ = l_Lean_MessageData_ofConstName(v_name_4855_, v___x_4859_);
v___x_4861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4858_);
lean_ctor_set(v___x_4861_, 1, v___x_4860_);
v___x_4862_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4861_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = l_Lean_indentExpr(v_expr_4856_);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4854_, v___x_4857_, v_opts_4794_, v___x_4865_);
return v___x_4866_;
}
case 5:
{
lean_object* v_env_4867_; lean_object* v_lctx_4868_; lean_object* v_expr_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v_env_4867_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4867_);
v_lctx_4868_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4868_);
v_expr_4869_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_expr_4869_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4870_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4871_ = l_Lean_indentExpr(v_expr_4869_);
v___x_4872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4870_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4867_, v_lctx_4868_, v_opts_4794_, v___x_4872_);
return v___x_4873_;
}
case 6:
{
lean_object* v_env_4874_; lean_object* v_lctx_4875_; lean_object* v_expr_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v_env_4874_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4874_);
v_lctx_4875_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4875_);
v_expr_4876_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_expr_4876_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4877_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4878_ = l_Lean_indentExpr(v_expr_4876_);
v___x_4879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4874_, v_lctx_4875_, v_opts_4794_, v___x_4879_);
return v___x_4880_;
}
case 7:
{
lean_object* v_env_4881_; lean_object* v_lctx_4882_; lean_object* v_name_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v_env_4881_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4881_);
v_lctx_4882_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4882_);
v_name_4883_ = lean_ctor_get(v_e_4793_, 2);
lean_inc(v_name_4883_);
lean_dec_ref_known(v_e_4793_, 5);
v___x_4884_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4885_ = l_Lean_MessageData_ofName(v_name_4883_);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4884_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4886_);
lean_ctor_set(v___x_4888_, 1, v___x_4887_);
v___x_4889_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4881_, v_lctx_4882_, v_opts_4794_, v___x_4888_);
return v___x_4889_;
}
case 8:
{
lean_object* v_env_4890_; lean_object* v_lctx_4891_; lean_object* v_expr_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v_env_4890_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4890_);
v_lctx_4891_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4891_);
v_expr_4892_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_expr_4892_);
lean_dec_ref_known(v_e_4793_, 4);
v___x_4893_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4894_ = l_Lean_indentExpr(v_expr_4892_);
v___x_4895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4893_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4890_, v_lctx_4891_, v_opts_4794_, v___x_4895_);
return v___x_4896_;
}
case 9:
{
lean_object* v_env_4897_; lean_object* v_lctx_4898_; lean_object* v_app_4899_; lean_object* v_funType_4900_; lean_object* v_argType_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_env_4897_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4897_);
v_lctx_4898_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4898_);
v_app_4899_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_app_4899_);
v_funType_4900_ = lean_ctor_get(v_e_4793_, 3);
lean_inc_ref(v_funType_4900_);
v_argType_4901_ = lean_ctor_get(v_e_4793_, 4);
lean_inc_ref(v_argType_4901_);
lean_dec_ref_known(v_e_4793_, 5);
v___x_4902_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4903_ = l_Lean_indentExpr(v_app_4899_);
v___x_4904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4904_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = l_Lean_indentExpr(v_argType_4901_);
v___x_4908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4906_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
v___x_4909_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4908_);
lean_ctor_set(v___x_4910_, 1, v___x_4909_);
v___x_4911_ = l_Lean_indentExpr(v_funType_4900_);
v___x_4912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4910_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
v___x_4913_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4897_, v_lctx_4898_, v_opts_4794_, v___x_4912_);
return v___x_4913_;
}
case 10:
{
lean_object* v_env_4914_; lean_object* v_lctx_4915_; lean_object* v_proj_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v_env_4914_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4914_);
v_lctx_4915_ = lean_ctor_get(v_e_4793_, 1);
lean_inc_ref(v_lctx_4915_);
v_proj_4916_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_proj_4916_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4917_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4918_ = l_Lean_indentExpr(v_proj_4916_);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4917_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4914_, v_lctx_4915_, v_opts_4794_, v___x_4919_);
return v___x_4920_;
}
case 11:
{
lean_object* v_env_4921_; lean_object* v_name_4922_; lean_object* v_type_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_env_4921_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_env_4921_);
v_name_4922_ = lean_ctor_get(v_e_4793_, 1);
lean_inc(v_name_4922_);
v_type_4923_ = lean_ctor_get(v_e_4793_, 2);
lean_inc_ref(v_type_4923_);
lean_dec_ref_known(v_e_4793_, 3);
v___x_4924_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4925_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4926_ = 1;
v___x_4927_ = l_Lean_MessageData_ofConstName(v_name_4922_, v___x_4926_);
v___x_4928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4925_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
v___x_4929_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = l_Lean_indentExpr(v_type_4923_);
v___x_4932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4930_);
lean_ctor_set(v___x_4932_, 1, v___x_4931_);
v___x_4933_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4921_, v___x_4924_, v_opts_4794_, v___x_4932_);
return v___x_4933_;
}
case 12:
{
lean_object* v_msg_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
lean_dec_ref(v_opts_4794_);
v_msg_4934_ = lean_ctor_get(v_e_4793_, 0);
lean_inc_ref(v_msg_4934_);
lean_dec_ref_known(v_e_4793_, 1);
v___x_4935_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4936_ = l_Lean_stringToMessageData(v_msg_4934_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
return v___x_4937_;
}
case 13:
{
lean_object* v___x_4938_; 
lean_dec_ref(v_opts_4794_);
v___x_4938_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4938_;
}
case 14:
{
lean_object* v___x_4939_; 
lean_dec_ref(v_opts_4794_);
v___x_4939_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4939_;
}
case 15:
{
lean_object* v___x_4940_; 
lean_dec_ref(v_opts_4794_);
v___x_4940_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4940_;
}
default: 
{
lean_object* v___x_4941_; 
lean_dec_ref(v_opts_4794_);
v___x_4941_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4942_, lean_object* v_e_4943_, lean_object* v_cls_4944_){
_start:
{
lean_object* v___x_4945_; double v___x_4946_; uint8_t v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4945_ = lean_box(0);
v___x_4946_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4947_ = 1;
v___x_4948_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4949_, 0, v_cls_4944_);
lean_ctor_set(v___x_4949_, 1, v___x_4945_);
lean_ctor_set(v___x_4949_, 2, v___x_4948_);
lean_ctor_set_float(v___x_4949_, sizeof(void*)*3, v___x_4946_);
lean_ctor_set_float(v___x_4949_, sizeof(void*)*3 + 8, v___x_4946_);
lean_ctor_set_uint8(v___x_4949_, sizeof(void*)*3 + 16, v___x_4947_);
v___x_4950_ = lean_apply_1(v_inst_4942_, v_e_4943_);
v___x_4951_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4952_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4949_);
lean_ctor_set(v___x_4952_, 1, v___x_4950_);
lean_ctor_set(v___x_4952_, 2, v___x_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4953_, lean_object* v_inst_4954_, lean_object* v_e_4955_, lean_object* v_cls_4956_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_toTraceElem___redArg(v_inst_4954_, v_e_4955_, v_cls_4956_);
return v___x_4957_;
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
