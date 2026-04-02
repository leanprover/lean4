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
lean_object* lean_register_option(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedMVarId_default;
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedMessageData_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedMessageData_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageData;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "maxTraceChildren"};
static const lean_object* l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 113, 99, 32, 64, 25, 169, 239)}};
static const lean_object* l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Maximum number of trace node children to display"};
static const lean_object* l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_ctor_object l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_MessageData_initFn___closed__0_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(175, 61, 140, 215, 80, 247, 40, 222)}};
static const lean_object* l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMessageLog;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__0;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__1;
static lean_once_cell_t l_Lean_MessageLog_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageLog_empty___closed__2;
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
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_136__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static lean_object* _init_l_Lean_instInhabitedMessageData_default___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Lean_instInhabitedMVarId_default;
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData_default(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_instInhabitedMessageData_default___closed__0, &l_Lean_instInhabitedMessageData_default___closed__0_once, _init_l_Lean_instInhabitedMessageData_default___closed__0);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageData(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_instInhabitedMessageData_default;
return v___x_502_;
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
v___x_535_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
v___x_691_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
v___x_726_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
v___x_756_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
v___x_841_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_921_, lean_object* v_decl_922_, lean_object* v_ref_923_){
_start:
{
lean_object* v_defValue_925_; lean_object* v_descr_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_952_; 
v_defValue_925_ = lean_ctor_get(v_decl_922_, 0);
v_descr_926_ = lean_ctor_get(v_decl_922_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_decl_922_);
if (v_isSharedCheck_952_ == 0)
{
v___x_928_ = v_decl_922_;
v_isShared_929_ = v_isSharedCheck_952_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_descr_926_);
lean_inc(v_defValue_925_);
lean_dec(v_decl_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_952_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc(v_defValue_925_);
v___x_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_930_, 0, v_defValue_925_);
lean_inc_n(v_name_921_, 2);
v___x_931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_931_, 0, v_name_921_);
lean_ctor_set(v___x_931_, 1, v_ref_923_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
lean_ctor_set(v___x_931_, 3, v_descr_926_);
v___x_932_ = lean_register_option(v_name_921_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_942_; 
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_932_, 0);
lean_dec(v_unused_943_);
v___x_934_ = v___x_932_;
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_932_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v_defValue_925_);
lean_ctor_set(v___x_928_, 0, v_name_921_);
v___x_937_ = v___x_928_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_name_921_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_defValue_925_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_937_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_del_object(v___x_928_);
lean_dec(v_defValue_925_);
lean_dec(v_name_921_);
v_a_944_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_932_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_932_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_953_, lean_object* v_decl_954_, lean_object* v_ref_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_953_, v_decl_954_, v_ref_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_971_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_972_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_973_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_970_, v___x_971_, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_nat_to_int(v_a_976_);
return v___x_977_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
v___x_979_ = l_instMonadBaseIO;
v___x_980_ = l_instInhabitedOfMonad___redArg(v___x_979_, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_981_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_2068__overap_984_; lean_object* v___x_985_; 
v___x_983_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2068__overap_984_ = lean_panic_fn_borrowed(v___x_983_, v_msg_981_);
v___x_985_ = lean_apply_1(v___x_2068__overap_984_, lean_box(0));
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_dec(v_x_989_);
return v_x_990_;
}
else
{
lean_object* v_head_992_; lean_object* v_tail_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v_head_992_ = lean_ctor_get(v_x_991_, 0);
v_tail_993_ = lean_ctor_get(v_x_991_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v_x_991_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_tail_993_);
lean_inc(v_head_992_);
lean_dec(v_x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
lean_inc(v_x_989_);
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 5);
lean_ctor_set(v___x_995_, 1, v_x_989_);
lean_ctor_set(v___x_995_, 0, v_x_990_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_x_990_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_x_989_);
v___x_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v_head_992_);
v_x_990_ = v___x_999_;
v_x_991_ = v_tail_993_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_object* v___x_1005_; 
lean_dec(v_x_1004_);
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
else
{
lean_object* v_tail_1006_; 
v_tail_1006_ = lean_ctor_get(v_x_1003_, 1);
if (lean_obj_tag(v_tail_1006_) == 0)
{
lean_object* v_head_1007_; 
lean_dec(v_x_1004_);
v_head_1007_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_head_1007_);
lean_dec_ref(v_x_1003_);
return v_head_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v___x_1009_; 
lean_inc(v_tail_1006_);
v_head_1008_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_head_1008_);
lean_dec_ref(v_x_1003_);
v___x_1009_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1004_, v_head_1008_, v_tail_1006_);
return v___x_1009_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1024_; double v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_float_of_nat(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
switch(lean_obj_tag(v_x_1031_))
{
case 0:
{
lean_object* v_a_1033_; lean_object* v_fmt_1034_; 
lean_dec(v_x_1030_);
lean_dec_ref(v_x_1029_);
v_a_1033_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_a_1033_);
lean_dec_ref(v_x_1031_);
v_fmt_1034_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_fmt_1034_);
lean_dec_ref(v_a_1033_);
return v_fmt_1034_;
}
case 1:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
lean_dec_ref(v_x_1029_);
v_a_1035_ = lean_ctor_get(v_x_1031_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v_x_1031_);
v___x_1036_ = l_Lean_formatRawGoal(v_a_1035_);
return v___x_1036_;
}
else
{
lean_object* v_a_1037_; lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1037_ = lean_ctor_get(v_x_1031_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v_x_1031_);
v_val_1038_ = lean_ctor_get(v_x_1030_, 0);
lean_inc(v_val_1038_);
lean_dec_ref(v_x_1030_);
v___x_1039_ = l_Lean_MessageData_mkPPContext(v_x_1029_, v_val_1038_);
lean_dec(v_val_1038_);
lean_dec_ref(v_x_1029_);
v___x_1040_ = l_Lean_ppGoal(v___x_1039_, v_a_1037_);
return v___x_1040_;
}
}
case 3:
{
lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v___x_1043_; 
lean_dec(v_x_1030_);
v_a_1041_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_a_1041_);
v_a_1042_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_a_1042_);
lean_dec_ref(v_x_1031_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_a_1041_);
v_x_1030_ = v___x_1043_;
v_x_1031_ = v_a_1042_;
goto _start;
}
case 4:
{
lean_object* v_a_1045_; lean_object* v_a_1046_; 
lean_dec_ref(v_x_1029_);
v_a_1045_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_a_1045_);
v_a_1046_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_a_1046_);
lean_dec_ref(v_x_1031_);
v_x_1029_ = v_a_1045_;
v_x_1031_ = v_a_1046_;
goto _start;
}
case 5:
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
v_a_1048_ = lean_ctor_get(v_x_1031_, 0);
v_a_1049_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1051_ = v_x_1031_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_inc(v_a_1048_);
lean_dec(v_x_1031_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = l_Lean_MessageData_formatAux(v_x_1029_, v_x_1030_, v_a_1049_);
v___x_1054_ = lean_nat_to_int(v_a_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 4);
lean_ctor_set(v___x_1051_, 1, v___x_1053_);
lean_ctor_set(v___x_1051_, 0, v___x_1054_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1053_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
case 6:
{
lean_object* v_a_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
v_a_1059_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_a_1059_);
lean_dec_ref(v_x_1031_);
v___x_1060_ = l_Lean_MessageData_formatAux(v_x_1029_, v_x_1030_, v_a_1059_);
v___x_1061_ = 0;
v___x_1062_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1061_);
return v___x_1062_;
}
case 7:
{
lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_a_1063_ = lean_ctor_get(v_x_1031_, 0);
v_a_1064_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_x_1031_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_inc(v_a_1063_);
lean_dec(v_x_1031_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_inc(v_x_1030_);
lean_inc_ref(v_x_1029_);
v___x_1068_ = l_Lean_MessageData_formatAux(v_x_1029_, v_x_1030_, v_a_1063_);
v___x_1069_ = l_Lean_MessageData_formatAux(v_x_1029_, v_x_1030_, v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 5);
lean_ctor_set(v___x_1066_, 1, v___x_1069_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
case 9:
{
lean_object* v_data_1074_; lean_object* v_msg_1075_; lean_object* v_children_1076_; size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_1079_; lean_object* v_msg_1081_; lean_object* v_cls_1093_; double v_startTime_1094_; double v_stopTime_1095_; uint8_t v___x_1096_; 
v_data_1074_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_data_1074_);
v_msg_1075_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_msg_1075_);
v_children_1076_ = lean_ctor_get(v_x_1031_, 2);
lean_inc_ref(v_children_1076_);
lean_dec_ref(v_x_1031_);
v_sz_1077_ = lean_array_size(v_children_1076_);
v___x_1078_ = ((size_t)0ULL);
lean_inc(v_x_1030_);
lean_inc_ref(v_x_1029_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1029_, v_x_1030_, v_sz_1077_, v___x_1078_, v_children_1076_);
v_cls_1093_ = lean_ctor_get(v_data_1074_, 0);
lean_inc(v_cls_1093_);
v_startTime_1094_ = lean_ctor_get_float(v_data_1074_, sizeof(void*)*3);
v_stopTime_1095_ = lean_ctor_get_float(v_data_1074_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1074_);
v___x_1096_ = l_Lean_Name_isAnonymous(v_cls_1093_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; double v___x_1112_; uint8_t v___x_1113_; 
v___x_1097_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1098_ = 1;
v___x_1099_ = l_Lean_Name_toString(v_cls_1093_, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1097_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1112_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1113_ = lean_float_beq(v_startTime_1094_, v___x_1112_);
if (v___x_1113_ == 0)
{
goto v___jp_1104_;
}
else
{
if (v___x_1096_ == 0)
{
v_msg_1081_ = v___x_1103_;
goto v___jp_1080_;
}
else
{
goto v___jp_1104_;
}
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; double v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1105_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_float_sub(v_stopTime_1095_, v_startTime_1094_);
v___x_1108_ = lean_float_to_string(v___x_1107_);
v___x_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1106_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1102_);
v_msg_1081_ = v___x_1111_;
goto v___jp_1080_;
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_cls_1093_);
lean_dec_ref(v_msg_1075_);
lean_dec(v_x_1030_);
lean_dec_ref(v_x_1029_);
v___x_1114_ = lean_array_to_list(v___x_1079_);
v___x_1115_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1116_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1114_, v___x_1115_);
return v___x_1116_;
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1082_ = l_Lean_MessageData_formatAux(v_x_1029_, v_x_1030_, v_msg_1075_);
v___x_1083_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_msg_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1086_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1082_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1084_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_array_to_list(v___x_1079_);
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1091_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1085_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
return v___x_1092_;
}
}
case 10:
{
lean_object* v_f_1117_; lean_object* v___x_1118_; lean_object* v___y_1120_; 
v_f_1117_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_f_1117_);
lean_dec_ref(v_x_1031_);
v___x_1118_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_box(0);
v___y_1120_ = v___x_1136_;
goto v___jp_1119_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_val_1137_ = lean_ctor_get(v_x_1030_, 0);
v___x_1138_ = l_Lean_MessageData_mkPPContext(v_x_1029_, v_val_1137_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___y_1120_ = v___x_1139_;
goto v___jp_1119_;
}
v___jp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_apply_2(v_f_1117_, v___y_1120_, lean_box(0));
v___x_1122_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1121_, v___x_1118_);
if (lean_obj_tag(v___x_1122_) == 1)
{
lean_object* v_val_1123_; 
lean_dec(v___x_1121_);
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1122_);
v_x_1031_ = v_val_1123_;
goto _start;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v___x_1122_);
lean_dec(v_x_1030_);
lean_dec_ref(v_x_1029_);
v___x_1125_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1126_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1127_ = lean_unsigned_to_nat(330u);
v___x_1128_ = lean_unsigned_to_nat(8u);
v___x_1129_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1130_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1121_);
lean_dec(v___x_1121_);
v___x_1131_ = 1;
v___x_1132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_string_append(v___x_1129_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l_mkPanicMessageWithDecl(v___x_1125_, v___x_1126_, v___x_1127_, v___x_1128_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1134_);
return v___x_1135_;
}
}
}
default: 
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_a_1140_);
lean_dec_ref(v_x_1031_);
v_x_1031_ = v_a_1140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1142_, lean_object* v_x_1143_, size_t v_sz_1144_, size_t v_i_1145_, lean_object* v_bs_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1145_, v_sz_1144_);
if (v___x_1148_ == 0)
{
lean_dec(v_x_1143_);
lean_dec_ref(v_x_1142_);
return v_bs_1146_;
}
else
{
lean_object* v_v_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_bs_x27_1152_; size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v_v_1149_ = lean_array_uget_borrowed(v_bs_1146_, v_i_1145_);
lean_inc(v_v_1149_);
lean_inc(v_x_1143_);
lean_inc_ref(v_x_1142_);
v___x_1150_ = l_Lean_MessageData_formatAux(v_x_1142_, v_x_1143_, v_v_1149_);
v___x_1151_ = lean_unsigned_to_nat(0u);
v_bs_x27_1152_ = lean_array_uset(v_bs_1146_, v_i_1145_, v___x_1151_);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1145_, v___x_1153_);
v___x_1155_ = lean_array_uset(v_bs_x27_1152_, v_i_1145_, v___x_1150_);
v_i_1145_ = v___x_1154_;
v_bs_1146_ = v___x_1155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1157_, v_x_1158_, v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1161_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_MessageData_formatAux(v_x_1166_, v_x_1167_, v_x_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1174_, lean_object* v_ctx_x3f_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1178_ = l_Lean_MessageData_formatAux(v___x_1177_, v_ctx_x3f_1175_, v_msgData_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1179_, lean_object* v_ctx_x3f_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_MessageData_format(v_msgData_1179_, v_ctx_x3f_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_MessageData_format(v_msgData_1183_, v___x_1185_);
v___x_1187_ = l_Std_Format_defWidth;
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = l_Std_Format_pretty(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_MessageData_toString(v_msgData_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1193_);
lean_ctor_set(v___x_1195_, 1, v_a_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_s_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_a_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1223_ = l_Lean_MessageData_ofFormat(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1224_){
_start:
{
if (lean_obj_tag(v_o_1224_) == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1225_;
}
else
{
lean_object* v_val_1226_; lean_object* v___x_1227_; 
v_val_1226_ = lean_ctor_get(v_o_1224_, 0);
lean_inc(v_val_1226_);
lean_dec_ref(v_o_1224_);
v___x_1227_ = l_Lean_MessageData_ofExpr(v_val_1226_);
return v___x_1227_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1231_ = l_Lean_MessageData_ofFormat(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1236_ = l_Lean_MessageData_ofFormat(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1237_, lean_object* v_i_1238_, lean_object* v_acc_1239_){
_start:
{
lean_object* v___y_1241_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_es_1237_);
v___x_1246_ = lean_nat_dec_lt(v_i_1238_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v_i_1238_);
v___x_1247_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_acc_1239_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
return v___x_1248_;
}
else
{
lean_object* v_e_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_e_1249_ = lean_array_fget_borrowed(v_es_1237_, v_i_1238_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_nat_dec_eq(v_i_1238_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_acc_1239_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
lean_inc(v_e_1249_);
v___x_1254_ = l_Lean_MessageData_ofExpr(v_e_1249_);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___y_1241_ = v___x_1255_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc(v_e_1249_);
v___x_1256_ = l_Lean_MessageData_ofExpr(v_e_1249_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_acc_1239_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___y_1241_ = v___x_1257_;
goto v___jp_1240_;
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_i_1238_, v___x_1242_);
lean_dec(v_i_1238_);
v_i_1238_ = v___x_1243_;
v_acc_1239_ = v___y_1241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1258_, lean_object* v_i_1259_, lean_object* v_acc_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1258_, v_i_1259_, v_acc_1260_);
lean_dec_ref(v_es_1258_);
return v_res_1261_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1266_ = l_Lean_MessageData_ofFormat(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1270_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1267_, v___x_1268_, v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1271_);
lean_dec_ref(v_es_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1275_, lean_object* v_f_1276_, lean_object* v_r_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1278_ = lean_string_length(v_l_1275_);
v___x_1279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_l_1275_);
v___x_1280_ = l_Lean_MessageData_ofFormat(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_f_1276_);
v___x_1282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_r_1277_);
v___x_1283_ = l_Lean_MessageData_ofFormat(v___x_1282_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1281_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1278_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1289_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1290_ = l_Lean_MessageData_bracket(v___x_1288_, v_f_1287_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1293_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1294_ = l_Lean_MessageData_bracket(v___x_1292_, v_f_1291_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
if (lean_obj_tag(v_x_1295_) == 0)
{
lean_object* v___x_1297_; 
lean_dec_ref(v_x_1296_);
v___x_1297_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1297_;
}
else
{
lean_object* v_tail_1298_; 
v_tail_1298_ = lean_ctor_get(v_x_1295_, 1);
if (lean_obj_tag(v_tail_1298_) == 0)
{
lean_object* v_head_1299_; 
lean_dec_ref(v_x_1296_);
v_head_1299_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_head_1299_);
lean_dec_ref(v_x_1295_);
return v_head_1299_;
}
else
{
lean_object* v_head_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1309_; 
lean_inc(v_tail_1298_);
v_head_1300_ = lean_ctor_get(v_x_1295_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_x_1295_, 1);
lean_dec(v_unused_1310_);
v___x_1302_ = v_x_1295_;
v_isShared_1303_ = v_isSharedCheck_1309_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_head_1300_);
lean_dec(v_x_1295_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1309_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
lean_inc_ref(v_x_1296_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 7);
lean_ctor_set(v___x_1302_, 1, v_x_1296_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_head_1300_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_x_1296_);
v___x_1305_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = l_Lean_MessageData_joinSep(v_tail_1298_, v_x_1296_);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
return v___x_1307_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1315_ = l_Lean_MessageData_ofFormat(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1320_ = l_Lean_MessageData_ofFormat(v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_box(1);
v___x_1322_ = l_Lean_MessageData_ofFormat(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1324_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1326_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1329_ = l_Lean_MessageData_joinSep(v_x_1326_, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_sbracket(v___x_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_array_to_list(v_msgs_1331_);
v___x_1333_ = l_Lean_MessageData_ofList(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1348_ = l_Lean_MessageData_ofFormat(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1349_){
_start:
{
if (lean_obj_tag(v_xs_1349_) == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1350_;
}
else
{
lean_object* v_tail_1351_; 
v_tail_1351_ = lean_ctor_get(v_xs_1349_, 1);
lean_inc(v_tail_1351_);
if (lean_obj_tag(v_tail_1351_) == 0)
{
lean_object* v_head_1352_; 
v_head_1352_ = lean_ctor_get(v_xs_1349_, 0);
lean_inc(v_head_1352_);
lean_dec_ref(v_xs_1349_);
return v_head_1352_;
}
else
{
lean_object* v_tail_1353_; 
v_tail_1353_ = lean_ctor_get(v_tail_1351_, 1);
if (lean_obj_tag(v_tail_1353_) == 0)
{
lean_object* v_head_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1371_; 
v_head_1354_ = lean_ctor_get(v_xs_1349_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_xs_1349_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_xs_1349_, 1);
lean_dec(v_unused_1372_);
v___x_1356_ = v_xs_1349_;
v_isShared_1357_ = v_isSharedCheck_1371_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_head_1354_);
lean_dec(v_xs_1349_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1371_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_head_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
v_head_1358_ = lean_ctor_get(v_tail_1351_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_tail_1351_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v_tail_1351_, 1);
lean_dec(v_unused_1370_);
v___x_1360_ = v_tail_1351_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_head_1358_);
lean_dec(v_tail_1351_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 7);
lean_ctor_set(v___x_1360_, 1, v___x_1362_);
lean_ctor_set(v___x_1360_, 0, v_head_1354_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_head_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 7);
lean_ctor_set(v___x_1356_, 1, v_head_1358_);
lean_ctor_set(v___x_1356_, 0, v___x_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_head_1358_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v_tail_1351_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1397_ = lean_ctor_get(v_tail_1351_, 1);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_tail_1351_, 0);
lean_dec(v_unused_1398_);
v___x_1374_ = v_tail_1351_;
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_tail_1351_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1376_ = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(v_xs_1349_);
v___x_1377_ = lean_array_mk(v_xs_1349_);
v___x_1378_ = lean_array_pop(v___x_1377_);
v___x_1379_ = lean_array_to_list(v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1381_ = l_Lean_MessageData_joinSep(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 7);
lean_ctor_set(v___x_1374_, 1, v___x_1382_);
lean_ctor_set(v___x_1374_, 0, v___x_1381_);
v___x_1384_ = v___x_1374_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v___x_1385_ = l_List_getLast_x21___redArg(v___x_1376_, v_xs_1349_);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_xs_1349_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1393_ = lean_ctor_get(v_xs_1349_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_xs_1349_, 0);
lean_dec(v_unused_1394_);
v___x_1387_ = v_xs_1349_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v_xs_1349_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 7);
lean_ctor_set(v___x_1387_, 1, v___x_1385_);
lean_ctor_set(v___x_1387_, 0, v___x_1384_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
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
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1403_ = l_Lean_MessageData_ofFormat(v___x_1402_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1408_ = l_Lean_MessageData_ofFormat(v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1409_){
_start:
{
if (lean_obj_tag(v_xs_1409_) == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1410_;
}
else
{
lean_object* v_tail_1411_; 
v_tail_1411_ = lean_ctor_get(v_xs_1409_, 1);
lean_inc(v_tail_1411_);
if (lean_obj_tag(v_tail_1411_) == 0)
{
lean_object* v_head_1412_; 
v_head_1412_ = lean_ctor_get(v_xs_1409_, 0);
lean_inc(v_head_1412_);
lean_dec_ref(v_xs_1409_);
return v_head_1412_;
}
else
{
lean_object* v_tail_1413_; 
v_tail_1413_ = lean_ctor_get(v_tail_1411_, 1);
if (lean_obj_tag(v_tail_1413_) == 0)
{
lean_object* v_head_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1431_; 
v_head_1414_ = lean_ctor_get(v_xs_1409_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_xs_1409_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_xs_1409_, 1);
lean_dec(v_unused_1432_);
v___x_1416_ = v_xs_1409_;
v_isShared_1417_ = v_isSharedCheck_1431_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_head_1414_);
lean_dec(v_xs_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1431_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_head_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1429_; 
v_head_1418_ = lean_ctor_get(v_tail_1411_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_tail_1411_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_tail_1411_, 1);
lean_dec(v_unused_1430_);
v___x_1420_ = v_tail_1411_;
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_head_1418_);
lean_dec(v_tail_1411_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 7);
lean_ctor_set(v___x_1420_, 1, v___x_1422_);
lean_ctor_set(v___x_1420_, 0, v_head_1414_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_head_1414_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v_head_1418_);
lean_ctor_set(v___x_1416_, 0, v___x_1424_);
v___x_1426_ = v___x_1416_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_head_1418_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1456_; 
v_isSharedCheck_1456_ = !lean_is_exclusive(v_tail_1411_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1457_ = lean_ctor_get(v_tail_1411_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_tail_1411_, 0);
lean_dec(v_unused_1458_);
v___x_1434_ = v_tail_1411_;
v_isShared_1435_ = v_isSharedCheck_1456_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v_tail_1411_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1456_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1436_ = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(v_xs_1409_);
v___x_1437_ = lean_array_mk(v_xs_1409_);
v___x_1438_ = lean_array_pop(v___x_1437_);
v___x_1439_ = lean_array_to_list(v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1441_ = l_Lean_MessageData_joinSep(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 7);
lean_ctor_set(v___x_1434_, 1, v___x_1442_);
lean_ctor_set(v___x_1434_, 0, v___x_1441_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v___x_1445_ = l_List_getLast_x21___redArg(v___x_1436_, v_xs_1409_);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_xs_1409_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1453_ = lean_ctor_get(v_xs_1409_, 1);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_xs_1409_, 0);
lean_dec(v_unused_1454_);
v___x_1447_ = v_xs_1409_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_xs_1409_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 7);
lean_ctor_set(v___x_1447_, 1, v___x_1445_);
lean_ctor_set(v___x_1447_, 0, v___x_1444_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
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
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_1465_ = l_Lean_MessageData_ofFormat(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_1467_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_note_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_1476_ = l_Lean_MessageData_ofFormat(v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_1478_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_hint_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_1487_ = lean_box(0);
v___x_1488_ = l_List_mapTR_loop___redArg(v___x_1486_, v_es_1485_, v___x_1487_);
v___x_1489_ = l_Lean_MessageData_ofList(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1493_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_1494_ = l_Lean_instInhabitedPosition_default;
v___x_1495_ = lean_box(0);
v___x_1496_ = 0;
v___x_1497_ = 0;
v___x_1498_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1498_, 0, v___x_1493_);
lean_ctor_set(v___x_1498_, 1, v___x_1494_);
lean_ctor_set(v___x_1498_, 2, v___x_1495_);
lean_ctor_set(v___x_1498_, 3, v___x_1493_);
lean_ctor_set(v___x_1498_, 4, v_inst_1492_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5, v___x_1496_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5 + 1, v___x_1497_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5 + 2, v___x_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_a_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_1519_, lean_object* v_x_1520_){
_start:
{
lean_object* v_fileName_1521_; lean_object* v_pos_1522_; lean_object* v_endPos_1523_; uint8_t v_keepFullRange_1524_; uint8_t v_severity_1525_; uint8_t v_isSilent_1526_; lean_object* v_caption_1527_; lean_object* v_data_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_fileName_1521_ = lean_ctor_get(v_x_1520_, 0);
lean_inc_ref(v_fileName_1521_);
v_pos_1522_ = lean_ctor_get(v_x_1520_, 1);
lean_inc_ref(v_pos_1522_);
v_endPos_1523_ = lean_ctor_get(v_x_1520_, 2);
lean_inc(v_endPos_1523_);
v_keepFullRange_1524_ = lean_ctor_get_uint8(v_x_1520_, sizeof(void*)*5);
v_severity_1525_ = lean_ctor_get_uint8(v_x_1520_, sizeof(void*)*5 + 1);
v_isSilent_1526_ = lean_ctor_get_uint8(v_x_1520_, sizeof(void*)*5 + 2);
v_caption_1527_ = lean_ctor_get(v_x_1520_, 3);
lean_inc_ref(v_caption_1527_);
v_data_1528_ = lean_ctor_get(v_x_1520_, 4);
lean_inc(v_data_1528_);
lean_dec_ref(v_x_1520_);
v___x_1529_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_1530_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_fileName_1521_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1536_ = l_Lean_instToJsonPosition_toJson(v_pos_1522_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1533_);
v___x_1539_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1540_ = l_Option_toJson___redArg(v___x_1529_, v_endPos_1523_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1533_);
v___x_1543_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1544_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1544_, 0, v_keepFullRange_1524_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1533_);
v___x_1547_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1548_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1525_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1533_);
v___x_1551_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1552_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1552_, 0, v_isSilent_1526_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1533_);
v___x_1555_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_caption_1527_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1533_);
v___x_1559_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1560_ = lean_apply_1(v_inst_1519_, v_data_1528_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1533_);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___x_1533_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1558_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1554_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1550_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1546_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1542_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1538_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1534_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_1572_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1573_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_1571_, v___x_1570_, v___x_1572_);
v___x_1574_ = l_Lean_Json_mkObj(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_1575_, lean_object* v_inst_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_1576_, v_x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1580_, 0, lean_box(0));
lean_closure_set(v___x_1580_, 1, v_inst_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_1581_, lean_object* v_inst_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1583_, 0, lean_box(0));
lean_closure_set(v___x_1583_, 1, v_inst_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = 1;
v___x_1590_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_1591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_1594_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_1595_ = lean_string_append(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = 1;
v___x_1599_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_1600_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1599_, v___x_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_1602_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1603_ = lean_string_append(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1606_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_1607_ = lean_string_append(v___x_1606_, v___x_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = 1;
v___x_1614_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_1615_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_1617_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1618_ = lean_string_append(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1620_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_1621_ = lean_string_append(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 1;
v___x_1625_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_1626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1625_, v___x_1624_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_1628_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1629_ = lean_string_append(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1631_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_1632_ = lean_string_append(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = 1;
v___x_1637_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_1638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1637_, v___x_1636_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_1640_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1641_ = lean_string_append(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1643_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_1644_ = lean_string_append(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = 1;
v___x_1648_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_1649_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1648_, v___x_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_1651_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1652_ = lean_string_append(v___x_1651_, v___x_1650_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1654_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_1655_ = lean_string_append(v___x_1654_, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = 1;
v___x_1659_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_1660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1659_, v___x_1658_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_1662_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1663_ = lean_string_append(v___x_1662_, v___x_1661_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1665_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_1666_ = lean_string_append(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = 1;
v___x_1670_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_1671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_1673_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1674_ = lean_string_append(v___x_1673_, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1676_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_1677_ = lean_string_append(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = 1;
v___x_1681_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_1682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_1684_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1685_ = lean_string_append(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1687_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_1688_ = lean_string_append(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_1689_, lean_object* v_json_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_1692_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_1690_);
v___x_1693_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1691_, v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_1699_ = lean_string_append(v___x_1698_, v_a_1694_);
lean_dec(v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1704_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1693_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1693_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 0);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1712_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1693_);
v___x_1713_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_1714_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_1715_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_1690_);
v___x_1716_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1713_, v___x_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_1722_ = lean_string_append(v___x_1721_, v_a_1717_);
lean_dec(v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1722_);
v___x_1724_ = v___x_1719_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1727_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1716_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1716_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 0);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_a_1735_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1716_);
v___x_1736_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_1690_);
v___x_1737_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1714_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1742_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_1743_ = lean_string_append(v___x_1742_, v_a_1738_);
lean_dec(v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1748_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1737_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1737_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set_tag(v___x_1750_, 0);
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_a_1756_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1737_);
v___x_1757_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_1758_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_1690_);
v___x_1759_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1757_, v___x_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1764_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_1765_ = lean_string_append(v___x_1764_, v_a_1760_);
lean_dec(v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1765_);
v___x_1767_ = v___x_1762_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1770_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1759_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1759_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 0);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_a_1778_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1759_);
v___x_1779_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_1780_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_1690_);
v___x_1781_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1779_, v___x_1780_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1786_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_1787_ = lean_string_append(v___x_1786_, v_a_1782_);
lean_dec(v_a_1782_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1792_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1781_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1781_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 0);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1800_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1781_);
v___x_1801_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_1690_);
v___x_1802_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1757_, v___x_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1812_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1812_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1807_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_1808_ = lean_string_append(v___x_1807_, v_a_1803_);
lean_dec(v_a_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1813_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1802_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1802_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 0);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1802_);
v___x_1822_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_1690_);
v___x_1823_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v___x_1691_, v___x_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_a_1821_);
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_1829_ = lean_string_append(v___x_1828_, v_a_1824_);
lean_dec(v_a_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
else
{
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_a_1821_);
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
lean_dec(v_json_1690_);
lean_dec_ref(v_inst_1689_);
v_a_1834_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1823_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1823_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set_tag(v___x_1836_, 0);
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1823_);
v___x_1843_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1844_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1690_, v_inst_1689_, v___x_1843_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1842_);
lean_dec(v_a_1821_);
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_1850_ = lean_string_append(v___x_1849_, v_a_1845_);
lean_dec(v_a_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_a_1842_);
lean_dec(v_a_1821_);
lean_dec(v_a_1800_);
lean_dec(v_a_1778_);
lean_dec(v_a_1756_);
lean_dec(v_a_1735_);
lean_dec(v_a_1712_);
v_a_1855_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1844_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1844_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 0);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1874_; 
v_a_1863_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1865_ = v___x_1844_;
v_isShared_1866_ = v_isSharedCheck_1874_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1844_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1874_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; uint8_t v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1872_; 
v___x_1867_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1867_, 0, v_a_1712_);
lean_ctor_set(v___x_1867_, 1, v_a_1735_);
lean_ctor_set(v___x_1867_, 2, v_a_1756_);
lean_ctor_set(v___x_1867_, 3, v_a_1842_);
lean_ctor_set(v___x_1867_, 4, v_a_1863_);
v___x_1868_ = lean_unbox(v_a_1778_);
lean_dec(v_a_1778_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*5, v___x_1868_);
v___x_1869_ = lean_unbox(v_a_1800_);
lean_dec(v_a_1800_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*5 + 1, v___x_1869_);
v___x_1870_ = lean_unbox(v_a_1821_);
lean_dec(v_a_1821_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*5 + 2, v___x_1870_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1872_ = v___x_1865_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_1875_, lean_object* v_inst_1876_, lean_object* v_json_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_1876_, v_json_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1880_, 0, lean_box(0));
lean_closure_set(v___x_1880_, 1, v_inst_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_1881_, lean_object* v_inst_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1883_, 0, lean_box(0));
lean_closure_set(v___x_1883_, 1, v_inst_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_1884_){
_start:
{
if (lean_obj_tag(v_x_1884_) == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1887_; 
v_val_1886_ = lean_ctor_get(v_x_1884_, 0);
lean_inc(v_val_1886_);
lean_dec_ref(v_x_1884_);
v___x_1887_ = l_Lean_instToJsonPosition_toJson(v_val_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
if (lean_obj_tag(v_a_1888_) == 0)
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_array_to_list(v_a_1889_);
return v___x_1890_;
}
else
{
lean_object* v_head_1891_; lean_object* v_tail_1892_; lean_object* v___x_1893_; 
v_head_1891_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_head_1891_);
v_tail_1892_ = lean_ctor_get(v_a_1888_, 1);
lean_inc(v_tail_1892_);
lean_dec_ref(v_a_1888_);
v___x_1893_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1889_, v_head_1891_);
v_a_1888_ = v_tail_1892_;
v_a_1889_ = v___x_1893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_1896_){
_start:
{
lean_object* v_toBaseMessage_1897_; lean_object* v_kind_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1963_; 
v_toBaseMessage_1897_ = lean_ctor_get(v_x_1896_, 0);
v_kind_1898_ = lean_ctor_get(v_x_1896_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_x_1896_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1900_ = v_x_1896_;
v_isShared_1901_ = v_isSharedCheck_1963_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_kind_1898_);
lean_inc(v_toBaseMessage_1897_);
lean_dec(v_x_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1963_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_fileName_1902_; lean_object* v_pos_1903_; lean_object* v_endPos_1904_; uint8_t v_keepFullRange_1905_; uint8_t v_severity_1906_; uint8_t v_isSilent_1907_; lean_object* v_caption_1908_; lean_object* v_data_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v_fileName_1902_ = lean_ctor_get(v_toBaseMessage_1897_, 0);
lean_inc_ref(v_fileName_1902_);
v_pos_1903_ = lean_ctor_get(v_toBaseMessage_1897_, 1);
lean_inc_ref(v_pos_1903_);
v_endPos_1904_ = lean_ctor_get(v_toBaseMessage_1897_, 2);
lean_inc(v_endPos_1904_);
v_keepFullRange_1905_ = lean_ctor_get_uint8(v_toBaseMessage_1897_, sizeof(void*)*5);
v_severity_1906_ = lean_ctor_get_uint8(v_toBaseMessage_1897_, sizeof(void*)*5 + 1);
v_isSilent_1907_ = lean_ctor_get_uint8(v_toBaseMessage_1897_, sizeof(void*)*5 + 2);
v_caption_1908_ = lean_ctor_get(v_toBaseMessage_1897_, 3);
lean_inc_ref(v_caption_1908_);
v_data_1909_ = lean_ctor_get(v_toBaseMessage_1897_, 4);
lean_inc(v_data_1909_);
lean_dec_ref(v_toBaseMessage_1897_);
v___x_1910_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_fileName_1902_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_1911_);
lean_ctor_set(v___x_1900_, 0, v___x_1910_);
v___x_1913_ = v___x_1900_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1917_ = l_Lean_instToJsonPosition_toJson(v_pos_1903_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1914_);
v___x_1920_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1921_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_1904_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1914_);
v___x_1924_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1925_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1925_, 0, v_keepFullRange_1905_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1914_);
v___x_1928_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1929_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1906_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1914_);
v___x_1932_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1933_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1933_, 0, v_isSilent_1907_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1914_);
v___x_1936_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_caption_1908_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1914_);
v___x_1940_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_data_1909_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1914_);
v___x_1944_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_1945_ = 1;
v___x_1946_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1898_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1944_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1914_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1914_);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1943_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1939_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1935_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1931_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1927_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1923_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1919_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1915_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1960_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_1958_, v___x_1959_);
v___x_1961_ = l_Lean_Json_mkObj(v___x_1960_);
return v___x_1961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_1966_, lean_object* v_k_1967_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = l_Lean_Json_getObjValD(v_j_1966_, v_k_1967_);
v___x_1969_ = l_Lean_Json_getStr_x3f(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_1970_, lean_object* v_k_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_1970_, v_k_1971_);
lean_dec_ref(v_k_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_1973_, lean_object* v_k_1974_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = l_Lean_Json_getObjValD(v_j_1973_, v_k_1974_);
v___x_1976_ = l_Lean_instFromJsonPosition_fromJson(v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_1977_, lean_object* v_k_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_1977_, v_k_1978_);
lean_dec_ref(v_k_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_1980_, lean_object* v_k_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l_Lean_Json_getObjValD(v_j_1980_, v_k_1981_);
v___x_1983_ = l_Lean_Json_getBool_x3f(v___x_1982_);
lean_dec(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_1984_, lean_object* v_k_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_1984_, v_k_1985_);
lean_dec_ref(v_k_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_1987_, lean_object* v_k_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = l_Lean_Json_getObjValD(v_j_1987_, v_k_1988_);
v___x_1990_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_1991_, lean_object* v_k_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_1991_, v_k_1992_);
lean_dec_ref(v_k_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_1994_, lean_object* v_k_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = l_Lean_Json_getObjValD(v_j_1994_, v_k_1995_);
v___x_1997_ = l_Lean_Name_fromJson_x3f(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_1998_, lean_object* v_k_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_1998_, v_k_1999_);
lean_dec_ref(v_k_1999_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2003_){
_start:
{
if (lean_obj_tag(v_x_2003_) == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_instFromJsonPosition_fromJson(v_x_2003_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
v_a_2014_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2016_ = v___x_2005_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2005_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_a_2014_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2023_, lean_object* v_k_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Json_getObjValD(v_j_2023_, v_k_2024_);
v___x_2026_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2027_, lean_object* v_k_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2027_, v_k_2028_);
lean_dec_ref(v_k_2028_);
return v_res_2029_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = 1;
v___x_2035_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2036_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2035_, v___x_2034_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2038_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2039_ = lean_string_append(v___x_2038_, v___x_2037_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2041_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2042_ = lean_string_append(v___x_2041_, v___x_2040_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2044_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2045_ = lean_string_append(v___x_2044_, v___x_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2047_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2048_ = lean_string_append(v___x_2047_, v___x_2046_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2050_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2051_ = lean_string_append(v___x_2050_, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2053_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2054_ = lean_string_append(v___x_2053_, v___x_2052_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2056_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2057_ = lean_string_append(v___x_2056_, v___x_2055_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2059_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2060_ = lean_string_append(v___x_2059_, v___x_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2062_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2063_ = lean_string_append(v___x_2062_, v___x_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2065_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2066_ = lean_string_append(v___x_2065_, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2068_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2069_ = lean_string_append(v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2071_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2072_ = lean_string_append(v___x_2071_, v___x_2070_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2074_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2075_ = lean_string_append(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2077_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2078_ = lean_string_append(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2080_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2081_ = lean_string_append(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2083_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2084_ = lean_string_append(v___x_2083_, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2086_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2087_ = lean_string_append(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = 1;
v___x_2091_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2091_, v___x_2090_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2094_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2095_ = lean_string_append(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2097_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2098_ = lean_string_append(v___x_2097_, v___x_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2099_);
v___x_2101_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2099_, v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_json_2099_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2106_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2107_ = lean_string_append(v___x_2106_, v_a_2102_);
lean_dec(v_a_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2109_ = v___x_2104_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_json_2099_);
v_a_2112_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2101_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2101_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 0);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2101_);
v___x_2121_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2099_);
v___x_2122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2099_, v___x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2132_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2132_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2127_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2128_ = lean_string_append(v___x_2127_, v_a_2123_);
lean_dec(v_a_2123_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2128_);
v___x_2130_ = v___x_2125_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2133_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2122_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2122_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 0);
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2141_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2122_);
v___x_2142_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2099_);
v___x_2143_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2099_, v___x_2142_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2148_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2149_ = lean_string_append(v___x_2148_, v_a_2144_);
lean_dec(v_a_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
else
{
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2154_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2143_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2143_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2143_);
v___x_2163_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2099_);
v___x_2164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2099_, v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2169_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2170_ = lean_string_append(v___x_2169_, v_a_2165_);
lean_dec(v_a_2165_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2175_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2164_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2164_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 0);
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_a_2183_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2164_);
v___x_2184_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2099_);
v___x_2185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2099_, v___x_2184_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2191_ = lean_string_append(v___x_2190_, v_a_2186_);
lean_dec(v_a_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2191_);
v___x_2193_ = v___x_2188_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2196_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2185_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2185_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 0);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_a_2204_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2185_);
v___x_2205_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2099_);
v___x_2206_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2099_, v___x_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2212_ = lean_string_append(v___x_2211_, v_a_2207_);
lean_dec(v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2217_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2206_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2206_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 0);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v_a_2225_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2206_);
v___x_2226_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2099_);
v___x_2227_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2099_, v___x_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2233_ = lean_string_append(v___x_2232_, v_a_2228_);
lean_dec(v_a_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2238_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2227_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2227_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set_tag(v___x_2240_, 0);
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2227_);
v___x_2247_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2099_);
v___x_2248_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2099_, v___x_2247_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2246_);
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2254_ = lean_string_append(v___x_2253_, v_a_2249_);
lean_dec(v_a_2249_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2254_);
v___x_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2246_);
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
lean_dec(v_json_2099_);
v_a_2259_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2248_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2248_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 0);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2267_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2248_);
v___x_2268_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2269_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2099_, v___x_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2267_);
lean_dec(v_a_2246_);
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
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
v___x_2274_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
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
lean_dec(v_a_2267_);
lean_dec(v_a_2246_);
lean_dec(v_a_2225_);
lean_dec(v_a_2204_);
lean_dec(v_a_2183_);
lean_dec(v_a_2162_);
lean_dec(v_a_2141_);
lean_dec(v_a_2120_);
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
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2300_; 
v_a_2288_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2290_ = v___x_2269_;
v_isShared_2291_ = v_isSharedCheck_2300_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2269_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2300_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2292_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2292_, 0, v_a_2120_);
lean_ctor_set(v___x_2292_, 1, v_a_2141_);
lean_ctor_set(v___x_2292_, 2, v_a_2162_);
lean_ctor_set(v___x_2292_, 3, v_a_2246_);
lean_ctor_set(v___x_2292_, 4, v_a_2267_);
v___x_2293_ = lean_unbox(v_a_2183_);
lean_dec(v_a_2183_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5, v___x_2293_);
v___x_2294_ = lean_unbox(v_a_2204_);
lean_dec(v_a_2204_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5 + 1, v___x_2294_);
v___x_2295_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*5 + 2, v___x_2295_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2292_);
lean_ctor_set(v___x_2296_, 1, v_a_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2296_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2307_ = l_Lean_Name_str___override(v_errorName_2305_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2308_, lean_object* v_name_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = l_Lean_kindOfErrorName(v_name_2309_);
v___x_2311_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_msg_2308_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2313_){
_start:
{
switch(lean_obj_tag(v_a_2313_))
{
case 0:
{
return v_a_2313_;
}
case 1:
{
lean_object* v_pre_2314_; lean_object* v_str_2315_; lean_object* v_p_x27_2316_; uint8_t v___y_2318_; uint8_t v___x_2321_; 
v_pre_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_pre_2314_);
v_str_2315_ = lean_ctor_get(v_a_2313_, 1);
lean_inc_ref(v_str_2315_);
lean_dec_ref(v_a_2313_);
v_p_x27_2316_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2314_);
v___x_2321_ = l_Lean_Name_isAnonymous(v_p_x27_2316_);
if (v___x_2321_ == 0)
{
v___y_2318_ = v___x_2321_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2323_ = lean_string_dec_eq(v_str_2315_, v___x_2322_);
v___y_2318_ = v___x_2323_;
goto v___jp_2317_;
}
v___jp_2317_:
{
if (v___y_2318_ == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Name_str___override(v_p_x27_2316_, v_str_2315_);
return v___x_2319_;
}
else
{
lean_object* v___x_2320_; 
lean_dec(v_p_x27_2316_);
lean_dec_ref(v_str_2315_);
v___x_2320_ = lean_box(0);
return v___x_2320_;
}
}
}
default: 
{
lean_object* v_pre_2324_; lean_object* v_i_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_pre_2324_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_pre_2324_);
v_i_2325_ = lean_ctor_get(v_a_2313_, 1);
lean_inc(v_i_2325_);
lean_dec_ref(v_a_2313_);
v___x_2326_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2324_);
v___x_2327_ = l_Lean_Name_num___override(v___x_2326_, v_i_2325_);
return v___x_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2328_){
_start:
{
switch(lean_obj_tag(v_x_2328_))
{
case 3:
{
lean_object* v_a_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2338_; 
v_a_2329_ = lean_ctor_get(v_x_2328_, 0);
v_a_2330_ = lean_ctor_get(v_x_2328_, 1);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2332_ = v_x_2328_;
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_inc(v_a_2329_);
lean_dec(v_x_2328_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = l_Lean_MessageData_stripNestedTags(v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v___x_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2329_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
case 4:
{
lean_object* v_a_2339_; lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2348_; 
v_a_2339_ = lean_ctor_get(v_x_2328_, 0);
v_a_2340_ = lean_ctor_get(v_x_2328_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2342_ = v_x_2328_;
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_inc(v_a_2339_);
lean_dec(v_x_2328_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = l_Lean_MessageData_stripNestedTags(v_a_2340_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 1, v___x_2344_);
v___x_2346_ = v___x_2342_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2339_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
case 8:
{
lean_object* v_a_2349_; lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2358_; 
v_a_2349_ = lean_ctor_get(v_x_2328_, 0);
v_a_2350_ = lean_ctor_get(v_x_2328_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2352_ = v_x_2328_;
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_inc(v_a_2349_);
lean_dec(v_x_2328_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2349_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_a_2350_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
default: 
{
return v_x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2359_){
_start:
{
if (lean_obj_tag(v_x_2359_) == 1)
{
lean_object* v_pre_2360_; lean_object* v_str_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_pre_2360_ = lean_ctor_get(v_x_2359_, 0);
v_str_2361_ = lean_ctor_get(v_x_2359_, 1);
v___x_2362_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2363_ = lean_string_dec_eq(v_str_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_box(0);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; 
lean_inc(v_pre_2360_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_pre_2360_);
return v___x_2365_;
}
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_box(0);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_errorNameOfKind_x3f(v_x_2367_);
lean_dec(v_x_2367_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_MessageData_kind(v_msg_2369_);
v___x_2371_ = l_Lean_errorNameOfKind_x3f(v___x_2370_);
lean_dec(v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_MessageData_errorName_x3f(v_msg_2372_);
lean_dec_ref(v_msg_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2374_){
_start:
{
lean_object* v_data_2375_; lean_object* v___x_2376_; 
v_data_2375_ = lean_ctor_get(v_msg_2374_, 4);
v___x_2376_ = l_Lean_MessageData_errorName_x3f(v_data_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Message_errorName_x3f(v_msg_2377_);
lean_dec_ref(v_msg_2377_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2379_){
_start:
{
lean_object* v_toBaseMessage_2380_; lean_object* v_fileName_2381_; lean_object* v_pos_2382_; lean_object* v_endPos_2383_; uint8_t v_keepFullRange_2384_; uint8_t v_severity_2385_; uint8_t v_isSilent_2386_; lean_object* v_caption_2387_; lean_object* v_data_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2397_; 
v_toBaseMessage_2380_ = lean_ctor_get(v_msg_2379_, 0);
lean_inc_ref(v_toBaseMessage_2380_);
lean_dec_ref(v_msg_2379_);
v_fileName_2381_ = lean_ctor_get(v_toBaseMessage_2380_, 0);
v_pos_2382_ = lean_ctor_get(v_toBaseMessage_2380_, 1);
v_endPos_2383_ = lean_ctor_get(v_toBaseMessage_2380_, 2);
v_keepFullRange_2384_ = lean_ctor_get_uint8(v_toBaseMessage_2380_, sizeof(void*)*5);
v_severity_2385_ = lean_ctor_get_uint8(v_toBaseMessage_2380_, sizeof(void*)*5 + 1);
v_isSilent_2386_ = lean_ctor_get_uint8(v_toBaseMessage_2380_, sizeof(void*)*5 + 2);
v_caption_2387_ = lean_ctor_get(v_toBaseMessage_2380_, 3);
v_data_2388_ = lean_ctor_get(v_toBaseMessage_2380_, 4);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_toBaseMessage_2380_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2390_ = v_toBaseMessage_2380_;
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_data_2388_);
lean_inc(v_caption_2387_);
lean_inc(v_endPos_2383_);
lean_inc(v_pos_2382_);
lean_inc(v_fileName_2381_);
lean_dec(v_toBaseMessage_2380_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_data_2388_);
v___x_2393_ = l_Lean_MessageData_ofFormat(v___x_2392_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_fileName_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_pos_2382_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_endPos_2383_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_caption_2387_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___x_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2396_, sizeof(void*)*5, v_keepFullRange_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2396_, sizeof(void*)*5 + 1, v_severity_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2396_, sizeof(void*)*5 + 2, v_isSilent_2386_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2403_, uint8_t v_includeEndPos_2404_){
_start:
{
lean_object* v___y_2406_; lean_object* v___y_2410_; uint8_t v___y_2411_; uint32_t v___y_2412_; lean_object* v_str_2416_; lean_object* v_toBaseMessage_2428_; lean_object* v_kind_2429_; lean_object* v_fileName_2430_; lean_object* v_pos_2431_; lean_object* v_endPos_2432_; uint8_t v_severity_2433_; lean_object* v_caption_2434_; lean_object* v_data_2435_; lean_object* v___y_2437_; lean_object* v_str_2438_; lean_object* v___y_2446_; 
v_toBaseMessage_2428_ = lean_ctor_get(v_msg_2403_, 0);
lean_inc_ref(v_toBaseMessage_2428_);
v_kind_2429_ = lean_ctor_get(v_msg_2403_, 1);
lean_inc(v_kind_2429_);
lean_dec_ref(v_msg_2403_);
v_fileName_2430_ = lean_ctor_get(v_toBaseMessage_2428_, 0);
lean_inc_ref(v_fileName_2430_);
v_pos_2431_ = lean_ctor_get(v_toBaseMessage_2428_, 1);
lean_inc_ref(v_pos_2431_);
v_endPos_2432_ = lean_ctor_get(v_toBaseMessage_2428_, 2);
lean_inc(v_endPos_2432_);
v_severity_2433_ = lean_ctor_get_uint8(v_toBaseMessage_2428_, sizeof(void*)*5 + 1);
v_caption_2434_ = lean_ctor_get(v_toBaseMessage_2428_, 3);
lean_inc_ref(v_caption_2434_);
v_data_2435_ = lean_ctor_get(v_toBaseMessage_2428_, 4);
lean_inc(v_data_2435_);
lean_dec_ref(v_toBaseMessage_2428_);
if (v_includeEndPos_2404_ == 0)
{
lean_object* v___x_2452_; 
lean_dec(v_endPos_2432_);
v___x_2452_ = lean_box(0);
v___y_2446_ = v___x_2452_;
goto v___jp_2445_;
}
else
{
v___y_2446_ = v_endPos_2432_;
goto v___jp_2445_;
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v_str_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2408_ = lean_string_append(v___y_2406_, v___x_2407_);
return v_str_2408_;
}
v___jp_2409_:
{
uint32_t v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = 10;
v___x_2414_ = lean_uint32_dec_eq(v___y_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
v___y_2406_ = v___y_2410_;
goto v___jp_2405_;
}
else
{
if (v___y_2411_ == 0)
{
return v___y_2410_;
}
else
{
v___y_2406_ = v___y_2410_;
goto v___jp_2405_;
}
}
}
v___jp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2417_ = lean_string_utf8_byte_size(v_str_2416_);
v___x_2418_ = lean_unsigned_to_nat(0u);
v___x_2419_ = lean_nat_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_inc_ref(v_str_2416_);
v___x_2420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2420_, 0, v_str_2416_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set(v___x_2420_, 2, v___x_2417_);
v___x_2421_ = l_String_Slice_Pos_prev_x3f(v___x_2420_, v___x_2417_);
if (lean_obj_tag(v___x_2421_) == 0)
{
uint32_t v___x_2422_; 
lean_dec_ref(v___x_2420_);
v___x_2422_ = 65;
v___y_2410_ = v_str_2416_;
v___y_2411_ = v___x_2419_;
v___y_2412_ = v___x_2422_;
goto v___jp_2409_;
}
else
{
lean_object* v_val_2423_; lean_object* v___x_2424_; 
v_val_2423_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_val_2423_);
lean_dec_ref(v___x_2421_);
v___x_2424_ = l_String_Slice_Pos_get_x3f(v___x_2420_, v_val_2423_);
lean_dec(v_val_2423_);
lean_dec_ref(v___x_2420_);
if (lean_obj_tag(v___x_2424_) == 0)
{
uint32_t v___x_2425_; 
v___x_2425_ = 65;
v___y_2410_ = v_str_2416_;
v___y_2411_ = v___x_2419_;
v___y_2412_ = v___x_2425_;
goto v___jp_2409_;
}
else
{
lean_object* v_val_2426_; uint32_t v___x_2427_; 
v_val_2426_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2426_);
lean_dec_ref(v___x_2424_);
v___x_2427_ = lean_unbox_uint32(v_val_2426_);
lean_dec(v_val_2426_);
v___y_2410_ = v_str_2416_;
v___y_2411_ = v___x_2419_;
v___y_2412_ = v___x_2427_;
goto v___jp_2409_;
}
}
}
else
{
v___y_2406_ = v_str_2416_;
goto v___jp_2405_;
}
}
v___jp_2436_:
{
switch(v_severity_2433_)
{
case 0:
{
lean_dec(v___y_2437_);
lean_dec_ref(v_pos_2431_);
lean_dec_ref(v_fileName_2430_);
lean_dec(v_kind_2429_);
v_str_2416_ = v_str_2438_;
goto v___jp_2415_;
}
case 1:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_str_2441_; 
v___x_2439_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2440_ = l_Lean_errorNameOfKind_x3f(v_kind_2429_);
lean_dec(v_kind_2429_);
v_str_2441_ = l_Lean_mkErrorStringWithPos(v_fileName_2430_, v_pos_2431_, v_str_2438_, v___y_2437_, v___x_2439_, v___x_2440_);
lean_dec_ref(v_str_2438_);
v_str_2416_ = v_str_2441_;
goto v___jp_2415_;
}
default: 
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_str_2444_; 
v___x_2442_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2443_ = l_Lean_errorNameOfKind_x3f(v_kind_2429_);
lean_dec(v_kind_2429_);
v_str_2444_ = l_Lean_mkErrorStringWithPos(v_fileName_2430_, v_pos_2431_, v_str_2438_, v___y_2437_, v___x_2442_, v___x_2443_);
lean_dec_ref(v_str_2438_);
v_str_2416_ = v_str_2444_;
goto v___jp_2415_;
}
}
}
v___jp_2445_:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2448_ = lean_string_dec_eq(v_caption_2434_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v_str_2451_; 
v___x_2449_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2450_ = lean_string_append(v_caption_2434_, v___x_2449_);
v_str_2451_ = lean_string_append(v___x_2450_, v_data_2435_);
lean_dec(v_data_2435_);
v___y_2437_ = v___y_2446_;
v_str_2438_ = v_str_2451_;
goto v___jp_2436_;
}
else
{
lean_dec_ref(v_caption_2434_);
v___y_2437_ = v___y_2446_;
v_str_2438_ = v_data_2435_;
goto v___jp_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2453_, lean_object* v_includeEndPos_2454_){
_start:
{
uint8_t v_includeEndPos_boxed_2455_; lean_object* v_res_2456_; 
v_includeEndPos_boxed_2455_ = lean_unbox(v_includeEndPos_2454_);
v_res_2456_ = l_Lean_SerialMessage_toString(v_msg_2453_, v_includeEndPos_boxed_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2457_){
_start:
{
uint8_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = 0;
v___x_2459_ = l_Lean_SerialMessage_toString(v_msg_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2462_){
_start:
{
lean_object* v_data_2463_; lean_object* v___x_2464_; 
v_data_2463_ = lean_ctor_get(v_msg_2462_, 4);
v___x_2464_ = l_Lean_MessageData_kind(v_data_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Message_kind(v_msg_2465_);
lean_dec_ref(v_msg_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2467_){
_start:
{
lean_object* v_data_2468_; uint8_t v___x_2469_; 
v_data_2468_ = lean_ctor_get(v_msg_2467_, 4);
v___x_2469_ = l_Lean_MessageData_isTrace(v_data_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2470_){
_start:
{
uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_res_2471_ = l_Lean_Message_isTrace(v_msg_2470_);
lean_dec_ref(v_msg_2470_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2473_){
_start:
{
lean_object* v_fileName_2475_; lean_object* v_pos_2476_; lean_object* v_endPos_2477_; uint8_t v_keepFullRange_2478_; uint8_t v_severity_2479_; uint8_t v_isSilent_2480_; lean_object* v_caption_2481_; lean_object* v_data_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2492_; 
v_fileName_2475_ = lean_ctor_get(v_msg_2473_, 0);
v_pos_2476_ = lean_ctor_get(v_msg_2473_, 1);
v_endPos_2477_ = lean_ctor_get(v_msg_2473_, 2);
v_keepFullRange_2478_ = lean_ctor_get_uint8(v_msg_2473_, sizeof(void*)*5);
v_severity_2479_ = lean_ctor_get_uint8(v_msg_2473_, sizeof(void*)*5 + 1);
v_isSilent_2480_ = lean_ctor_get_uint8(v_msg_2473_, sizeof(void*)*5 + 2);
v_caption_2481_ = lean_ctor_get(v_msg_2473_, 3);
v_data_2482_ = lean_ctor_get(v_msg_2473_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_msg_2473_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2484_ = v_msg_2473_;
v_isShared_2485_ = v_isSharedCheck_2492_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_data_2482_);
lean_inc(v_caption_2481_);
lean_inc(v_endPos_2477_);
lean_inc(v_pos_2476_);
lean_inc(v_fileName_2475_);
lean_dec(v_msg_2473_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2492_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_inc(v_data_2482_);
v___x_2486_ = l_Lean_MessageData_toString(v_data_2482_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 4, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_fileName_2475_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_pos_2476_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_endPos_2477_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_caption_2481_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v___x_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*5, v_keepFullRange_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*5 + 1, v_severity_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*5 + 2, v_isSilent_2480_);
v___x_2488_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = l_Lean_MessageData_kind(v_data_2482_);
lean_dec(v_data_2482_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Message_serialize(v_msg_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2496_, uint8_t v_includeEndPos_2497_){
_start:
{
lean_object* v_fileName_2499_; lean_object* v_pos_2500_; lean_object* v_endPos_2501_; uint8_t v_severity_2502_; lean_object* v_caption_2503_; lean_object* v_data_2504_; lean_object* v___x_2505_; lean_object* v___y_2507_; lean_object* v___y_2511_; uint8_t v___y_2512_; uint32_t v___y_2513_; lean_object* v_str_2517_; lean_object* v___x_2529_; lean_object* v___y_2531_; lean_object* v_str_2532_; lean_object* v___y_2540_; 
v_fileName_2499_ = lean_ctor_get(v_msg_2496_, 0);
lean_inc_ref(v_fileName_2499_);
v_pos_2500_ = lean_ctor_get(v_msg_2496_, 1);
lean_inc_ref(v_pos_2500_);
v_endPos_2501_ = lean_ctor_get(v_msg_2496_, 2);
lean_inc(v_endPos_2501_);
v_severity_2502_ = lean_ctor_get_uint8(v_msg_2496_, sizeof(void*)*5 + 1);
v_caption_2503_ = lean_ctor_get(v_msg_2496_, 3);
lean_inc_ref(v_caption_2503_);
v_data_2504_ = lean_ctor_get(v_msg_2496_, 4);
lean_inc_n(v_data_2504_, 2);
lean_dec_ref(v_msg_2496_);
v___x_2505_ = l_Lean_MessageData_toString(v_data_2504_);
v___x_2529_ = l_Lean_MessageData_kind(v_data_2504_);
lean_dec(v_data_2504_);
if (v_includeEndPos_2497_ == 0)
{
lean_object* v___x_2546_; 
lean_dec(v_endPos_2501_);
v___x_2546_ = lean_box(0);
v___y_2540_ = v___x_2546_;
goto v___jp_2539_;
}
else
{
v___y_2540_ = v_endPos_2501_;
goto v___jp_2539_;
}
v___jp_2506_:
{
lean_object* v___x_2508_; lean_object* v_str_2509_; 
v___x_2508_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2509_ = lean_string_append(v___y_2507_, v___x_2508_);
return v_str_2509_;
}
v___jp_2510_:
{
uint32_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = 10;
v___x_2515_ = lean_uint32_dec_eq(v___y_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
v___y_2507_ = v___y_2511_;
goto v___jp_2506_;
}
else
{
if (v___y_2512_ == 0)
{
return v___y_2511_;
}
else
{
v___y_2507_ = v___y_2511_;
goto v___jp_2506_;
}
}
}
v___jp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2518_ = lean_string_utf8_byte_size(v_str_2517_);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_nat_dec_eq(v___x_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_inc_ref(v_str_2517_);
v___x_2521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2521_, 0, v_str_2517_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
lean_ctor_set(v___x_2521_, 2, v___x_2518_);
v___x_2522_ = l_String_Slice_Pos_prev_x3f(v___x_2521_, v___x_2518_);
if (lean_obj_tag(v___x_2522_) == 0)
{
uint32_t v___x_2523_; 
lean_dec_ref(v___x_2521_);
v___x_2523_ = 65;
v___y_2511_ = v_str_2517_;
v___y_2512_ = v___x_2520_;
v___y_2513_ = v___x_2523_;
goto v___jp_2510_;
}
else
{
lean_object* v_val_2524_; lean_object* v___x_2525_; 
v_val_2524_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_val_2524_);
lean_dec_ref(v___x_2522_);
v___x_2525_ = l_String_Slice_Pos_get_x3f(v___x_2521_, v_val_2524_);
lean_dec(v_val_2524_);
lean_dec_ref(v___x_2521_);
if (lean_obj_tag(v___x_2525_) == 0)
{
uint32_t v___x_2526_; 
v___x_2526_ = 65;
v___y_2511_ = v_str_2517_;
v___y_2512_ = v___x_2520_;
v___y_2513_ = v___x_2526_;
goto v___jp_2510_;
}
else
{
lean_object* v_val_2527_; uint32_t v___x_2528_; 
v_val_2527_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_val_2527_);
lean_dec_ref(v___x_2525_);
v___x_2528_ = lean_unbox_uint32(v_val_2527_);
lean_dec(v_val_2527_);
v___y_2511_ = v_str_2517_;
v___y_2512_ = v___x_2520_;
v___y_2513_ = v___x_2528_;
goto v___jp_2510_;
}
}
}
else
{
v___y_2507_ = v_str_2517_;
goto v___jp_2506_;
}
}
v___jp_2530_:
{
switch(v_severity_2502_)
{
case 0:
{
lean_dec(v___y_2531_);
lean_dec(v___x_2529_);
lean_dec_ref(v_pos_2500_);
lean_dec_ref(v_fileName_2499_);
v_str_2517_ = v_str_2532_;
goto v___jp_2516_;
}
case 1:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_str_2535_; 
v___x_2533_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2534_ = l_Lean_errorNameOfKind_x3f(v___x_2529_);
lean_dec(v___x_2529_);
v_str_2535_ = l_Lean_mkErrorStringWithPos(v_fileName_2499_, v_pos_2500_, v_str_2532_, v___y_2531_, v___x_2533_, v___x_2534_);
lean_dec_ref(v_str_2532_);
v_str_2517_ = v_str_2535_;
goto v___jp_2516_;
}
default: 
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_str_2538_; 
v___x_2536_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2537_ = l_Lean_errorNameOfKind_x3f(v___x_2529_);
lean_dec(v___x_2529_);
v_str_2538_ = l_Lean_mkErrorStringWithPos(v_fileName_2499_, v_pos_2500_, v_str_2532_, v___y_2531_, v___x_2536_, v___x_2537_);
lean_dec_ref(v_str_2532_);
v_str_2517_ = v_str_2538_;
goto v___jp_2516_;
}
}
}
v___jp_2539_:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2542_ = lean_string_dec_eq(v_caption_2503_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_str_2545_; 
v___x_2543_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2544_ = lean_string_append(v_caption_2503_, v___x_2543_);
v_str_2545_ = lean_string_append(v___x_2544_, v___x_2505_);
lean_dec_ref(v___x_2505_);
v___y_2531_ = v___y_2540_;
v_str_2532_ = v_str_2545_;
goto v___jp_2530_;
}
else
{
lean_dec_ref(v_caption_2503_);
v___y_2531_ = v___y_2540_;
v_str_2532_ = v___x_2505_;
goto v___jp_2530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2547_, lean_object* v_includeEndPos_2548_, lean_object* v_a_2549_){
_start:
{
uint8_t v_includeEndPos_boxed_2550_; lean_object* v_res_2551_; 
v_includeEndPos_boxed_2550_ = lean_unbox(v_includeEndPos_2548_);
v_res_2551_ = l_Lean_Message_toString(v_msg_2547_, v_includeEndPos_boxed_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2552_){
_start:
{
lean_object* v_fileName_2554_; lean_object* v_pos_2555_; lean_object* v_endPos_2556_; uint8_t v_keepFullRange_2557_; uint8_t v_severity_2558_; uint8_t v_isSilent_2559_; lean_object* v_caption_2560_; lean_object* v_data_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_fileName_2554_ = lean_ctor_get(v_msg_2552_, 0);
lean_inc_ref(v_fileName_2554_);
v_pos_2555_ = lean_ctor_get(v_msg_2552_, 1);
lean_inc_ref(v_pos_2555_);
v_endPos_2556_ = lean_ctor_get(v_msg_2552_, 2);
lean_inc(v_endPos_2556_);
v_keepFullRange_2557_ = lean_ctor_get_uint8(v_msg_2552_, sizeof(void*)*5);
v_severity_2558_ = lean_ctor_get_uint8(v_msg_2552_, sizeof(void*)*5 + 1);
v_isSilent_2559_ = lean_ctor_get_uint8(v_msg_2552_, sizeof(void*)*5 + 2);
v_caption_2560_ = lean_ctor_get(v_msg_2552_, 3);
lean_inc_ref(v_caption_2560_);
v_data_2561_ = lean_ctor_get(v_msg_2552_, 4);
lean_inc_n(v_data_2561_, 2);
lean_dec_ref(v_msg_2552_);
v___x_2562_ = l_Lean_MessageData_toString(v_data_2561_);
v___x_2563_ = l_Lean_MessageData_kind(v_data_2561_);
lean_dec(v_data_2561_);
v___x_2564_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_fileName_2554_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_box(0);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2570_ = l_Lean_instToJsonPosition_toJson(v_pos_2555_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2567_);
v___x_2573_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2574_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2556_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___x_2567_);
v___x_2577_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2578_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2578_, 0, v_keepFullRange_2557_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2567_);
v___x_2581_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2582_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2558_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2567_);
v___x_2585_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2586_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2586_, 0, v_isSilent_2559_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2567_);
v___x_2589_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_caption_2560_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2567_);
v___x_2593_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2562_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2567_);
v___x_2597_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2598_ = 1;
v___x_2599_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2563_, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2597_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2567_);
v___x_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2567_);
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2596_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2592_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2588_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2584_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2580_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2576_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2572_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2568_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2613_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2611_, v___x_2612_);
v___x_2614_ = l_Lean_Json_mkObj(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Message_toJson(v_msg_2615_);
return v_res_2617_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = l_Lean_NameSet_empty;
v___x_2620_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_2621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
lean_ctor_set(v___x_2621_, 2, v___x_2619_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_instInhabitedMessageLog_default;
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__0(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = lean_unsigned_to_nat(32u);
v___x_2625_ = lean_mk_empty_array_with_capacity(v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__1(void){
_start:
{
size_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2627_ = ((size_t)5ULL);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_unsigned_to_nat(32u);
v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
v___x_2631_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__0, &l_Lean_MessageLog_empty___closed__0_once, _init_l_Lean_MessageLog_empty___closed__0);
v___x_2632_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
lean_ctor_set(v___x_2632_, 1, v___x_2630_);
lean_ctor_set(v___x_2632_, 2, v___x_2628_);
lean_ctor_set(v___x_2632_, 3, v___x_2628_);
lean_ctor_set_usize(v___x_2632_, 4, v___x_2627_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__2(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = l_Lean_NameSet_empty;
v___x_2634_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v___x_2635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
lean_ctor_set(v___x_2635_, 2, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_2637_){
_start:
{
lean_object* v_unreported_2638_; 
v_unreported_2638_ = lean_ctor_get(v_self_2637_, 1);
lean_inc_ref(v_unreported_2638_);
return v_unreported_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_MessageLog_msgs(v_self_2639_);
lean_dec_ref(v_self_2639_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_2641_){
_start:
{
lean_object* v_reported_2642_; lean_object* v_unreported_2643_; lean_object* v___x_2644_; 
v_reported_2642_ = lean_ctor_get(v_x_2641_, 0);
lean_inc_ref(v_reported_2642_);
v_unreported_2643_ = lean_ctor_get(v_x_2641_, 1);
lean_inc_ref(v_unreported_2643_);
lean_dec_ref(v_x_2641_);
v___x_2644_ = l_Lean_PersistentArray_append___redArg(v_reported_2642_, v_unreported_2643_);
lean_dec_ref(v_unreported_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_2645_){
_start:
{
lean_object* v_unreported_2646_; uint8_t v___x_2647_; 
v_unreported_2646_ = lean_ctor_get(v_log_2645_, 1);
v___x_2647_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_2646_);
if (v___x_2647_ == 0)
{
uint8_t v___x_2648_; 
v___x_2648_ = 1;
return v___x_2648_;
}
else
{
uint8_t v___x_2649_; 
v___x_2649_ = 0;
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Lean_MessageLog_hasUnreported(v_log_2650_);
lean_dec_ref(v_log_2650_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_2653_, lean_object* v_log_2654_){
_start:
{
lean_object* v_reported_2655_; lean_object* v_unreported_2656_; lean_object* v_loggedKinds_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2665_; 
v_reported_2655_ = lean_ctor_get(v_log_2654_, 0);
v_unreported_2656_ = lean_ctor_get(v_log_2654_, 1);
v_loggedKinds_2657_ = lean_ctor_get(v_log_2654_, 2);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_log_2654_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2659_ = v_log_2654_;
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_loggedKinds_2657_);
lean_inc(v_unreported_2656_);
lean_inc(v_reported_2655_);
lean_dec(v_log_2654_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = l_Lean_PersistentArray_push___redArg(v_unreported_2656_, v_msg_2653_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2661_);
v___x_2663_ = v___x_2659_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_reported_2655_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_loggedKinds_2657_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_2668_, lean_object* v_x_2669_){
_start:
{
if (lean_obj_tag(v_x_2669_) == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_b_u2082_2668_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; 
v___x_2671_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_2672_, lean_object* v_x_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2672_, v_x_2673_);
lean_dec(v_x_2673_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_2675_, lean_object* v_k_2676_, lean_object* v_t_2677_){
_start:
{
if (lean_obj_tag(v_t_2677_) == 0)
{
lean_object* v_size_2678_; lean_object* v_k_2679_; lean_object* v_v_2680_; lean_object* v_l_2681_; lean_object* v_r_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2697_; 
v_size_2678_ = lean_ctor_get(v_t_2677_, 0);
v_k_2679_ = lean_ctor_get(v_t_2677_, 1);
v_v_2680_ = lean_ctor_get(v_t_2677_, 2);
v_l_2681_ = lean_ctor_get(v_t_2677_, 3);
v_r_2682_ = lean_ctor_get(v_t_2677_, 4);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_t_2677_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2684_ = v_t_2677_;
v_isShared_2685_ = v_isSharedCheck_2697_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_r_2682_);
lean_inc(v_l_2681_);
lean_inc(v_v_2680_);
lean_inc(v_k_2679_);
lean_inc(v_size_2678_);
lean_dec(v_t_2677_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2697_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
uint8_t v___x_2686_; 
v___x_2686_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2676_, v_k_2679_);
switch(v___x_2686_)
{
case 0:
{
lean_object* v_impl_2687_; lean_object* v___x_2688_; 
lean_del_object(v___x_2684_);
lean_dec(v_size_2678_);
v_impl_2687_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2675_, v_k_2676_, v_l_2681_);
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2679_, v_v_2680_, v_impl_2687_, v_r_2682_);
return v___x_2688_;
}
case 1:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_val_2691_; lean_object* v___x_2693_; 
lean_dec(v_k_2679_);
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_v_2680_);
v___x_2690_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2675_, v___x_2689_);
lean_dec_ref(v___x_2689_);
v_val_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_val_2691_);
lean_dec(v___x_2690_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 2, v_val_2691_);
lean_ctor_set(v___x_2684_, 1, v_k_2676_);
v___x_2693_ = v___x_2684_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_size_2678_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_k_2676_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_val_2691_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_l_2681_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v_r_2682_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
default: 
{
lean_object* v_impl_2695_; lean_object* v___x_2696_; 
lean_del_object(v___x_2684_);
lean_dec(v_size_2678_);
v_impl_2695_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2675_, v_k_2676_, v_r_2682_);
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2679_, v_v_2680_, v_l_2681_, v_impl_2695_);
return v___x_2696_;
}
}
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v_val_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2675_, v___x_2698_);
v_val_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_val_2700_);
lean_dec(v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v_k_2676_);
lean_ctor_set(v___x_2702_, 2, v_val_2700_);
lean_ctor_set(v___x_2702_, 3, v_t_2677_);
lean_ctor_set(v___x_2702_, 4, v_t_2677_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_2703_, lean_object* v_x_2704_){
_start:
{
if (lean_obj_tag(v_x_2704_) == 0)
{
lean_object* v_k_2705_; lean_object* v_v_2706_; lean_object* v_l_2707_; lean_object* v_r_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_k_2705_ = lean_ctor_get(v_x_2704_, 1);
lean_inc(v_k_2705_);
v_v_2706_ = lean_ctor_get(v_x_2704_, 2);
lean_inc(v_v_2706_);
v_l_2707_ = lean_ctor_get(v_x_2704_, 3);
lean_inc(v_l_2707_);
v_r_2708_ = lean_ctor_get(v_x_2704_, 4);
lean_inc(v_r_2708_);
lean_dec_ref(v_x_2704_);
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2703_, v_l_2707_);
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_2706_, v_k_2705_, v___x_2709_);
v_init_2703_ = v___x_2710_;
v_x_2704_ = v_r_2708_;
goto _start;
}
else
{
return v_init_2703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_2712_, lean_object* v_l_u2082_2713_){
_start:
{
lean_object* v_reported_2714_; lean_object* v_unreported_2715_; lean_object* v_loggedKinds_2716_; lean_object* v_reported_2717_; lean_object* v_unreported_2718_; lean_object* v_loggedKinds_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2729_; 
v_reported_2714_ = lean_ctor_get(v_l_u2081_2712_, 0);
lean_inc_ref(v_reported_2714_);
v_unreported_2715_ = lean_ctor_get(v_l_u2081_2712_, 1);
lean_inc_ref(v_unreported_2715_);
v_loggedKinds_2716_ = lean_ctor_get(v_l_u2081_2712_, 2);
lean_inc(v_loggedKinds_2716_);
lean_dec_ref(v_l_u2081_2712_);
v_reported_2717_ = lean_ctor_get(v_l_u2082_2713_, 0);
v_unreported_2718_ = lean_ctor_get(v_l_u2082_2713_, 1);
v_loggedKinds_2719_ = lean_ctor_get(v_l_u2082_2713_, 2);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_l_u2082_2713_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2721_ = v_l_u2082_2713_;
v_isShared_2722_ = v_isSharedCheck_2729_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_loggedKinds_2719_);
lean_inc(v_unreported_2718_);
lean_inc(v_reported_2717_);
lean_dec(v_l_u2082_2713_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2729_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2723_ = l_Lean_PersistentArray_append___redArg(v_reported_2714_, v_reported_2717_);
lean_dec_ref(v_reported_2717_);
v___x_2724_ = l_Lean_PersistentArray_append___redArg(v_unreported_2715_, v_unreported_2718_);
lean_dec_ref(v_unreported_2718_);
v___x_2725_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_2716_, v_loggedKinds_2719_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 2, v___x_2725_);
lean_ctor_set(v___x_2721_, 1, v___x_2724_);
lean_ctor_set(v___x_2721_, 0, v___x_2723_);
v___x_2727_ = v___x_2721_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_2730_, lean_object* v_k_2731_, lean_object* v_t_2732_, lean_object* v_hl_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2730_, v_k_2731_, v_t_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_2735_, lean_object* v_t_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2735_, v_t_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_2740_, size_t v_i_2741_, size_t v_stop_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_eq(v_i_2741_, v_stop_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; uint8_t v_severity_2745_; uint8_t v___x_2746_; 
v___x_2744_ = lean_array_uget_borrowed(v_as_2740_, v_i_2741_);
v_severity_2745_ = lean_ctor_get_uint8(v___x_2744_, sizeof(void*)*5 + 1);
v___x_2746_ = 1;
if (v_severity_2745_ == 2)
{
return v___x_2746_;
}
else
{
if (v___x_2743_ == 0)
{
size_t v___x_2747_; size_t v___x_2748_; 
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_add(v_i_2741_, v___x_2747_);
v_i_2741_ = v___x_2748_;
goto _start;
}
else
{
return v___x_2746_;
}
}
}
else
{
uint8_t v___x_2750_; 
v___x_2750_ = 0;
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_2751_, lean_object* v_i_2752_, lean_object* v_stop_2753_){
_start:
{
size_t v_i_boxed_2754_; size_t v_stop_boxed_2755_; uint8_t v_res_2756_; lean_object* v_r_2757_; 
v_i_boxed_2754_ = lean_unbox_usize(v_i_2752_);
lean_dec(v_i_2752_);
v_stop_boxed_2755_ = lean_unbox_usize(v_stop_2753_);
lean_dec(v_stop_2753_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_2751_, v_i_boxed_2754_, v_stop_boxed_2755_);
lean_dec_ref(v_as_2751_);
v_r_2757_ = lean_box(v_res_2756_);
return v_r_2757_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
lean_object* v_cs_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_cs_2759_ = lean_ctor_get(v_x_2758_, 0);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_array_get_size(v_cs_2759_);
v___x_2762_ = lean_nat_dec_lt(v___x_2760_, v___x_2761_);
if (v___x_2762_ == 0)
{
return v___x_2762_;
}
else
{
if (v___x_2762_ == 0)
{
return v___x_2762_;
}
else
{
size_t v___x_2763_; size_t v___x_2764_; uint8_t v___x_2765_; 
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = lean_usize_of_nat(v___x_2761_);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_2759_, v___x_2763_, v___x_2764_);
return v___x_2765_;
}
}
}
else
{
lean_object* v_vs_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v_vs_2766_ = lean_ctor_get(v_x_2758_, 0);
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = lean_array_get_size(v_vs_2766_);
v___x_2769_ = lean_nat_dec_lt(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
return v___x_2769_;
}
else
{
if (v___x_2769_ == 0)
{
return v___x_2769_;
}
else
{
size_t v___x_2770_; size_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = lean_usize_of_nat(v___x_2768_);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_2766_, v___x_2770_, v___x_2771_);
return v___x_2772_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_2773_, size_t v_i_2774_, size_t v_stop_2775_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_eq(v_i_2774_, v_stop_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = lean_array_uget_borrowed(v_as_2773_, v_i_2774_);
v___x_2778_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_2777_);
if (v___x_2778_ == 0)
{
size_t v___x_2779_; size_t v___x_2780_; 
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_add(v_i_2774_, v___x_2779_);
v_i_2774_ = v___x_2780_;
goto _start;
}
else
{
return v___x_2778_;
}
}
else
{
uint8_t v___x_2782_; 
v___x_2782_ = 0;
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_2783_, lean_object* v_i_2784_, lean_object* v_stop_2785_){
_start:
{
size_t v_i_boxed_2786_; size_t v_stop_boxed_2787_; uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_i_boxed_2786_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_stop_boxed_2787_ = lean_unbox_usize(v_stop_2785_);
lean_dec(v_stop_2785_);
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_2783_, v_i_boxed_2786_, v_stop_boxed_2787_);
lean_dec_ref(v_as_2783_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_2790_);
lean_dec_ref(v_x_2790_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_2793_){
_start:
{
lean_object* v_root_2794_; lean_object* v_tail_2795_; uint8_t v___x_2796_; 
v_root_2794_ = lean_ctor_get(v_t_2793_, 0);
v_tail_2795_ = lean_ctor_get(v_t_2793_, 1);
v___x_2796_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_2794_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = lean_unsigned_to_nat(0u);
v___x_2798_ = lean_array_get_size(v_tail_2795_);
v___x_2799_ = lean_nat_dec_lt(v___x_2797_, v___x_2798_);
if (v___x_2799_ == 0)
{
return v___x_2796_;
}
else
{
if (v___x_2799_ == 0)
{
return v___x_2796_;
}
else
{
size_t v___x_2800_; size_t v___x_2801_; uint8_t v___x_2802_; 
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = lean_usize_of_nat(v___x_2798_);
v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_2795_, v___x_2800_, v___x_2801_);
return v___x_2802_;
}
}
}
else
{
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_2803_){
_start:
{
uint8_t v_res_2804_; lean_object* v_r_2805_; 
v_res_2804_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_2803_);
lean_dec_ref(v_t_2803_);
v_r_2805_ = lean_box(v_res_2804_);
return v_r_2805_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_2806_, lean_object* v_as_2807_, size_t v_i_2808_, size_t v_stop_2809_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_eq(v_i_2808_, v_stop_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; uint8_t v_severity_2812_; uint8_t v___x_2813_; 
v___x_2811_ = lean_array_uget_borrowed(v_as_2807_, v_i_2808_);
v_severity_2812_ = lean_ctor_get_uint8(v___x_2811_, sizeof(void*)*5 + 1);
v___x_2813_ = 1;
if (v_severity_2812_ == 2)
{
return v___x_2813_;
}
else
{
if (v___x_2806_ == 0)
{
size_t v___x_2814_; size_t v___x_2815_; 
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2808_, v___x_2814_);
v_i_2808_ = v___x_2815_;
goto _start;
}
else
{
return v___x_2813_;
}
}
}
else
{
uint8_t v___x_2817_; 
v___x_2817_ = 0;
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_2818_, lean_object* v_as_2819_, lean_object* v_i_2820_, lean_object* v_stop_2821_){
_start:
{
uint8_t v___x_1884__boxed_2822_; size_t v_i_boxed_2823_; size_t v_stop_boxed_2824_; uint8_t v_res_2825_; lean_object* v_r_2826_; 
v___x_1884__boxed_2822_ = lean_unbox(v___x_2818_);
v_i_boxed_2823_ = lean_unbox_usize(v_i_2820_);
lean_dec(v_i_2820_);
v_stop_boxed_2824_ = lean_unbox_usize(v_stop_2821_);
lean_dec(v_stop_2821_);
v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_2822_, v_as_2819_, v_i_boxed_2823_, v_stop_boxed_2824_);
lean_dec_ref(v_as_2819_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_2827_, lean_object* v_x_2828_){
_start:
{
if (lean_obj_tag(v_x_2828_) == 0)
{
lean_object* v_cs_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v_cs_2829_ = lean_ctor_get(v_x_2828_, 0);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_array_get_size(v_cs_2829_);
v___x_2832_ = lean_nat_dec_lt(v___x_2830_, v___x_2831_);
if (v___x_2832_ == 0)
{
return v___x_2832_;
}
else
{
if (v___x_2832_ == 0)
{
return v___x_2832_;
}
else
{
size_t v___x_2833_; size_t v___x_2834_; uint8_t v___x_2835_; 
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = lean_usize_of_nat(v___x_2831_);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_2827_, v_cs_2829_, v___x_2833_, v___x_2834_);
return v___x_2835_;
}
}
}
else
{
lean_object* v_vs_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v_vs_2836_ = lean_ctor_get(v_x_2828_, 0);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = lean_array_get_size(v_vs_2836_);
v___x_2839_ = lean_nat_dec_lt(v___x_2837_, v___x_2838_);
if (v___x_2839_ == 0)
{
return v___x_2839_;
}
else
{
if (v___x_2839_ == 0)
{
return v___x_2839_;
}
else
{
size_t v___x_2840_; size_t v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = lean_usize_of_nat(v___x_2838_);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2827_, v_vs_2836_, v___x_2840_, v___x_2841_);
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_2843_, lean_object* v_as_2844_, size_t v_i_2845_, size_t v_stop_2846_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_eq(v_i_2845_, v_stop_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = lean_array_uget_borrowed(v_as_2844_, v_i_2845_);
v___x_2849_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2843_, v___x_2848_);
if (v___x_2849_ == 0)
{
size_t v___x_2850_; size_t v___x_2851_; 
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2845_, v___x_2850_);
v_i_2845_ = v___x_2851_;
goto _start;
}
else
{
return v___x_2849_;
}
}
else
{
uint8_t v___x_2853_; 
v___x_2853_ = 0;
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2854_, lean_object* v_as_2855_, lean_object* v_i_2856_, lean_object* v_stop_2857_){
_start:
{
uint8_t v___x_1901__boxed_2858_; size_t v_i_boxed_2859_; size_t v_stop_boxed_2860_; uint8_t v_res_2861_; lean_object* v_r_2862_; 
v___x_1901__boxed_2858_ = lean_unbox(v___x_2854_);
v_i_boxed_2859_ = lean_unbox_usize(v_i_2856_);
lean_dec(v_i_2856_);
v_stop_boxed_2860_ = lean_unbox_usize(v_stop_2857_);
lean_dec(v_stop_2857_);
v_res_2861_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_2858_, v_as_2855_, v_i_boxed_2859_, v_stop_boxed_2860_);
lean_dec_ref(v_as_2855_);
v_r_2862_ = lean_box(v_res_2861_);
return v_r_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_2863_, lean_object* v_x_2864_){
_start:
{
uint8_t v___x_1909__boxed_2865_; uint8_t v_res_2866_; lean_object* v_r_2867_; 
v___x_1909__boxed_2865_ = lean_unbox(v___x_2863_);
v_res_2866_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_2865_, v_x_2864_);
lean_dec_ref(v_x_2864_);
v_r_2867_ = lean_box(v_res_2866_);
return v_r_2867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_2868_, lean_object* v_t_2869_){
_start:
{
lean_object* v_root_2870_; lean_object* v_tail_2871_; uint8_t v___x_2872_; 
v_root_2870_ = lean_ctor_get(v_t_2869_, 0);
v_tail_2871_ = lean_ctor_get(v_t_2869_, 1);
v___x_2872_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2868_, v_root_2870_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_array_get_size(v_tail_2871_);
v___x_2875_ = lean_nat_dec_lt(v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
return v___x_2872_;
}
else
{
if (v___x_2875_ == 0)
{
return v___x_2872_;
}
else
{
size_t v___x_2876_; size_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = lean_usize_of_nat(v___x_2874_);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2868_, v_tail_2871_, v___x_2876_, v___x_2877_);
return v___x_2878_;
}
}
}
else
{
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_2879_, lean_object* v_t_2880_){
_start:
{
uint8_t v___x_1952__boxed_2881_; uint8_t v_res_2882_; lean_object* v_r_2883_; 
v___x_1952__boxed_2881_ = lean_unbox(v___x_2879_);
v_res_2882_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_2881_, v_t_2880_);
lean_dec_ref(v_t_2880_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_2884_){
_start:
{
lean_object* v_reported_2885_; lean_object* v_unreported_2886_; uint8_t v___x_2887_; 
v_reported_2885_ = lean_ctor_get(v_log_2884_, 0);
v_unreported_2886_ = lean_ctor_get(v_log_2884_, 1);
v___x_2887_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_2885_);
if (v___x_2887_ == 0)
{
uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_2887_, v_unreported_2886_);
return v___x_2888_;
}
else
{
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Lean_MessageLog_hasErrors(v_log_2889_);
lean_dec_ref(v_log_2889_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_2892_){
_start:
{
lean_object* v_reported_2893_; lean_object* v_unreported_2894_; lean_object* v_loggedKinds_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2906_; 
v_reported_2893_ = lean_ctor_get(v_log_2892_, 0);
v_unreported_2894_ = lean_ctor_get(v_log_2892_, 1);
v_loggedKinds_2895_ = lean_ctor_get(v_log_2892_, 2);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_log_2892_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2897_ = v_log_2892_;
v_isShared_2898_ = v_isSharedCheck_2906_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_loggedKinds_2895_);
lean_inc(v_unreported_2894_);
lean_inc(v_reported_2893_);
lean_dec(v_log_2892_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2906_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2899_ = l_Lean_PersistentArray_append___redArg(v_reported_2893_, v_unreported_2894_);
lean_dec_ref(v_unreported_2894_);
v___x_2900_ = lean_unsigned_to_nat(32u);
v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
lean_dec_ref(v___x_2901_);
v___x_2902_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 1, v___x_2902_);
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2904_ = v___x_2897_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v_loggedKinds_2895_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_2907_, size_t v_i_2908_, lean_object* v_bs_2909_){
_start:
{
uint8_t v___x_2910_; 
v___x_2910_ = lean_usize_dec_lt(v_i_2908_, v_sz_2907_);
if (v___x_2910_ == 0)
{
return v_bs_2909_;
}
else
{
lean_object* v_v_2911_; lean_object* v_fileName_2912_; lean_object* v_pos_2913_; lean_object* v_endPos_2914_; uint8_t v_keepFullRange_2915_; uint8_t v_severity_2916_; uint8_t v_isSilent_2917_; lean_object* v_caption_2918_; lean_object* v_data_2919_; lean_object* v___x_2920_; lean_object* v_bs_x27_2921_; lean_object* v___y_2923_; 
v_v_2911_ = lean_array_uget(v_bs_2909_, v_i_2908_);
v_fileName_2912_ = lean_ctor_get(v_v_2911_, 0);
v_pos_2913_ = lean_ctor_get(v_v_2911_, 1);
v_endPos_2914_ = lean_ctor_get(v_v_2911_, 2);
v_keepFullRange_2915_ = lean_ctor_get_uint8(v_v_2911_, sizeof(void*)*5);
v_severity_2916_ = lean_ctor_get_uint8(v_v_2911_, sizeof(void*)*5 + 1);
v_isSilent_2917_ = lean_ctor_get_uint8(v_v_2911_, sizeof(void*)*5 + 2);
v_caption_2918_ = lean_ctor_get(v_v_2911_, 3);
v_data_2919_ = lean_ctor_get(v_v_2911_, 4);
v___x_2920_ = lean_unsigned_to_nat(0u);
v_bs_x27_2921_ = lean_array_uset(v_bs_2909_, v_i_2908_, v___x_2920_);
if (v_severity_2916_ == 2)
{
lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2935_; 
lean_inc(v_data_2919_);
lean_inc_ref(v_caption_2918_);
lean_inc(v_endPos_2914_);
lean_inc_ref(v_pos_2913_);
lean_inc_ref(v_fileName_2912_);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_v_2911_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; lean_object* v_unused_2937_; lean_object* v_unused_2938_; lean_object* v_unused_2939_; lean_object* v_unused_2940_; 
v_unused_2936_ = lean_ctor_get(v_v_2911_, 4);
lean_dec(v_unused_2936_);
v_unused_2937_ = lean_ctor_get(v_v_2911_, 3);
lean_dec(v_unused_2937_);
v_unused_2938_ = lean_ctor_get(v_v_2911_, 2);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_v_2911_, 1);
lean_dec(v_unused_2939_);
v_unused_2940_ = lean_ctor_get(v_v_2911_, 0);
lean_dec(v_unused_2940_);
v___x_2929_ = v_v_2911_;
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
else
{
lean_dec(v_v_2911_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
uint8_t v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = 1;
if (v_isShared_2930_ == 0)
{
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_fileName_2912_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_pos_2913_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_endPos_2914_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_caption_2918_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_data_2919_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*5, v_keepFullRange_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*5 + 2, v_isSilent_2917_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*5 + 1, v___x_2931_);
v___y_2923_ = v___x_2933_;
goto v___jp_2922_;
}
}
}
else
{
v___y_2923_ = v_v_2911_;
goto v___jp_2922_;
}
v___jp_2922_:
{
size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = lean_usize_add(v_i_2908_, v___x_2924_);
v___x_2926_ = lean_array_uset(v_bs_x27_2921_, v_i_2908_, v___y_2923_);
v_i_2908_ = v___x_2925_;
v_bs_2909_ = v___x_2926_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_2941_, lean_object* v_i_2942_, lean_object* v_bs_2943_){
_start:
{
size_t v_sz_boxed_2944_; size_t v_i_boxed_2945_; lean_object* v_res_2946_; 
v_sz_boxed_2944_ = lean_unbox_usize(v_sz_2941_);
lean_dec(v_sz_2941_);
v_i_boxed_2945_ = lean_unbox_usize(v_i_2942_);
lean_dec(v_i_2942_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_2944_, v_i_boxed_2945_, v_bs_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_2947_, size_t v_i_2948_, lean_object* v_bs_2949_){
_start:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_usize_dec_lt(v_i_2948_, v_sz_2947_);
if (v___x_2950_ == 0)
{
return v_bs_2949_;
}
else
{
lean_object* v_v_2951_; lean_object* v___x_2952_; lean_object* v_bs_x27_2953_; lean_object* v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v_v_2951_ = lean_array_uget(v_bs_2949_, v_i_2948_);
v___x_2952_ = lean_unsigned_to_nat(0u);
v_bs_x27_2953_ = lean_array_uset(v_bs_2949_, v_i_2948_, v___x_2952_);
v___x_2954_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_2951_);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2948_, v___x_2955_);
v___x_2957_ = lean_array_uset(v_bs_x27_2953_, v_i_2948_, v___x_2954_);
v_i_2948_ = v___x_2956_;
v_bs_2949_ = v___x_2957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_2959_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
lean_object* v_cs_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2970_; 
v_cs_2960_ = lean_ctor_get(v_x_2959_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2962_ = v_x_2959_;
v_isShared_2963_ = v_isSharedCheck_2970_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_cs_2960_);
lean_dec(v_x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2970_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
size_t v_sz_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v_sz_2964_ = lean_array_size(v_cs_2960_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_2964_, v___x_2965_, v_cs_2960_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2966_);
v___x_2968_ = v___x_2962_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_vs_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2981_; 
v_vs_2971_ = lean_ctor_get(v_x_2959_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2973_ = v_x_2959_;
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_vs_2971_);
lean_dec(v_x_2959_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
size_t v_sz_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v_sz_2975_ = lean_array_size(v_vs_2971_);
v___x_2976_ = ((size_t)0ULL);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2975_, v___x_2976_, v_vs_2971_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2977_);
v___x_2979_ = v___x_2973_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2982_, lean_object* v_i_2983_, lean_object* v_bs_2984_){
_start:
{
size_t v_sz_boxed_2985_; size_t v_i_boxed_2986_; lean_object* v_res_2987_; 
v_sz_boxed_2985_ = lean_unbox_usize(v_sz_2982_);
lean_dec(v_sz_2982_);
v_i_boxed_2986_ = lean_unbox_usize(v_i_2983_);
lean_dec(v_i_2983_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_2985_, v_i_boxed_2986_, v_bs_2984_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_2988_){
_start:
{
lean_object* v_root_2989_; lean_object* v_tail_2990_; lean_object* v_size_2991_; size_t v_shift_2992_; lean_object* v_tailOff_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3004_; 
v_root_2989_ = lean_ctor_get(v_t_2988_, 0);
v_tail_2990_ = lean_ctor_get(v_t_2988_, 1);
v_size_2991_ = lean_ctor_get(v_t_2988_, 2);
v_shift_2992_ = lean_ctor_get_usize(v_t_2988_, 4);
v_tailOff_2993_ = lean_ctor_get(v_t_2988_, 3);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_t_2988_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2995_ = v_t_2988_;
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_tailOff_2993_);
lean_inc(v_size_2991_);
lean_inc(v_tail_2990_);
lean_inc(v_root_2989_);
lean_dec(v_t_2988_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; size_t v_sz_2998_; size_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2997_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_2989_);
v_sz_2998_ = lean_array_size(v_tail_2990_);
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2998_, v___x_2999_, v_tail_2990_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_3000_);
lean_ctor_set(v___x_2995_, 0, v___x_2997_);
v___x_3002_ = v___x_2995_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_size_2991_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_tailOff_2993_);
lean_ctor_set_usize(v_reuseFailAlloc_3003_, 4, v_shift_2992_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3005_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v_unreported_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3018_; 
v___x_3006_ = lean_unsigned_to_nat(32u);
v___x_3007_ = lean_mk_empty_array_with_capacity(v___x_3006_);
lean_dec_ref(v___x_3007_);
v___x_3008_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3009_ = lean_ctor_get(v_log_3005_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_log_3005_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; lean_object* v_unused_3020_; 
v_unused_3019_ = lean_ctor_get(v_log_3005_, 2);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v_log_3005_, 0);
lean_dec(v_unused_3020_);
v___x_3011_ = v_log_3005_;
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_unreported_3009_);
lean_dec(v_log_3005_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3013_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3009_);
v___x_3014_ = l_Lean_NameSet_empty;
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 2, v___x_3014_);
lean_ctor_set(v___x_3011_, 1, v___x_3013_);
lean_ctor_set(v___x_3011_, 0, v___x_3008_);
v___x_3016_ = v___x_3011_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3021_, size_t v_i_3022_, lean_object* v_bs_3023_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_lt(v_i_3022_, v_sz_3021_);
if (v___x_3024_ == 0)
{
return v_bs_3023_;
}
else
{
lean_object* v_v_3025_; lean_object* v_fileName_3026_; lean_object* v_pos_3027_; lean_object* v_endPos_3028_; uint8_t v_keepFullRange_3029_; uint8_t v_severity_3030_; uint8_t v_isSilent_3031_; lean_object* v_caption_3032_; lean_object* v_data_3033_; lean_object* v___x_3034_; lean_object* v_bs_x27_3035_; lean_object* v___y_3037_; 
v_v_3025_ = lean_array_uget(v_bs_3023_, v_i_3022_);
v_fileName_3026_ = lean_ctor_get(v_v_3025_, 0);
v_pos_3027_ = lean_ctor_get(v_v_3025_, 1);
v_endPos_3028_ = lean_ctor_get(v_v_3025_, 2);
v_keepFullRange_3029_ = lean_ctor_get_uint8(v_v_3025_, sizeof(void*)*5);
v_severity_3030_ = lean_ctor_get_uint8(v_v_3025_, sizeof(void*)*5 + 1);
v_isSilent_3031_ = lean_ctor_get_uint8(v_v_3025_, sizeof(void*)*5 + 2);
v_caption_3032_ = lean_ctor_get(v_v_3025_, 3);
v_data_3033_ = lean_ctor_get(v_v_3025_, 4);
v___x_3034_ = lean_unsigned_to_nat(0u);
v_bs_x27_3035_ = lean_array_uset(v_bs_3023_, v_i_3022_, v___x_3034_);
if (v_severity_3030_ == 2)
{
lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
lean_inc(v_data_3033_);
lean_inc_ref(v_caption_3032_);
lean_inc(v_endPos_3028_);
lean_inc_ref(v_pos_3027_);
lean_inc_ref(v_fileName_3026_);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_v_3025_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; lean_object* v_unused_3052_; lean_object* v_unused_3053_; lean_object* v_unused_3054_; 
v_unused_3050_ = lean_ctor_get(v_v_3025_, 4);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_v_3025_, 3);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v_v_3025_, 2);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v_v_3025_, 1);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v_v_3025_, 0);
lean_dec(v_unused_3054_);
v___x_3043_ = v_v_3025_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v_v_3025_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
uint8_t v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = 0;
if (v_isShared_3044_ == 0)
{
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_fileName_3026_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_pos_3027_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_endPos_3028_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_caption_3032_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_data_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*5, v_keepFullRange_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*5 + 2, v_isSilent_3031_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*5 + 1, v___x_3045_);
v___y_3037_ = v___x_3047_;
goto v___jp_3036_;
}
}
}
else
{
v___y_3037_ = v_v_3025_;
goto v___jp_3036_;
}
v___jp_3036_:
{
size_t v___x_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = ((size_t)1ULL);
v___x_3039_ = lean_usize_add(v_i_3022_, v___x_3038_);
v___x_3040_ = lean_array_uset(v_bs_x27_3035_, v_i_3022_, v___y_3037_);
v_i_3022_ = v___x_3039_;
v_bs_3023_ = v___x_3040_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3055_, lean_object* v_i_3056_, lean_object* v_bs_3057_){
_start:
{
size_t v_sz_boxed_3058_; size_t v_i_boxed_3059_; lean_object* v_res_3060_; 
v_sz_boxed_3058_ = lean_unbox_usize(v_sz_3055_);
lean_dec(v_sz_3055_);
v_i_boxed_3059_ = lean_unbox_usize(v_i_3056_);
lean_dec(v_i_3056_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3058_, v_i_boxed_3059_, v_bs_3057_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3061_, size_t v_i_3062_, lean_object* v_bs_3063_){
_start:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_lt(v_i_3062_, v_sz_3061_);
if (v___x_3064_ == 0)
{
return v_bs_3063_;
}
else
{
lean_object* v_v_3065_; lean_object* v___x_3066_; lean_object* v_bs_x27_3067_; lean_object* v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v_v_3065_ = lean_array_uget(v_bs_3063_, v_i_3062_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v_bs_x27_3067_ = lean_array_uset(v_bs_3063_, v_i_3062_, v___x_3066_);
v___x_3068_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3065_);
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3062_, v___x_3069_);
v___x_3071_ = lean_array_uset(v_bs_x27_3067_, v_i_3062_, v___x_3068_);
v_i_3062_ = v___x_3070_;
v_bs_3063_ = v___x_3071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3073_){
_start:
{
if (lean_obj_tag(v_x_3073_) == 0)
{
lean_object* v_cs_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3084_; 
v_cs_3074_ = lean_ctor_get(v_x_3073_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_x_3073_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3076_ = v_x_3073_;
v_isShared_3077_ = v_isSharedCheck_3084_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_cs_3074_);
lean_dec(v_x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3084_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
size_t v_sz_3078_; size_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v_sz_3078_ = lean_array_size(v_cs_3074_);
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3078_, v___x_3079_, v_cs_3074_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3080_);
v___x_3082_ = v___x_3076_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_object* v_vs_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3095_; 
v_vs_3085_ = lean_ctor_get(v_x_3073_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_x_3073_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3087_ = v_x_3073_;
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_vs_3085_);
lean_dec(v_x_3073_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v_sz_3089_ = lean_array_size(v_vs_3085_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3089_, v___x_3090_, v_vs_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3091_);
v___x_3093_ = v___x_3087_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3096_, lean_object* v_i_3097_, lean_object* v_bs_3098_){
_start:
{
size_t v_sz_boxed_3099_; size_t v_i_boxed_3100_; lean_object* v_res_3101_; 
v_sz_boxed_3099_ = lean_unbox_usize(v_sz_3096_);
lean_dec(v_sz_3096_);
v_i_boxed_3100_ = lean_unbox_usize(v_i_3097_);
lean_dec(v_i_3097_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3099_, v_i_boxed_3100_, v_bs_3098_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3102_){
_start:
{
lean_object* v_root_3103_; lean_object* v_tail_3104_; lean_object* v_size_3105_; size_t v_shift_3106_; lean_object* v_tailOff_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3118_; 
v_root_3103_ = lean_ctor_get(v_t_3102_, 0);
v_tail_3104_ = lean_ctor_get(v_t_3102_, 1);
v_size_3105_ = lean_ctor_get(v_t_3102_, 2);
v_shift_3106_ = lean_ctor_get_usize(v_t_3102_, 4);
v_tailOff_3107_ = lean_ctor_get(v_t_3102_, 3);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_t_3102_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3109_ = v_t_3102_;
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_tailOff_3107_);
lean_inc(v_size_3105_);
lean_inc(v_tail_3104_);
lean_inc(v_root_3103_);
lean_dec(v_t_3102_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3118_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; size_t v_sz_3112_; size_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3111_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3103_);
v_sz_3112_ = lean_array_size(v_tail_3104_);
v___x_3113_ = ((size_t)0ULL);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3112_, v___x_3113_, v_tail_3104_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3114_);
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3116_ = v___x_3109_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_size_3105_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_tailOff_3107_);
lean_ctor_set_usize(v_reuseFailAlloc_3117_, 4, v_shift_3106_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3119_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v_unreported_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3132_; 
v___x_3120_ = lean_unsigned_to_nat(32u);
v___x_3121_ = lean_mk_empty_array_with_capacity(v___x_3120_);
lean_dec_ref(v___x_3121_);
v___x_3122_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3123_ = lean_ctor_get(v_log_3119_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_log_3119_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3133_ = lean_ctor_get(v_log_3119_, 2);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_log_3119_, 0);
lean_dec(v_unused_3134_);
v___x_3125_ = v_log_3119_;
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_unreported_3123_);
lean_dec(v_log_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3127_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3123_);
v___x_3128_ = l_Lean_NameSet_empty;
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 2, v___x_3128_);
lean_ctor_set(v___x_3125_, 1, v___x_3127_);
lean_ctor_set(v___x_3125_, 0, v___x_3122_);
v___x_3130_ = v___x_3125_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3135_, size_t v_i_3136_, size_t v_stop_3137_, lean_object* v_b_3138_){
_start:
{
lean_object* v___y_3140_; uint8_t v___x_3144_; 
v___x_3144_ = lean_usize_dec_eq(v_i_3136_, v_stop_3137_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; uint8_t v_severity_3146_; 
v___x_3145_ = lean_array_uget_borrowed(v_as_3135_, v_i_3136_);
v_severity_3146_ = lean_ctor_get_uint8(v___x_3145_, sizeof(void*)*5 + 1);
if (v_severity_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_inc(v___x_3145_);
v___x_3147_ = l_Lean_PersistentArray_push___redArg(v_b_3138_, v___x_3145_);
v___y_3140_ = v___x_3147_;
goto v___jp_3139_;
}
else
{
v___y_3140_ = v_b_3138_;
goto v___jp_3139_;
}
}
else
{
return v_b_3138_;
}
v___jp_3139_:
{
size_t v___x_3141_; size_t v___x_3142_; 
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_add(v_i_3136_, v___x_3141_);
v_i_3136_ = v___x_3142_;
v_b_3138_ = v___y_3140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3148_, lean_object* v_i_3149_, lean_object* v_stop_3150_, lean_object* v_b_3151_){
_start:
{
size_t v_i_boxed_3152_; size_t v_stop_boxed_3153_; lean_object* v_res_3154_; 
v_i_boxed_3152_ = lean_unbox_usize(v_i_3149_);
lean_dec(v_i_3149_);
v_stop_boxed_3153_ = lean_unbox_usize(v_stop_3150_);
lean_dec(v_stop_3150_);
v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3148_, v_i_boxed_3152_, v_stop_boxed_3153_, v_b_3151_);
lean_dec_ref(v_as_3148_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3155_, lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3155_) == 0)
{
lean_object* v_cs_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_cs_3157_ = lean_ctor_get(v_x_3155_, 0);
v___x_3158_ = lean_unsigned_to_nat(0u);
v___x_3159_ = lean_array_get_size(v_cs_3157_);
v___x_3160_ = lean_nat_dec_lt(v___x_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
return v_x_3156_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_nat_dec_le(v___x_3159_, v___x_3159_);
if (v___x_3161_ == 0)
{
if (v___x_3160_ == 0)
{
return v_x_3156_;
}
else
{
size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = lean_usize_of_nat(v___x_3159_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3157_, v___x_3162_, v___x_3163_, v_x_3156_);
return v___x_3164_;
}
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3159_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3157_, v___x_3165_, v___x_3166_, v_x_3156_);
return v___x_3167_;
}
}
}
else
{
lean_object* v_vs_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_vs_3168_ = lean_ctor_get(v_x_3155_, 0);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_array_get_size(v_vs_3168_);
v___x_3171_ = lean_nat_dec_lt(v___x_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
return v_x_3156_;
}
else
{
uint8_t v___x_3172_; 
v___x_3172_ = lean_nat_dec_le(v___x_3170_, v___x_3170_);
if (v___x_3172_ == 0)
{
if (v___x_3171_ == 0)
{
return v_x_3156_;
}
else
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((size_t)0ULL);
v___x_3174_ = lean_usize_of_nat(v___x_3170_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3168_, v___x_3173_, v___x_3174_, v_x_3156_);
return v___x_3175_;
}
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = lean_usize_of_nat(v___x_3170_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3168_, v___x_3176_, v___x_3177_, v_x_3156_);
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3179_, size_t v_i_3180_, size_t v_stop_3181_, lean_object* v_b_3182_){
_start:
{
uint8_t v___x_3183_; 
v___x_3183_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; size_t v___x_3186_; size_t v___x_3187_; 
v___x_3184_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
v___x_3185_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3184_, v_b_3182_);
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3180_, v___x_3186_);
v_i_3180_ = v___x_3187_;
v_b_3182_ = v___x_3185_;
goto _start;
}
else
{
return v_b_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3189_, lean_object* v_i_3190_, lean_object* v_stop_3191_, lean_object* v_b_3192_){
_start:
{
size_t v_i_boxed_3193_; size_t v_stop_boxed_3194_; lean_object* v_res_3195_; 
v_i_boxed_3193_ = lean_unbox_usize(v_i_3190_);
lean_dec(v_i_3190_);
v_stop_boxed_3194_ = lean_unbox_usize(v_stop_3191_);
lean_dec(v_stop_3191_);
v_res_3195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3189_, v_i_boxed_3193_, v_stop_boxed_3194_, v_b_3192_);
lean_dec_ref(v_as_3189_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3196_, v_x_3197_);
lean_dec_ref(v_x_3196_);
return v_res_3198_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3200_, size_t v_x_3201_, size_t v_x_3202_, lean_object* v_x_3203_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_object* v_cs_3204_; lean_object* v___x_3205_; size_t v___x_3206_; lean_object* v_j_3207_; lean_object* v___x_3208_; size_t v___x_3209_; size_t v___x_3210_; size_t v___x_3211_; size_t v___x_3212_; size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_cs_3204_ = lean_ctor_get(v_x_3200_, 0);
v___x_3205_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3206_ = lean_usize_shift_right(v_x_3201_, v_x_3202_);
v_j_3207_ = lean_usize_to_nat(v___x_3206_);
v___x_3208_ = lean_array_get_borrowed(v___x_3205_, v_cs_3204_, v_j_3207_);
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_shift_left(v___x_3209_, v_x_3202_);
v___x_3211_ = lean_usize_sub(v___x_3210_, v___x_3209_);
v___x_3212_ = lean_usize_land(v_x_3201_, v___x_3211_);
v___x_3213_ = ((size_t)5ULL);
v___x_3214_ = lean_usize_sub(v_x_3202_, v___x_3213_);
v___x_3215_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3208_, v___x_3212_, v___x_3214_, v_x_3203_);
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = lean_nat_add(v_j_3207_, v___x_3216_);
lean_dec(v_j_3207_);
v___x_3218_ = lean_array_get_size(v_cs_3204_);
v___x_3219_ = lean_nat_dec_lt(v___x_3217_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_dec(v___x_3217_);
return v___x_3215_;
}
else
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_nat_dec_le(v___x_3218_, v___x_3218_);
if (v___x_3220_ == 0)
{
if (v___x_3219_ == 0)
{
lean_dec(v___x_3217_);
return v___x_3215_;
}
else
{
size_t v___x_3221_; size_t v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_usize_of_nat(v___x_3217_);
lean_dec(v___x_3217_);
v___x_3222_ = lean_usize_of_nat(v___x_3218_);
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3204_, v___x_3221_, v___x_3222_, v___x_3215_);
return v___x_3223_;
}
}
else
{
size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_usize_of_nat(v___x_3217_);
lean_dec(v___x_3217_);
v___x_3225_ = lean_usize_of_nat(v___x_3218_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3204_, v___x_3224_, v___x_3225_, v___x_3215_);
return v___x_3226_;
}
}
}
else
{
lean_object* v_vs_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_vs_3227_ = lean_ctor_get(v_x_3200_, 0);
v___x_3228_ = lean_usize_to_nat(v_x_3201_);
v___x_3229_ = lean_array_get_size(v_vs_3227_);
v___x_3230_ = lean_nat_dec_lt(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_dec(v___x_3228_);
return v_x_3203_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_nat_dec_le(v___x_3229_, v___x_3229_);
if (v___x_3231_ == 0)
{
if (v___x_3230_ == 0)
{
lean_dec(v___x_3228_);
return v_x_3203_;
}
else
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_usize_of_nat(v___x_3228_);
lean_dec(v___x_3228_);
v___x_3233_ = lean_usize_of_nat(v___x_3229_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3227_, v___x_3232_, v___x_3233_, v_x_3203_);
return v___x_3234_;
}
}
else
{
size_t v___x_3235_; size_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_usize_of_nat(v___x_3228_);
lean_dec(v___x_3228_);
v___x_3236_ = lean_usize_of_nat(v___x_3229_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3227_, v___x_3235_, v___x_3236_, v_x_3203_);
return v___x_3237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3238_, lean_object* v_x_3239_, lean_object* v_x_3240_, lean_object* v_x_3241_){
_start:
{
size_t v_x_1528__boxed_3242_; size_t v_x_1529__boxed_3243_; lean_object* v_res_3244_; 
v_x_1528__boxed_3242_ = lean_unbox_usize(v_x_3239_);
lean_dec(v_x_3239_);
v_x_1529__boxed_3243_ = lean_unbox_usize(v_x_3240_);
lean_dec(v_x_3240_);
v_res_3244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3238_, v_x_1528__boxed_3242_, v_x_1529__boxed_3243_, v_x_3241_);
lean_dec_ref(v_x_3238_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3245_, lean_object* v_init_3246_, lean_object* v_start_3247_){
_start:
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = lean_nat_dec_eq(v_start_3247_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v_root_3250_; lean_object* v_tail_3251_; size_t v_shift_3252_; lean_object* v_tailOff_3253_; uint8_t v___x_3254_; 
v_root_3250_ = lean_ctor_get(v_t_3245_, 0);
v_tail_3251_ = lean_ctor_get(v_t_3245_, 1);
v_shift_3252_ = lean_ctor_get_usize(v_t_3245_, 4);
v_tailOff_3253_ = lean_ctor_get(v_t_3245_, 3);
v___x_3254_ = lean_nat_dec_le(v_tailOff_3253_, v_start_3247_);
if (v___x_3254_ == 0)
{
size_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3255_ = lean_usize_of_nat(v_start_3247_);
v___x_3256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3250_, v___x_3255_, v_shift_3252_, v_init_3246_);
v___x_3257_ = lean_array_get_size(v_tail_3251_);
v___x_3258_ = lean_nat_dec_lt(v___x_3248_, v___x_3257_);
if (v___x_3258_ == 0)
{
return v___x_3256_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_nat_dec_le(v___x_3257_, v___x_3257_);
if (v___x_3259_ == 0)
{
if (v___x_3258_ == 0)
{
return v___x_3256_;
}
else
{
size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = ((size_t)0ULL);
v___x_3261_ = lean_usize_of_nat(v___x_3257_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3251_, v___x_3260_, v___x_3261_, v___x_3256_);
return v___x_3262_;
}
}
else
{
size_t v___x_3263_; size_t v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = lean_usize_of_nat(v___x_3257_);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3251_, v___x_3263_, v___x_3264_, v___x_3256_);
return v___x_3265_;
}
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3266_ = lean_nat_sub(v_start_3247_, v_tailOff_3253_);
v___x_3267_ = lean_array_get_size(v_tail_3251_);
v___x_3268_ = lean_nat_dec_lt(v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_dec(v___x_3266_);
return v_init_3246_;
}
else
{
uint8_t v___x_3269_; 
v___x_3269_ = lean_nat_dec_le(v___x_3267_, v___x_3267_);
if (v___x_3269_ == 0)
{
if (v___x_3268_ == 0)
{
lean_dec(v___x_3266_);
return v_init_3246_;
}
else
{
size_t v___x_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_usize_of_nat(v___x_3266_);
lean_dec(v___x_3266_);
v___x_3271_ = lean_usize_of_nat(v___x_3267_);
v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3251_, v___x_3270_, v___x_3271_, v_init_3246_);
return v___x_3272_;
}
}
else
{
size_t v___x_3273_; size_t v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_usize_of_nat(v___x_3266_);
lean_dec(v___x_3266_);
v___x_3274_ = lean_usize_of_nat(v___x_3267_);
v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3251_, v___x_3273_, v___x_3274_, v_init_3246_);
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_root_3276_; lean_object* v_tail_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v_root_3276_ = lean_ctor_get(v_t_3245_, 0);
v_tail_3277_ = lean_ctor_get(v_t_3245_, 1);
v___x_3278_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3276_, v_init_3246_);
v___x_3279_ = lean_array_get_size(v_tail_3277_);
v___x_3280_ = lean_nat_dec_lt(v___x_3248_, v___x_3279_);
if (v___x_3280_ == 0)
{
return v___x_3278_;
}
else
{
uint8_t v___x_3281_; 
v___x_3281_ = lean_nat_dec_le(v___x_3279_, v___x_3279_);
if (v___x_3281_ == 0)
{
if (v___x_3280_ == 0)
{
return v___x_3278_;
}
else
{
size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = lean_usize_of_nat(v___x_3279_);
v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3277_, v___x_3282_, v___x_3283_, v___x_3278_);
return v___x_3284_;
}
}
else
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((size_t)0ULL);
v___x_3286_ = lean_usize_of_nat(v___x_3279_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3277_, v___x_3285_, v___x_3286_, v___x_3278_);
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3288_, lean_object* v_init_3289_, lean_object* v_start_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3288_, v_init_3289_, v_start_3290_);
lean_dec(v_start_3290_);
lean_dec_ref(v_t_3288_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3292_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_unreported_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3306_; 
v___x_3293_ = lean_unsigned_to_nat(32u);
v___x_3294_ = lean_mk_empty_array_with_capacity(v___x_3293_);
lean_dec_ref(v___x_3294_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3297_ = lean_ctor_get(v_log_3292_, 1);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_log_3292_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; lean_object* v_unused_3308_; 
v_unused_3307_ = lean_ctor_get(v_log_3292_, 2);
lean_dec(v_unused_3307_);
v_unused_3308_ = lean_ctor_get(v_log_3292_, 0);
lean_dec(v_unused_3308_);
v___x_3299_ = v_log_3292_;
v_isShared_3300_ = v_isSharedCheck_3306_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_unreported_3297_);
lean_dec(v_log_3292_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3306_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3301_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3297_, v___x_3296_, v___x_3295_);
lean_dec_ref(v_unreported_3297_);
v___x_3302_ = l_Lean_NameSet_empty;
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 2, v___x_3302_);
lean_ctor_set(v___x_3299_, 1, v___x_3301_);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
v___x_3304_ = v___x_3299_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3309_, size_t v_i_3310_, size_t v_stop_3311_, lean_object* v_b_3312_){
_start:
{
lean_object* v___y_3314_; uint8_t v___x_3318_; 
v___x_3318_ = lean_usize_dec_eq(v_i_3310_, v_stop_3311_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; uint8_t v_severity_3320_; 
v___x_3319_ = lean_array_uget_borrowed(v_as_3309_, v_i_3310_);
v_severity_3320_ = lean_ctor_get_uint8(v___x_3319_, sizeof(void*)*5 + 1);
if (v_severity_3320_ == 1)
{
lean_object* v___x_3321_; 
lean_inc(v___x_3319_);
v___x_3321_ = l_Lean_PersistentArray_push___redArg(v_b_3312_, v___x_3319_);
v___y_3314_ = v___x_3321_;
goto v___jp_3313_;
}
else
{
v___y_3314_ = v_b_3312_;
goto v___jp_3313_;
}
}
else
{
return v_b_3312_;
}
v___jp_3313_:
{
size_t v___x_3315_; size_t v___x_3316_; 
v___x_3315_ = ((size_t)1ULL);
v___x_3316_ = lean_usize_add(v_i_3310_, v___x_3315_);
v_i_3310_ = v___x_3316_;
v_b_3312_ = v___y_3314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3322_, lean_object* v_i_3323_, lean_object* v_stop_3324_, lean_object* v_b_3325_){
_start:
{
size_t v_i_boxed_3326_; size_t v_stop_boxed_3327_; lean_object* v_res_3328_; 
v_i_boxed_3326_ = lean_unbox_usize(v_i_3323_);
lean_dec(v_i_3323_);
v_stop_boxed_3327_ = lean_unbox_usize(v_stop_3324_);
lean_dec(v_stop_3324_);
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3322_, v_i_boxed_3326_, v_stop_boxed_3327_, v_b_3325_);
lean_dec_ref(v_as_3322_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
if (lean_obj_tag(v_x_3329_) == 0)
{
lean_object* v_cs_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_cs_3331_ = lean_ctor_get(v_x_3329_, 0);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_array_get_size(v_cs_3331_);
v___x_3334_ = lean_nat_dec_lt(v___x_3332_, v___x_3333_);
if (v___x_3334_ == 0)
{
return v_x_3330_;
}
else
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_nat_dec_le(v___x_3333_, v___x_3333_);
if (v___x_3335_ == 0)
{
if (v___x_3334_ == 0)
{
return v_x_3330_;
}
else
{
size_t v___x_3336_; size_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = lean_usize_of_nat(v___x_3333_);
v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3331_, v___x_3336_, v___x_3337_, v_x_3330_);
return v___x_3338_;
}
}
else
{
size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((size_t)0ULL);
v___x_3340_ = lean_usize_of_nat(v___x_3333_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3331_, v___x_3339_, v___x_3340_, v_x_3330_);
return v___x_3341_;
}
}
}
else
{
lean_object* v_vs_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_vs_3342_ = lean_ctor_get(v_x_3329_, 0);
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = lean_array_get_size(v_vs_3342_);
v___x_3345_ = lean_nat_dec_lt(v___x_3343_, v___x_3344_);
if (v___x_3345_ == 0)
{
return v_x_3330_;
}
else
{
uint8_t v___x_3346_; 
v___x_3346_ = lean_nat_dec_le(v___x_3344_, v___x_3344_);
if (v___x_3346_ == 0)
{
if (v___x_3345_ == 0)
{
return v_x_3330_;
}
else
{
size_t v___x_3347_; size_t v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = ((size_t)0ULL);
v___x_3348_ = lean_usize_of_nat(v___x_3344_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3342_, v___x_3347_, v___x_3348_, v_x_3330_);
return v___x_3349_;
}
}
else
{
size_t v___x_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = lean_usize_of_nat(v___x_3344_);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3342_, v___x_3350_, v___x_3351_, v_x_3330_);
return v___x_3352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3353_, size_t v_i_3354_, size_t v_stop_3355_, lean_object* v_b_3356_){
_start:
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_usize_dec_eq(v_i_3354_, v_stop_3355_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; size_t v___x_3360_; size_t v___x_3361_; 
v___x_3358_ = lean_array_uget_borrowed(v_as_3353_, v_i_3354_);
v___x_3359_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3358_, v_b_3356_);
v___x_3360_ = ((size_t)1ULL);
v___x_3361_ = lean_usize_add(v_i_3354_, v___x_3360_);
v_i_3354_ = v___x_3361_;
v_b_3356_ = v___x_3359_;
goto _start;
}
else
{
return v_b_3356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3363_, lean_object* v_i_3364_, lean_object* v_stop_3365_, lean_object* v_b_3366_){
_start:
{
size_t v_i_boxed_3367_; size_t v_stop_boxed_3368_; lean_object* v_res_3369_; 
v_i_boxed_3367_ = lean_unbox_usize(v_i_3364_);
lean_dec(v_i_3364_);
v_stop_boxed_3368_ = lean_unbox_usize(v_stop_3365_);
lean_dec(v_stop_3365_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3363_, v_i_boxed_3367_, v_stop_boxed_3368_, v_b_3366_);
lean_dec_ref(v_as_3363_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3370_, lean_object* v_x_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3370_, v_x_3371_);
lean_dec_ref(v_x_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3373_, size_t v_x_3374_, size_t v_x_3375_, lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3373_) == 0)
{
lean_object* v_cs_3377_; lean_object* v___x_3378_; size_t v___x_3379_; lean_object* v_j_3380_; lean_object* v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; size_t v___x_3384_; size_t v___x_3385_; size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_cs_3377_ = lean_ctor_get(v_x_3373_, 0);
v___x_3378_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3379_ = lean_usize_shift_right(v_x_3374_, v_x_3375_);
v_j_3380_ = lean_usize_to_nat(v___x_3379_);
v___x_3381_ = lean_array_get_borrowed(v___x_3378_, v_cs_3377_, v_j_3380_);
v___x_3382_ = ((size_t)1ULL);
v___x_3383_ = lean_usize_shift_left(v___x_3382_, v_x_3375_);
v___x_3384_ = lean_usize_sub(v___x_3383_, v___x_3382_);
v___x_3385_ = lean_usize_land(v_x_3374_, v___x_3384_);
v___x_3386_ = ((size_t)5ULL);
v___x_3387_ = lean_usize_sub(v_x_3375_, v___x_3386_);
v___x_3388_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3381_, v___x_3385_, v___x_3387_, v_x_3376_);
v___x_3389_ = lean_unsigned_to_nat(1u);
v___x_3390_ = lean_nat_add(v_j_3380_, v___x_3389_);
lean_dec(v_j_3380_);
v___x_3391_ = lean_array_get_size(v_cs_3377_);
v___x_3392_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec(v___x_3390_);
return v___x_3388_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
if (v___x_3393_ == 0)
{
if (v___x_3392_ == 0)
{
lean_dec(v___x_3390_);
return v___x_3388_;
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_usize_of_nat(v___x_3390_);
lean_dec(v___x_3390_);
v___x_3395_ = lean_usize_of_nat(v___x_3391_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3377_, v___x_3394_, v___x_3395_, v___x_3388_);
return v___x_3396_;
}
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = lean_usize_of_nat(v___x_3390_);
lean_dec(v___x_3390_);
v___x_3398_ = lean_usize_of_nat(v___x_3391_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3377_, v___x_3397_, v___x_3398_, v___x_3388_);
return v___x_3399_;
}
}
}
else
{
lean_object* v_vs_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_vs_3400_ = lean_ctor_get(v_x_3373_, 0);
v___x_3401_ = lean_usize_to_nat(v_x_3374_);
v___x_3402_ = lean_array_get_size(v_vs_3400_);
v___x_3403_ = lean_nat_dec_lt(v___x_3401_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_dec(v___x_3401_);
return v_x_3376_;
}
else
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_nat_dec_le(v___x_3402_, v___x_3402_);
if (v___x_3404_ == 0)
{
if (v___x_3403_ == 0)
{
lean_dec(v___x_3401_);
return v_x_3376_;
}
else
{
size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = lean_usize_of_nat(v___x_3401_);
lean_dec(v___x_3401_);
v___x_3406_ = lean_usize_of_nat(v___x_3402_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3400_, v___x_3405_, v___x_3406_, v_x_3376_);
return v___x_3407_;
}
}
else
{
size_t v___x_3408_; size_t v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_usize_of_nat(v___x_3401_);
lean_dec(v___x_3401_);
v___x_3409_ = lean_usize_of_nat(v___x_3402_);
v___x_3410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3400_, v___x_3408_, v___x_3409_, v_x_3376_);
return v___x_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3411_, lean_object* v_x_3412_, lean_object* v_x_3413_, lean_object* v_x_3414_){
_start:
{
size_t v_x_1527__boxed_3415_; size_t v_x_1528__boxed_3416_; lean_object* v_res_3417_; 
v_x_1527__boxed_3415_ = lean_unbox_usize(v_x_3412_);
lean_dec(v_x_3412_);
v_x_1528__boxed_3416_ = lean_unbox_usize(v_x_3413_);
lean_dec(v_x_3413_);
v_res_3417_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3411_, v_x_1527__boxed_3415_, v_x_1528__boxed_3416_, v_x_3414_);
lean_dec_ref(v_x_3411_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3418_, lean_object* v_init_3419_, lean_object* v_start_3420_){
_start:
{
lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_nat_dec_eq(v_start_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v_root_3423_; lean_object* v_tail_3424_; size_t v_shift_3425_; lean_object* v_tailOff_3426_; uint8_t v___x_3427_; 
v_root_3423_ = lean_ctor_get(v_t_3418_, 0);
v_tail_3424_ = lean_ctor_get(v_t_3418_, 1);
v_shift_3425_ = lean_ctor_get_usize(v_t_3418_, 4);
v_tailOff_3426_ = lean_ctor_get(v_t_3418_, 3);
v___x_3427_ = lean_nat_dec_le(v_tailOff_3426_, v_start_3420_);
if (v___x_3427_ == 0)
{
size_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3428_ = lean_usize_of_nat(v_start_3420_);
v___x_3429_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3423_, v___x_3428_, v_shift_3425_, v_init_3419_);
v___x_3430_ = lean_array_get_size(v_tail_3424_);
v___x_3431_ = lean_nat_dec_lt(v___x_3421_, v___x_3430_);
if (v___x_3431_ == 0)
{
return v___x_3429_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_nat_dec_le(v___x_3430_, v___x_3430_);
if (v___x_3432_ == 0)
{
if (v___x_3431_ == 0)
{
return v___x_3429_;
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = lean_usize_of_nat(v___x_3430_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3424_, v___x_3433_, v___x_3434_, v___x_3429_);
return v___x_3435_;
}
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3430_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3424_, v___x_3436_, v___x_3437_, v___x_3429_);
return v___x_3438_;
}
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = lean_nat_sub(v_start_3420_, v_tailOff_3426_);
v___x_3440_ = lean_array_get_size(v_tail_3424_);
v___x_3441_ = lean_nat_dec_lt(v___x_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_dec(v___x_3439_);
return v_init_3419_;
}
else
{
uint8_t v___x_3442_; 
v___x_3442_ = lean_nat_dec_le(v___x_3440_, v___x_3440_);
if (v___x_3442_ == 0)
{
if (v___x_3441_ == 0)
{
lean_dec(v___x_3439_);
return v_init_3419_;
}
else
{
size_t v___x_3443_; size_t v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = lean_usize_of_nat(v___x_3439_);
lean_dec(v___x_3439_);
v___x_3444_ = lean_usize_of_nat(v___x_3440_);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3424_, v___x_3443_, v___x_3444_, v_init_3419_);
return v___x_3445_;
}
}
else
{
size_t v___x_3446_; size_t v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_usize_of_nat(v___x_3439_);
lean_dec(v___x_3439_);
v___x_3447_ = lean_usize_of_nat(v___x_3440_);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3424_, v___x_3446_, v___x_3447_, v_init_3419_);
return v___x_3448_;
}
}
}
}
else
{
lean_object* v_root_3449_; lean_object* v_tail_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_root_3449_ = lean_ctor_get(v_t_3418_, 0);
v_tail_3450_ = lean_ctor_get(v_t_3418_, 1);
v___x_3451_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3449_, v_init_3419_);
v___x_3452_ = lean_array_get_size(v_tail_3450_);
v___x_3453_ = lean_nat_dec_lt(v___x_3421_, v___x_3452_);
if (v___x_3453_ == 0)
{
return v___x_3451_;
}
else
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_nat_dec_le(v___x_3452_, v___x_3452_);
if (v___x_3454_ == 0)
{
if (v___x_3453_ == 0)
{
return v___x_3451_;
}
else
{
size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = lean_usize_of_nat(v___x_3452_);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3450_, v___x_3455_, v___x_3456_, v___x_3451_);
return v___x_3457_;
}
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3452_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3450_, v___x_3458_, v___x_3459_, v___x_3451_);
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3461_, lean_object* v_init_3462_, lean_object* v_start_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3461_, v_init_3462_, v_start_3463_);
lean_dec(v_start_3463_);
lean_dec_ref(v_t_3461_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v_unreported_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3479_; 
v___x_3466_ = lean_unsigned_to_nat(32u);
v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
lean_dec_ref(v___x_3467_);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3470_ = lean_ctor_get(v_log_3465_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_log_3465_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; lean_object* v_unused_3481_; 
v_unused_3480_ = lean_ctor_get(v_log_3465_, 2);
lean_dec(v_unused_3480_);
v_unused_3481_ = lean_ctor_get(v_log_3465_, 0);
lean_dec(v_unused_3481_);
v___x_3472_ = v_log_3465_;
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_unreported_3470_);
lean_dec(v_log_3465_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3479_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3474_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3470_, v___x_3469_, v___x_3468_);
lean_dec_ref(v_unreported_3470_);
v___x_3475_ = l_Lean_NameSet_empty;
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 2, v___x_3475_);
lean_ctor_set(v___x_3472_, 1, v___x_3474_);
lean_ctor_set(v___x_3472_, 0, v___x_3469_);
v___x_3477_ = v___x_3472_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3482_, lean_object* v_log_3483_, lean_object* v_f_3484_){
_start:
{
lean_object* v_unreported_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_unreported_3485_ = lean_ctor_get(v_log_3483_, 1);
lean_inc_ref(v_unreported_3485_);
lean_dec_ref(v_log_3483_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = l_Lean_PersistentArray_forM___redArg(v_inst_3482_, v_unreported_3485_, v_f_3484_, v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3488_, lean_object* v_inst_3489_, lean_object* v_log_3490_, lean_object* v_f_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_MessageLog_forM___redArg(v_inst_3489_, v_log_3490_, v_f_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3493_){
_start:
{
lean_object* v_unreported_3494_; lean_object* v___x_3495_; 
v_unreported_3494_ = lean_ctor_get(v_log_3493_, 1);
v___x_3495_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_MessageLog_toList(v_log_3496_);
lean_dec_ref(v_log_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3498_){
_start:
{
lean_object* v_unreported_3499_; lean_object* v___x_3500_; 
v_unreported_3499_ = lean_ctor_get(v_log_3498_, 1);
v___x_3500_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_MessageLog_toArray(v_log_3501_);
lean_dec_ref(v_log_3501_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_unsigned_to_nat(2u);
v___x_3505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v_msg_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v_msg_3506_);
v___x_3509_ = l_Lean_MessageData_nestD(v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3510_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = l_Lean_MessageData_ofExpr(v_e_3510_);
v___x_3512_ = l_Lean_indentD(v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3513_, lean_object* v_msg_3514_){
_start:
{
lean_object* v_env_3516_; lean_object* v_mctx_3517_; lean_object* v_lctx_3518_; lean_object* v_opts_3519_; lean_object* v_currNamespace_3520_; lean_object* v_openDecls_3521_; lean_object* v___x_3522_; lean_object* v_msg_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_env_3516_ = lean_ctor_get(v_ctx_3513_, 0);
v_mctx_3517_ = lean_ctor_get(v_ctx_3513_, 1);
v_lctx_3518_ = lean_ctor_get(v_ctx_3513_, 2);
v_opts_3519_ = lean_ctor_get(v_ctx_3513_, 3);
v_currNamespace_3520_ = lean_ctor_get(v_ctx_3513_, 4);
v_openDecls_3521_ = lean_ctor_get(v_ctx_3513_, 5);
lean_inc(v_openDecls_3521_);
lean_inc(v_currNamespace_3520_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_currNamespace_3520_);
lean_ctor_set(v___x_3522_, 1, v_openDecls_3521_);
v_msg_3523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3523_, 0, v___x_3522_);
lean_ctor_set(v_msg_3523_, 1, v_msg_3514_);
lean_inc_ref(v_opts_3519_);
lean_inc_ref(v_lctx_3518_);
lean_inc_ref(v_mctx_3517_);
lean_inc_ref(v_env_3516_);
v___x_3524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3524_, 0, v_env_3516_);
lean_ctor_set(v___x_3524_, 1, v_mctx_3517_);
lean_ctor_set(v___x_3524_, 2, v_lctx_3518_);
lean_ctor_set(v___x_3524_, 3, v_opts_3519_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
v___x_3526_ = l_Lean_MessageData_format(v_msg_3523_, v___x_3525_);
v___x_3527_ = l_Std_Format_defWidth;
v___x_3528_ = lean_unsigned_to_nat(0u);
v___x_3529_ = l_Std_Format_pretty(v___x_3526_, v___x_3527_, v___x_3528_, v___x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3530_, lean_object* v_msg_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3530_, v_msg_3531_);
lean_dec_ref(v_ctx_3530_);
return v_res_3533_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object* v_s_3534_, lean_object* v_a_3535_, uint8_t v_b_3536_){
_start:
{
lean_object* v_str_3537_; lean_object* v_startInclusive_3538_; lean_object* v_endExclusive_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_str_3537_ = lean_ctor_get(v_s_3534_, 0);
v_startInclusive_3538_ = lean_ctor_get(v_s_3534_, 1);
v_endExclusive_3539_ = lean_ctor_get(v_s_3534_, 2);
v___x_3540_ = lean_nat_sub(v_endExclusive_3539_, v_startInclusive_3538_);
v___x_3541_ = lean_nat_dec_eq(v_a_3535_, v___x_3540_);
lean_dec(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; uint32_t v___x_3543_; uint32_t v___x_3544_; uint8_t v___x_3545_; 
v___x_3542_ = lean_nat_add(v_startInclusive_3538_, v_a_3535_);
lean_dec(v_a_3535_);
v___x_3543_ = lean_string_utf8_get_fast(v_str_3537_, v___x_3542_);
v___x_3544_ = 10;
v___x_3545_ = lean_uint32_dec_eq(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_string_utf8_next_fast(v_str_3537_, v___x_3542_);
lean_dec(v___x_3542_);
v___x_3547_ = lean_nat_sub(v___x_3546_, v_startInclusive_3538_);
v_a_3535_ = v___x_3547_;
v_b_3536_ = v___x_3545_;
goto _start;
}
else
{
lean_dec(v___x_3542_);
return v___x_3545_;
}
}
else
{
lean_dec(v_a_3535_);
return v_b_3536_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object* v_s_3549_, lean_object* v_a_3550_, lean_object* v_b_3551_){
_start:
{
uint8_t v_b_boxed_3552_; uint8_t v_res_3553_; lean_object* v_r_3554_; 
v_b_boxed_3552_ = lean_unbox(v_b_3551_);
v_res_3553_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3549_, v_a_3550_, v_b_boxed_3552_);
lean_dec_ref(v_s_3549_);
v_r_3554_ = lean_box(v_res_3553_);
return v_r_3554_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object* v_s_3555_){
_start:
{
lean_object* v_searcher_3556_; uint8_t v___x_3557_; uint8_t v___x_3558_; 
v_searcher_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = 0;
v___x_3558_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3555_, v_searcher_3556_, v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v_s_3559_){
_start:
{
uint8_t v_res_3560_; lean_object* v_r_3561_; 
v_res_3560_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v_s_3559_);
lean_dec_ref(v_s_3559_);
v_r_3561_ = lean_box(v_res_3560_);
return v_r_3561_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_3566_ = l_Lean_MessageData_ofFormat(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_3571_ = l_Lean_MessageData_ofFormat(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3573_ = l_Lean_MessageData_ofFormat(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3574_, lean_object* v_maxInlineLength_3575_, lean_object* v_ctx_3576_){
_start:
{
lean_object* v_msg_3578_; lean_object* v___x_3579_; uint8_t v___y_3581_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v_msg_3578_ = l_Lean_MessageData_ofExpr(v_e_3574_);
lean_inc_ref(v_msg_3578_);
v___x_3579_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3576_, v_msg_3578_);
v___x_3589_ = lean_string_length(v___x_3579_);
v___x_3590_ = lean_nat_dec_lt(v_maxInlineLength_3575_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = lean_string_utf8_byte_size(v___x_3579_);
v___x_3593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3579_);
lean_ctor_set(v___x_3593_, 1, v___x_3591_);
lean_ctor_set(v___x_3593_, 2, v___x_3592_);
v___x_3594_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3593_);
lean_dec_ref(v___x_3593_);
v___y_3581_ = v___x_3594_;
goto v___jp_3580_;
}
else
{
lean_dec_ref(v___x_3579_);
v___y_3581_ = v___x_3590_;
goto v___jp_3580_;
}
v___jp_3580_:
{
if (v___y_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3582_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v_msg_3578_);
v___x_3584_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = l_Lean_indentD(v_msg_3578_);
v___x_3587_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3595_, lean_object* v_maxInlineLength_3596_, lean_object* v_ctx_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_inlineExpr___lam__0(v_e_3595_, v_maxInlineLength_3596_, v_ctx_3597_);
lean_dec_ref(v_ctx_3597_);
lean_dec(v_maxInlineLength_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3603_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3604_ = l_Lean_MessageData_ofExpr(v_e_3600_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3608_, lean_object* v_x_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_inlineExpr___lam__2(v_e_3608_, v_x_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3612_, lean_object* v_maxInlineLength_3613_){
_start:
{
lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; 
lean_inc_ref_n(v_e_3612_, 2);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3614_, 0, v_e_3612_);
lean_closure_set(v___f_3614_, 1, v_maxInlineLength_3613_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3615_, 0, v_e_3612_);
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3616_, 0, v_e_3612_);
v___x_3617_ = l_Lean_MessageData_lazy(v___f_3614_, v___f_3615_, v___f_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object* v_s_3618_, lean_object* v_inst_3619_, lean_object* v_R_3620_, lean_object* v_a_3621_, uint8_t v_b_3622_, lean_object* v_c_3623_){
_start:
{
uint8_t v___x_3624_; 
v___x_3624_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3618_, v_a_3621_, v_b_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object* v_s_3625_, lean_object* v_inst_3626_, lean_object* v_R_3627_, lean_object* v_a_3628_, lean_object* v_b_3629_, lean_object* v_c_3630_){
_start:
{
uint8_t v_b_boxed_3631_; uint8_t v_res_3632_; lean_object* v_r_3633_; 
v_b_boxed_3631_ = lean_unbox(v_b_3629_);
v_res_3632_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(v_s_3625_, v_inst_3626_, v_R_3627_, v_a_3628_, v_b_boxed_3631_, v_c_3630_);
lean_dec_ref(v_s_3625_);
v_r_3633_ = lean_box(v_res_3632_);
return v_r_3633_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_3638_ = l_Lean_MessageData_ofFormat(v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_3639_, lean_object* v_maxInlineLength_3640_, lean_object* v_ctx_3641_){
_start:
{
lean_object* v_msg_3643_; lean_object* v___x_3644_; uint8_t v___y_3646_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v_msg_3643_ = l_Lean_MessageData_ofExpr(v_e_3639_);
lean_inc_ref(v_msg_3643_);
v___x_3644_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3641_, v_msg_3643_);
v___x_3652_ = lean_string_length(v___x_3644_);
v___x_3653_ = lean_nat_dec_lt(v_maxInlineLength_3640_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3654_ = lean_unsigned_to_nat(0u);
v___x_3655_ = lean_string_utf8_byte_size(v___x_3644_);
v___x_3656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3644_);
lean_ctor_set(v___x_3656_, 1, v___x_3654_);
lean_ctor_set(v___x_3656_, 2, v___x_3655_);
v___x_3657_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3656_);
lean_dec_ref(v___x_3656_);
v___y_3646_ = v___x_3657_;
goto v___jp_3645_;
}
else
{
lean_dec_ref(v___x_3644_);
v___y_3646_ = v___x_3653_;
goto v___jp_3645_;
}
v___jp_3645_:
{
if (v___y_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3647_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v_msg_3643_);
v___x_3649_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
return v___x_3650_;
}
else
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_indentD(v_msg_3643_);
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_3658_, lean_object* v_maxInlineLength_3659_, lean_object* v_ctx_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_inlineExprTrailing___lam__0(v_e_3658_, v_maxInlineLength_3659_, v_ctx_3660_);
lean_dec_ref(v_ctx_3660_);
lean_dec(v_maxInlineLength_3659_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_3663_, lean_object* v_x_3664_){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3666_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3667_ = l_Lean_MessageData_ofExpr(v_e_3663_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_3671_, lean_object* v_x_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_inlineExprTrailing___lam__2(v_e_3671_, v_x_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_3675_, lean_object* v_maxInlineLength_3676_){
_start:
{
lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___x_3680_; 
lean_inc_ref_n(v_e_3675_, 2);
v___f_3677_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3677_, 0, v_e_3675_);
lean_closure_set(v___f_3677_, 1, v_maxInlineLength_3676_);
v___f_3678_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3678_, 0, v_e_3675_);
v___f_3679_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3679_, 0, v_e_3675_);
v___x_3680_ = l_Lean_MessageData_lazy(v___f_3677_, v___f_3678_, v___f_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_3685_ = l_Lean_MessageData_ofFormat(v___x_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_3690_ = l_Lean_MessageData_ofFormat(v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3692_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v_msg_3691_);
v___x_3694_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_3696_, lean_object* v_inst_3697_, lean_object* v_msg_3698_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = lean_apply_1(v_inst_3696_, v_msg_3698_);
v___x_3700_ = lean_apply_2(v_inst_3697_, lean_box(0), v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_3701_, lean_object* v_inst_3702_){
_start:
{
lean_object* v___f_3703_; 
v___f_3703_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3703_, 0, v_inst_3702_);
lean_closure_set(v___f_3703_, 1, v_inst_3701_);
return v___f_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_3704_, lean_object* v_n_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_){
_start:
{
lean_object* v___f_3708_; 
v___f_3708_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3708_, 0, v_inst_3707_);
lean_closure_set(v___f_3708_, 1, v_inst_3706_);
return v___f_3708_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(32u);
v___x_3710_ = lean_mk_empty_array_with_capacity(v___x_3709_);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3712_ = ((size_t)5ULL);
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_unsigned_to_nat(32u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
v___x_3716_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_3717_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___x_3715_);
lean_ctor_set(v___x_3717_, 2, v___x_3713_);
lean_ctor_set(v___x_3717_, 3, v___x_3713_);
lean_ctor_set_usize(v___x_3717_, 4, v___x_3712_);
return v___x_3717_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_box(1);
v___x_3719_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_3720_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_3721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v___x_3719_);
lean_ctor_set(v___x_3721_, 2, v___x_3718_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_3722_, lean_object* v_msgData_3723_, lean_object* v_toPure_3724_, lean_object* v_opts_3725_){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3726_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_3727_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_3728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3728_, 0, v_env_3722_);
lean_ctor_set(v___x_3728_, 1, v___x_3726_);
lean_ctor_set(v___x_3728_, 2, v___x_3727_);
lean_ctor_set(v___x_3728_, 3, v_opts_3725_);
v___x_3729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set(v___x_3729_, 1, v_msgData_3723_);
v___x_3730_ = lean_apply_2(v_toPure_3724_, lean_box(0), v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_3731_, lean_object* v_toPure_3732_, lean_object* v_toBind_3733_, lean_object* v_inst_3734_, lean_object* v_env_3735_){
_start:
{
lean_object* v___f_3736_; lean_object* v___x_3737_; 
v___f_3736_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3736_, 0, v_env_3735_);
lean_closure_set(v___f_3736_, 1, v_msgData_3731_);
lean_closure_set(v___f_3736_, 2, v_toPure_3732_);
v___x_3737_ = lean_apply_4(v_toBind_3733_, lean_box(0), lean_box(0), v_inst_3734_, v___f_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_3738_, lean_object* v_inst_3739_, lean_object* v_inst_3740_, lean_object* v_msgData_3741_){
_start:
{
lean_object* v_toApplicative_3742_; lean_object* v_toBind_3743_; lean_object* v_getEnv_3744_; lean_object* v_toPure_3745_; lean_object* v___f_3746_; lean_object* v___x_3747_; 
v_toApplicative_3742_ = lean_ctor_get(v_inst_3738_, 0);
lean_inc_ref(v_toApplicative_3742_);
v_toBind_3743_ = lean_ctor_get(v_inst_3738_, 1);
lean_inc_n(v_toBind_3743_, 2);
lean_dec_ref(v_inst_3738_);
v_getEnv_3744_ = lean_ctor_get(v_inst_3739_, 0);
lean_inc(v_getEnv_3744_);
lean_dec_ref(v_inst_3739_);
v_toPure_3745_ = lean_ctor_get(v_toApplicative_3742_, 1);
lean_inc(v_toPure_3745_);
lean_dec_ref(v_toApplicative_3742_);
v___f_3746_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3746_, 0, v_msgData_3741_);
lean_closure_set(v___f_3746_, 1, v_toPure_3745_);
lean_closure_set(v___f_3746_, 2, v_toBind_3743_);
lean_closure_set(v___f_3746_, 3, v_inst_3740_);
v___x_3747_ = lean_apply_4(v_toBind_3743_, lean_box(0), lean_box(0), v_getEnv_3744_, v___f_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_3748_, lean_object* v_inst_3749_, lean_object* v_inst_3750_, lean_object* v_inst_3751_, lean_object* v_msgData_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_addMessageContextPartial___redArg(v_inst_3749_, v_inst_3750_, v_inst_3751_, v_msgData_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_3754_, lean_object* v_mctx_3755_, lean_object* v_lctx_3756_, lean_object* v_msgData_3757_, lean_object* v_toPure_3758_, lean_object* v_opts_3759_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3760_, 0, v_env_3754_);
lean_ctor_set(v___x_3760_, 1, v_mctx_3755_);
lean_ctor_set(v___x_3760_, 2, v_lctx_3756_);
lean_ctor_set(v___x_3760_, 3, v_opts_3759_);
v___x_3761_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v_msgData_3757_);
v___x_3762_ = lean_apply_2(v_toPure_3758_, lean_box(0), v___x_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_3763_, lean_object* v_mctx_3764_, lean_object* v_msgData_3765_, lean_object* v_toPure_3766_, lean_object* v_toBind_3767_, lean_object* v_inst_3768_, lean_object* v_lctx_3769_){
_start:
{
lean_object* v___f_3770_; lean_object* v___x_3771_; 
v___f_3770_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3770_, 0, v_env_3763_);
lean_closure_set(v___f_3770_, 1, v_mctx_3764_);
lean_closure_set(v___f_3770_, 2, v_lctx_3769_);
lean_closure_set(v___f_3770_, 3, v_msgData_3765_);
lean_closure_set(v___f_3770_, 4, v_toPure_3766_);
v___x_3771_ = lean_apply_4(v_toBind_3767_, lean_box(0), lean_box(0), v_inst_3768_, v___f_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_3772_, lean_object* v_msgData_3773_, lean_object* v_toPure_3774_, lean_object* v_toBind_3775_, lean_object* v_inst_3776_, lean_object* v_inst_3777_, lean_object* v_mctx_3778_){
_start:
{
lean_object* v___f_3779_; lean_object* v___x_3780_; 
lean_inc(v_toBind_3775_);
v___f_3779_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3779_, 0, v_env_3772_);
lean_closure_set(v___f_3779_, 1, v_mctx_3778_);
lean_closure_set(v___f_3779_, 2, v_msgData_3773_);
lean_closure_set(v___f_3779_, 3, v_toPure_3774_);
lean_closure_set(v___f_3779_, 4, v_toBind_3775_);
lean_closure_set(v___f_3779_, 5, v_inst_3776_);
v___x_3780_ = lean_apply_4(v_toBind_3775_, lean_box(0), lean_box(0), v_inst_3777_, v___f_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_3781_, lean_object* v_msgData_3782_, lean_object* v_toPure_3783_, lean_object* v_toBind_3784_, lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_env_3787_){
_start:
{
lean_object* v_getMCtx_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; 
v_getMCtx_3788_ = lean_ctor_get(v_inst_3781_, 0);
lean_inc(v_getMCtx_3788_);
lean_dec_ref(v_inst_3781_);
lean_inc(v_toBind_3784_);
v___f_3789_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3789_, 0, v_env_3787_);
lean_closure_set(v___f_3789_, 1, v_msgData_3782_);
lean_closure_set(v___f_3789_, 2, v_toPure_3783_);
lean_closure_set(v___f_3789_, 3, v_toBind_3784_);
lean_closure_set(v___f_3789_, 4, v_inst_3785_);
lean_closure_set(v___f_3789_, 5, v_inst_3786_);
v___x_3790_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v_getMCtx_3788_, v___f_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_3791_, lean_object* v_inst_3792_, lean_object* v_inst_3793_, lean_object* v_inst_3794_, lean_object* v_inst_3795_, lean_object* v_msgData_3796_){
_start:
{
lean_object* v_toApplicative_3797_; lean_object* v_toBind_3798_; lean_object* v_getEnv_3799_; lean_object* v_toPure_3800_; lean_object* v___f_3801_; lean_object* v___x_3802_; 
v_toApplicative_3797_ = lean_ctor_get(v_inst_3791_, 0);
lean_inc_ref(v_toApplicative_3797_);
v_toBind_3798_ = lean_ctor_get(v_inst_3791_, 1);
lean_inc_n(v_toBind_3798_, 2);
lean_dec_ref(v_inst_3791_);
v_getEnv_3799_ = lean_ctor_get(v_inst_3792_, 0);
lean_inc(v_getEnv_3799_);
lean_dec_ref(v_inst_3792_);
v_toPure_3800_ = lean_ctor_get(v_toApplicative_3797_, 1);
lean_inc(v_toPure_3800_);
lean_dec_ref(v_toApplicative_3797_);
v___f_3801_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_3801_, 0, v_inst_3793_);
lean_closure_set(v___f_3801_, 1, v_msgData_3796_);
lean_closure_set(v___f_3801_, 2, v_toPure_3800_);
lean_closure_set(v___f_3801_, 3, v_toBind_3798_);
lean_closure_set(v___f_3801_, 4, v_inst_3795_);
lean_closure_set(v___f_3801_, 5, v_inst_3794_);
v___x_3802_ = lean_apply_4(v_toBind_3798_, lean_box(0), lean_box(0), v_getEnv_3799_, v___f_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_3803_, lean_object* v_inst_3804_, lean_object* v_inst_3805_, lean_object* v_inst_3806_, lean_object* v_inst_3807_, lean_object* v_inst_3808_, lean_object* v_msgData_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_addMessageContextFull___redArg(v_inst_3804_, v_inst_3805_, v_inst_3806_, v_inst_3807_, v_inst_3808_, v_msgData_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_3813_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_3815_);
lean_dec_ref(v_s_3815_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_a_3820_, lean_object* v_b_3821_){
_start:
{
lean_object* v_it_3823_; lean_object* v_startInclusive_3824_; lean_object* v_endExclusive_3825_; 
if (lean_obj_tag(v_a_3820_) == 0)
{
lean_object* v_currPos_3831_; lean_object* v_searcher_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3858_; 
v_currPos_3831_ = lean_ctor_get(v_a_3820_, 0);
v_searcher_3832_ = lean_ctor_get(v_a_3820_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3820_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3834_ = v_a_3820_;
v_isShared_3835_ = v_isSharedCheck_3858_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_searcher_3832_);
lean_inc(v_currPos_3831_);
lean_dec(v_a_3820_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3858_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_startInclusive_3836_; lean_object* v_endExclusive_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_startInclusive_3836_ = lean_ctor_get(v___x_3818_, 1);
v_endExclusive_3837_ = lean_ctor_get(v___x_3818_, 2);
v___x_3838_ = lean_nat_sub(v_endExclusive_3837_, v_startInclusive_3836_);
v___x_3839_ = lean_nat_dec_eq(v_searcher_3832_, v___x_3838_);
lean_dec(v___x_3838_);
if (v___x_3839_ == 0)
{
uint32_t v___x_3840_; uint32_t v___x_3841_; uint8_t v___x_3842_; 
v___x_3840_ = 10;
v___x_3841_ = lean_string_utf8_get_fast(v_str_3817_, v_searcher_3832_);
v___x_3842_ = lean_uint32_dec_eq(v___x_3841_, v___x_3840_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_string_utf8_next_fast(v_str_3817_, v_searcher_3832_);
lean_dec(v_searcher_3832_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3843_);
v___x_3845_ = v___x_3834_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_currPos_3831_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
v_a_3820_ = v___x_3845_;
goto _start;
}
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v_slice_3851_; lean_object* v_nextIt_3853_; 
v___x_3848_ = lean_string_utf8_next_fast(v_str_3817_, v_searcher_3832_);
v___x_3849_ = lean_nat_sub(v___x_3848_, v_searcher_3832_);
v___x_3850_ = lean_nat_add(v_searcher_3832_, v___x_3849_);
lean_dec(v___x_3849_);
v_slice_3851_ = l_String_Slice_subslice_x21(v___x_3818_, v_currPos_3831_, v_searcher_3832_);
lean_inc(v___x_3850_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3850_);
lean_ctor_set(v___x_3834_, 0, v___x_3850_);
v_nextIt_3853_ = v___x_3834_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v___x_3850_);
v_nextIt_3853_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v_startInclusive_3854_; lean_object* v_endExclusive_3855_; 
v_startInclusive_3854_ = lean_ctor_get(v_slice_3851_, 0);
lean_inc(v_startInclusive_3854_);
v_endExclusive_3855_ = lean_ctor_get(v_slice_3851_, 1);
lean_inc(v_endExclusive_3855_);
lean_dec_ref(v_slice_3851_);
v_it_3823_ = v_nextIt_3853_;
v_startInclusive_3824_ = v_startInclusive_3854_;
v_endExclusive_3825_ = v_endExclusive_3855_;
goto v___jp_3822_;
}
}
}
else
{
lean_object* v___x_3857_; 
lean_del_object(v___x_3834_);
lean_dec(v_searcher_3832_);
v___x_3857_ = lean_box(1);
lean_inc(v___x_3819_);
v_it_3823_ = v___x_3857_;
v_startInclusive_3824_ = v_currPos_3831_;
v_endExclusive_3825_ = v___x_3819_;
goto v___jp_3822_;
}
}
}
else
{
lean_dec(v___x_3819_);
return v_b_3821_;
}
v___jp_3822_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3826_ = lean_string_utf8_extract(v_str_3817_, v_startInclusive_3824_, v_endExclusive_3825_);
lean_dec(v_endExclusive_3825_);
lean_dec(v_startInclusive_3824_);
v___x_3827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
v___x_3828_ = l_Lean_MessageData_ofFormat(v___x_3827_);
v___x_3829_ = lean_array_push(v_b_3821_, v___x_3828_);
v_a_3820_ = v_it_3823_;
v_b_3821_ = v___x_3829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_3859_, lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v_a_3862_, lean_object* v_b_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3859_, v___x_3860_, v___x_3861_, v_a_3862_, v_b_3863_);
lean_dec_ref(v___x_3860_);
lean_dec_ref(v_str_3859_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_3867_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v_lines_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = lean_string_utf8_byte_size(v_str_3867_);
lean_inc_ref(v_str_3867_);
v___x_3870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3870_, 0, v_str_3867_);
lean_ctor_set(v___x_3870_, 1, v___x_3868_);
lean_ctor_set(v___x_3870_, 2, v___x_3869_);
v_lines_3871_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_3870_);
v___x_3872_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_3873_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3867_, v___x_3870_, v___x_3869_, v_lines_3871_, v___x_3872_);
lean_dec_ref(v___x_3870_);
lean_dec_ref(v_str_3867_);
v___x_3874_ = lean_array_to_list(v___x_3873_);
v___x_3875_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3876_ = l_Lean_MessageData_joinSep(v___x_3874_, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_3877_, lean_object* v___x_3878_, lean_object* v___x_3879_, lean_object* v_inst_3880_, lean_object* v_R_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3877_, v___x_3878_, v___x_3879_, v_a_3882_, v_b_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_3885_, lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v_inst_3888_, lean_object* v_R_3889_, lean_object* v_a_3890_, lean_object* v_b_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_3885_, v___x_3886_, v___x_3887_, v_inst_3888_, v_R_3889_, v_a_3890_, v_b_3891_);
lean_dec_ref(v___x_3886_);
lean_dec_ref(v_str_3885_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_3893_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_3895_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_3895_, 0, lean_box(0));
lean_closure_set(v___x_3895_, 1, lean_box(0));
lean_closure_set(v___x_3895_, 2, lean_box(0));
lean_closure_set(v___x_3895_, 3, v___x_3894_);
lean_closure_set(v___x_3895_, 4, v_inst_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_3896_, lean_object* v_inst_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_3905_){
_start:
{
lean_object* v___f_3906_; 
v___f_3906_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_instToMessageDataTSyntax(v_k_3907_);
lean_dec(v_k_3907_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_3913_, lean_object* v_as_3914_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3915_ = lean_box(0);
v___x_3916_ = l_List_mapTR_loop___redArg(v_inst_3913_, v_as_3914_, v___x_3915_);
v___x_3917_ = l_Lean_MessageData_ofList(v___x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_3918_){
_start:
{
lean_object* v___f_3919_; 
v___f_3919_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3919_, 0, v_inst_3918_);
return v___f_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_3920_, lean_object* v_inst_3921_){
_start:
{
lean_object* v___f_3922_; 
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3922_, 0, v_inst_3921_);
return v___f_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_3923_, lean_object* v_as_3924_){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3925_ = lean_array_to_list(v_as_3924_);
v___x_3926_ = lean_box(0);
v___x_3927_ = l_List_mapTR_loop___redArg(v_inst_3923_, v___x_3925_, v___x_3926_);
v___x_3928_ = l_Lean_MessageData_ofList(v___x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_3929_){
_start:
{
lean_object* v___f_3930_; 
v___f_3930_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3930_, 0, v_inst_3929_);
return v___f_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_3931_, lean_object* v_inst_3932_){
_start:
{
lean_object* v___f_3933_; 
v___f_3933_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3933_, 0, v_inst_3932_);
return v___f_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_3934_, lean_object* v_acc_3935_, lean_object* v_recur_3936_){
_start:
{
lean_object* v_array_3937_; lean_object* v_start_3938_; lean_object* v_stop_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3952_; 
v_array_3937_ = lean_ctor_get(v_it_3934_, 0);
v_start_3938_ = lean_ctor_get(v_it_3934_, 1);
v_stop_3939_ = lean_ctor_get(v_it_3934_, 2);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_it_3934_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3941_ = v_it_3934_;
v_isShared_3942_ = v_isSharedCheck_3952_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_stop_3939_);
lean_inc(v_start_3938_);
lean_inc(v_array_3937_);
lean_dec(v_it_3934_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3952_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
uint8_t v___x_3943_; 
v___x_3943_ = lean_nat_dec_lt(v_start_3938_, v_stop_3939_);
if (v___x_3943_ == 0)
{
lean_del_object(v___x_3941_);
lean_dec(v_stop_3939_);
lean_dec(v_start_3938_);
lean_dec_ref(v_array_3937_);
lean_dec_ref(v_recur_3936_);
return v_acc_3935_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = lean_nat_add(v_start_3938_, v___x_3944_);
lean_inc_ref(v_array_3937_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v___x_3945_);
v___x_3947_ = v___x_3941_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_array_3937_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v_stop_3939_);
v___x_3947_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = lean_array_fget(v_array_3937_, v_start_3938_);
lean_dec(v_start_3938_);
lean_dec_ref(v_array_3937_);
v___x_3949_ = lean_array_push(v_acc_3935_, v___x_3948_);
v___x_3950_ = lean_apply_3(v_recur_3936_, v___x_3947_, v___x_3949_, lean_box(0));
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_3955_, lean_object* v_inst_3956_, lean_object* v_as_3957_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3958_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_3959_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_3955_, v_as_3957_, v___x_3958_);
v___x_3960_ = lean_array_to_list(v___x_3959_);
v___x_3961_ = lean_box(0);
v___x_3962_ = l_List_mapTR_loop___redArg(v_inst_3956_, v___x_3960_, v___x_3961_);
v___x_3963_ = l_Lean_MessageData_ofList(v___x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_3965_){
_start:
{
lean_object* v___f_3966_; lean_object* v___f_3967_; 
v___f_3966_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3967_, 0, v___f_3966_);
lean_closure_set(v___f_3967_, 1, v_inst_3965_);
return v___f_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_3968_, lean_object* v_inst_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_3969_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_3975_ = l_Lean_MessageData_ofFormat(v___x_3974_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_3979_ = l_Lean_MessageData_ofFormat(v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_3980_, lean_object* v_x_3981_){
_start:
{
if (lean_obj_tag(v_x_3981_) == 0)
{
lean_object* v___x_3982_; 
lean_dec_ref(v_inst_3980_);
v___x_3982_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_3982_;
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_val_3983_ = lean_ctor_get(v_x_3981_, 0);
lean_inc(v_val_3983_);
lean_dec_ref(v_x_3981_);
v___x_3984_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_3985_ = lean_apply_1(v_inst_3980_, v_val_3983_);
v___x_3986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_3989_){
_start:
{
lean_object* v___f_3990_; 
v___f_3990_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3990_, 0, v_inst_3989_);
return v___f_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_3991_, lean_object* v_inst_3992_){
_start:
{
lean_object* v___f_3993_; 
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3993_, 0, v_inst_3992_);
return v___f_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_3994_, lean_object* v_inst_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v_fst_3997_; lean_object* v_snd_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4012_; 
v_fst_3997_ = lean_ctor_get(v_x_3996_, 0);
v_snd_3998_ = lean_ctor_get(v_x_3996_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_x_3996_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4000_ = v_x_3996_;
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_snd_3998_);
lean_inc(v_fst_3997_);
lean_dec(v_x_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_4002_ = lean_apply_1(v_inst_3994_, v_fst_3997_);
v___x_4003_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4001_ == 0)
{
lean_ctor_set_tag(v___x_4000_, 7);
lean_ctor_set(v___x_4000_, 1, v___x_4003_);
lean_ctor_set(v___x_4000_, 0, v___x_4002_);
v___x_4005_ = v___x_4000_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4006_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = lean_apply_1(v_inst_3995_, v_snd_3998_);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = l_Lean_MessageData_paren(v___x_4009_);
return v___x_4010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4013_, lean_object* v_inst_4014_){
_start:
{
lean_object* v___f_4015_; 
v___f_4015_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4015_, 0, v_inst_4013_);
lean_closure_set(v___f_4015_, 1, v_inst_4014_);
return v___f_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4016_, lean_object* v_00_u03b2_4017_, lean_object* v_inst_4018_, lean_object* v_inst_4019_){
_start:
{
lean_object* v___f_4020_; 
v___f_4020_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4020_, 0, v_inst_4018_);
lean_closure_set(v___f_4020_, 1, v_inst_4019_);
return v___f_4020_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4025_ = l_Lean_MessageData_ofFormat(v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4026_){
_start:
{
if (lean_obj_tag(v_x_4026_) == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4027_;
}
else
{
lean_object* v_val_4028_; lean_object* v___x_4029_; 
v_val_4028_ = lean_ctor_get(v_x_4026_, 0);
lean_inc(v_val_4028_);
lean_dec_ref(v_x_4026_);
v___x_4029_ = l_Lean_MessageData_ofExpr(v_val_4028_);
return v___x_4029_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
v___x_4064_ = l_String_toRawSubstring_x27(v___x_4063_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4080_ = l_String_toRawSubstring_x27(v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___x_4097_; uint8_t v___x_4098_; 
v___x_4097_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4094_);
v___x_4098_ = l_Lean_Syntax_isOfKind(v_x_4094_, v___x_4097_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_dec(v_x_4094_);
v___x_4099_ = lean_box(1);
v___x_4100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v_a_4096_);
return v___x_4100_;
}
else
{
lean_object* v_quotContext_4101_; lean_object* v_currMacroScope_4102_; lean_object* v_ref_4103_; lean_object* v___x_4104_; lean_object* v_interpStr_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_quotContext_4101_ = lean_ctor_get(v_a_4095_, 1);
v_currMacroScope_4102_ = lean_ctor_get(v_a_4095_, 2);
v_ref_4103_ = lean_ctor_get(v_a_4095_, 5);
v___x_4104_ = lean_unsigned_to_nat(1u);
v_interpStr_4105_ = l_Lean_Syntax_getArg(v_x_4094_, v___x_4104_);
lean_dec(v_x_4094_);
v___x_4106_ = 0;
v___x_4107_ = l_Lean_SourceInfo_fromRef(v_ref_4103_, v___x_4106_);
v___x_4108_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4109_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4102_, 2);
lean_inc_n(v_quotContext_4101_, 2);
v___x_4110_ = l_Lean_addMacroScope(v_quotContext_4101_, v___x_4109_, v_currMacroScope_4102_);
v___x_4111_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4107_);
v___x_4112_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4107_);
lean_ctor_set(v___x_4112_, 1, v___x_4108_);
lean_ctor_set(v___x_4112_, 2, v___x_4110_);
lean_ctor_set(v___x_4112_, 3, v___x_4111_);
v___x_4113_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4114_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4115_ = l_Lean_addMacroScope(v_quotContext_4101_, v___x_4114_, v_currMacroScope_4102_);
v___x_4116_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4107_);
lean_ctor_set(v___x_4117_, 1, v___x_4113_);
lean_ctor_set(v___x_4117_, 2, v___x_4115_);
lean_ctor_set(v___x_4117_, 3, v___x_4116_);
lean_inc_ref(v___x_4117_);
v___x_4118_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4105_, v___x_4112_, v___x_4117_, v___x_4117_, v_a_4095_, v_a_4096_);
lean_dec(v_interpStr_4105_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_a_4120_ = lean_ctor_get(v___x_4118_, 1);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4118_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4119_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4128_ = lean_ctor_get(v___x_4118_, 0);
v_a_4129_ = lean_ctor_get(v___x_4118_, 1);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4118_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_inc(v_a_4128_);
lean_dec(v___x_4118_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4128_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4137_, v_a_4138_, v_a_4139_);
lean_dec_ref(v_a_4138_);
return v_res_4140_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4143_ = l_Lean_stringToMessageData(v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4144_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4145_ = lean_array_to_list(v_msgs_4144_);
v___x_4146_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4147_ = l_Lean_MessageData_joinSep(v___x_4145_, v___x_4146_);
v___x_4148_ = l_Lean_indentD(v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4149_, lean_object* v_lctx_4150_, lean_object* v_opts_4151_, lean_object* v_msg_4152_){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = lean_elab_environment_of_kernel_env(v_env_4149_);
v___x_4154_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
lean_ctor_set(v___x_4155_, 2, v_lctx_4150_);
lean_ctor_set(v___x_4155_, 3, v_opts_4151_);
v___x_4156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v_msg_4152_);
return v___x_4156_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4159_ = l_Lean_stringToMessageData(v___x_4158_);
return v___x_4159_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4162_ = l_Lean_stringToMessageData(v___x_4161_);
return v___x_4162_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4164_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4165_ = l_Lean_stringToMessageData(v___x_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4166_, lean_object* v_n_4167_, lean_object* v_expectedType_4168_){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4169_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4170_ = l_Lean_MessageData_ofName(v_n_4167_);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4171_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = l_Lean_indentExpr(v_givenType_4166_);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_indentExpr(v_expectedType_4168_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4183_ = lean_box(1);
v___x_4184_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4185_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4184_);
lean_ctor_set(v___x_4186_, 2, v___x_4183_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4189_ = l_Lean_stringToMessageData(v___x_4188_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4192_ = l_Lean_stringToMessageData(v___x_4191_);
return v___x_4192_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4195_ = l_Lean_stringToMessageData(v___x_4194_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4200_ = l_Lean_MessageData_ofFormat(v___x_4199_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4206_ = l_Lean_stringToMessageData(v___x_4205_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4209_ = l_Lean_stringToMessageData(v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4212_ = l_Lean_stringToMessageData(v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4215_ = l_Lean_stringToMessageData(v___x_4214_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4218_ = l_Lean_stringToMessageData(v___x_4217_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4221_ = l_Lean_stringToMessageData(v___x_4220_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4224_ = l_Lean_stringToMessageData(v___x_4223_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4233_ = l_Lean_stringToMessageData(v___x_4232_);
return v___x_4233_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4236_ = l_Lean_stringToMessageData(v___x_4235_);
return v___x_4236_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4238_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4239_ = l_Lean_stringToMessageData(v___x_4238_);
return v___x_4239_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4242_ = l_Lean_stringToMessageData(v___x_4241_);
return v___x_4242_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4247_ = l_Lean_MessageData_ofFormat(v___x_4246_);
return v___x_4247_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4252_ = l_Lean_MessageData_ofFormat(v___x_4251_);
return v___x_4252_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4257_ = l_Lean_MessageData_ofFormat(v___x_4256_);
return v___x_4257_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4262_ = l_Lean_MessageData_ofFormat(v___x_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4263_, lean_object* v_opts_4264_){
_start:
{
switch(lean_obj_tag(v_e_4263_))
{
case 0:
{
lean_object* v_env_4265_; lean_object* v_name_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4279_; 
v_env_4265_ = lean_ctor_get(v_e_4263_, 0);
v_name_4266_ = lean_ctor_get(v_e_4263_, 1);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_e_4263_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4268_ = v_e_4263_;
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_name_4266_);
lean_inc(v_env_4265_);
lean_dec(v_e_4263_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4270_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4271_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4272_ = l_Lean_MessageData_ofName(v_name_4266_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set_tag(v___x_4268_, 7);
lean_ctor_set(v___x_4268_, 1, v___x_4272_);
lean_ctor_set(v___x_4268_, 0, v___x_4271_);
v___x_4274_ = v___x_4268_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4271_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4265_, v___x_4270_, v_opts_4264_, v___x_4276_);
return v___x_4277_;
}
}
}
case 1:
{
lean_object* v_env_4280_; lean_object* v_name_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4295_; 
v_env_4280_ = lean_ctor_get(v_e_4263_, 0);
v_name_4281_ = lean_ctor_get(v_e_4263_, 1);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_e_4263_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4283_ = v_e_4263_;
v_isShared_4284_ = v_isSharedCheck_4295_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_name_4281_);
lean_inc(v_env_4280_);
lean_dec(v_e_4263_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4295_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4285_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4286_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4287_ = 1;
v___x_4288_ = l_Lean_MessageData_ofConstName(v_name_4281_, v___x_4287_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 7);
lean_ctor_set(v___x_4283_, 1, v___x_4288_);
lean_ctor_set(v___x_4283_, 0, v___x_4286_);
v___x_4290_ = v___x_4283_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4280_, v___x_4285_, v_opts_4264_, v___x_4292_);
return v___x_4293_;
}
}
}
case 2:
{
lean_object* v_env_4296_; lean_object* v_decl_4297_; lean_object* v_givenType_4298_; lean_object* v___x_4299_; 
v_env_4296_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4296_);
v_decl_4297_ = lean_ctor_get(v_e_4263_, 1);
lean_inc(v_decl_4297_);
v_givenType_4298_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_givenType_4298_);
lean_dec_ref(v_e_4263_);
v___x_4299_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4297_))
{
case 1:
{
lean_object* v_val_4300_; lean_object* v_toConstantVal_4301_; lean_object* v_name_4302_; lean_object* v_type_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_val_4300_ = lean_ctor_get(v_decl_4297_, 0);
lean_inc_ref(v_val_4300_);
lean_dec_ref(v_decl_4297_);
v_toConstantVal_4301_ = lean_ctor_get(v_val_4300_, 0);
lean_inc_ref(v_toConstantVal_4301_);
lean_dec_ref(v_val_4300_);
v_name_4302_ = lean_ctor_get(v_toConstantVal_4301_, 0);
lean_inc(v_name_4302_);
v_type_4303_ = lean_ctor_get(v_toConstantVal_4301_, 2);
lean_inc_ref(v_type_4303_);
lean_dec_ref(v_toConstantVal_4301_);
v___x_4304_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4298_, v_name_4302_, v_type_4303_);
v___x_4305_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4296_, v___x_4299_, v_opts_4264_, v___x_4304_);
return v___x_4305_;
}
case 2:
{
lean_object* v_val_4306_; lean_object* v_toConstantVal_4307_; lean_object* v_name_4308_; lean_object* v_type_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_val_4306_ = lean_ctor_get(v_decl_4297_, 0);
lean_inc_ref(v_val_4306_);
lean_dec_ref(v_decl_4297_);
v_toConstantVal_4307_ = lean_ctor_get(v_val_4306_, 0);
lean_inc_ref(v_toConstantVal_4307_);
lean_dec_ref(v_val_4306_);
v_name_4308_ = lean_ctor_get(v_toConstantVal_4307_, 0);
lean_inc(v_name_4308_);
v_type_4309_ = lean_ctor_get(v_toConstantVal_4307_, 2);
lean_inc_ref(v_type_4309_);
lean_dec_ref(v_toConstantVal_4307_);
v___x_4310_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4298_, v_name_4308_, v_type_4309_);
v___x_4311_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4296_, v___x_4299_, v_opts_4264_, v___x_4310_);
return v___x_4311_;
}
default: 
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
lean_dec_ref(v_givenType_4298_);
lean_dec(v_decl_4297_);
v___x_4312_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4313_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4296_, v___x_4299_, v_opts_4264_, v___x_4312_);
return v___x_4313_;
}
}
}
case 3:
{
lean_object* v_env_4314_; lean_object* v_name_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_env_4314_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4314_);
v_name_4315_ = lean_ctor_get(v_e_4263_, 1);
lean_inc(v_name_4315_);
lean_dec_ref(v_e_4263_);
v___x_4316_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4317_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4318_ = 1;
v___x_4319_ = l_Lean_MessageData_ofConstName(v_name_4315_, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4317_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4320_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4314_, v___x_4316_, v_opts_4264_, v___x_4322_);
return v___x_4323_;
}
case 4:
{
lean_object* v_env_4324_; lean_object* v_name_4325_; lean_object* v_expr_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_env_4324_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4324_);
v_name_4325_ = lean_ctor_get(v_e_4263_, 1);
lean_inc(v_name_4325_);
v_expr_4326_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_expr_4326_);
lean_dec_ref(v_e_4263_);
v___x_4327_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4328_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4329_ = 1;
v___x_4330_ = l_Lean_MessageData_ofConstName(v_name_4325_, v___x_4329_);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4328_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = l_Lean_indentExpr(v_expr_4326_);
v___x_4335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4333_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
v___x_4336_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4324_, v___x_4327_, v_opts_4264_, v___x_4335_);
return v___x_4336_;
}
case 5:
{
lean_object* v_env_4337_; lean_object* v_lctx_4338_; lean_object* v_expr_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v_env_4337_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4337_);
v_lctx_4338_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4338_);
v_expr_4339_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_expr_4339_);
lean_dec_ref(v_e_4263_);
v___x_4340_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4341_ = l_Lean_indentExpr(v_expr_4339_);
v___x_4342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4340_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4337_, v_lctx_4338_, v_opts_4264_, v___x_4342_);
return v___x_4343_;
}
case 6:
{
lean_object* v_env_4344_; lean_object* v_lctx_4345_; lean_object* v_expr_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_env_4344_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4344_);
v_lctx_4345_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4345_);
v_expr_4346_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_expr_4346_);
lean_dec_ref(v_e_4263_);
v___x_4347_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4348_ = l_Lean_indentExpr(v_expr_4346_);
v___x_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4344_, v_lctx_4345_, v_opts_4264_, v___x_4349_);
return v___x_4350_;
}
case 7:
{
lean_object* v_env_4351_; lean_object* v_lctx_4352_; lean_object* v_name_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_env_4351_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4351_);
v_lctx_4352_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4352_);
v_name_4353_ = lean_ctor_get(v_e_4263_, 2);
lean_inc(v_name_4353_);
lean_dec_ref(v_e_4263_);
v___x_4354_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4355_ = l_Lean_MessageData_ofName(v_name_4353_);
v___x_4356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4356_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4351_, v_lctx_4352_, v_opts_4264_, v___x_4358_);
return v___x_4359_;
}
case 8:
{
lean_object* v_env_4360_; lean_object* v_lctx_4361_; lean_object* v_expr_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v_env_4360_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4360_);
v_lctx_4361_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4361_);
v_expr_4362_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_expr_4362_);
lean_dec_ref(v_e_4263_);
v___x_4363_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4364_ = l_Lean_indentExpr(v_expr_4362_);
v___x_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4360_, v_lctx_4361_, v_opts_4264_, v___x_4365_);
return v___x_4366_;
}
case 9:
{
lean_object* v_env_4367_; lean_object* v_lctx_4368_; lean_object* v_app_4369_; lean_object* v_funType_4370_; lean_object* v_argType_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_env_4367_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4367_);
v_lctx_4368_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4368_);
v_app_4369_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_app_4369_);
v_funType_4370_ = lean_ctor_get(v_e_4263_, 3);
lean_inc_ref(v_funType_4370_);
v_argType_4371_ = lean_ctor_get(v_e_4263_, 4);
lean_inc_ref(v_argType_4371_);
lean_dec_ref(v_e_4263_);
v___x_4372_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4373_ = l_Lean_indentExpr(v_app_4369_);
v___x_4374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = l_Lean_indentExpr(v_argType_4371_);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4378_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = l_Lean_indentExpr(v_funType_4370_);
v___x_4382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4380_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4367_, v_lctx_4368_, v_opts_4264_, v___x_4382_);
return v___x_4383_;
}
case 10:
{
lean_object* v_env_4384_; lean_object* v_lctx_4385_; lean_object* v_proj_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v_env_4384_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4384_);
v_lctx_4385_ = lean_ctor_get(v_e_4263_, 1);
lean_inc_ref(v_lctx_4385_);
v_proj_4386_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_proj_4386_);
lean_dec_ref(v_e_4263_);
v___x_4387_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4388_ = l_Lean_indentExpr(v_proj_4386_);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4384_, v_lctx_4385_, v_opts_4264_, v___x_4389_);
return v___x_4390_;
}
case 11:
{
lean_object* v_env_4391_; lean_object* v_name_4392_; lean_object* v_type_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_env_4391_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_env_4391_);
v_name_4392_ = lean_ctor_get(v_e_4263_, 1);
lean_inc(v_name_4392_);
v_type_4393_ = lean_ctor_get(v_e_4263_, 2);
lean_inc_ref(v_type_4393_);
lean_dec_ref(v_e_4263_);
v___x_4394_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4395_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4396_ = 1;
v___x_4397_ = l_Lean_MessageData_ofConstName(v_name_4392_, v___x_4396_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4395_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = l_Lean_indentExpr(v_type_4393_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4400_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4391_, v___x_4394_, v_opts_4264_, v___x_4402_);
return v___x_4403_;
}
case 12:
{
lean_object* v_msg_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_dec_ref(v_opts_4264_);
v_msg_4404_ = lean_ctor_get(v_e_4263_, 0);
lean_inc_ref(v_msg_4404_);
lean_dec_ref(v_e_4263_);
v___x_4405_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4406_ = l_Lean_stringToMessageData(v_msg_4404_);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4405_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
return v___x_4407_;
}
case 13:
{
lean_object* v___x_4408_; 
lean_dec_ref(v_opts_4264_);
v___x_4408_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4408_;
}
case 14:
{
lean_object* v___x_4409_; 
lean_dec_ref(v_opts_4264_);
v___x_4409_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4409_;
}
case 15:
{
lean_object* v___x_4410_; 
lean_dec_ref(v_opts_4264_);
v___x_4410_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4410_;
}
default: 
{
lean_object* v___x_4411_; 
lean_dec_ref(v_opts_4264_);
v___x_4411_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4412_, lean_object* v_e_4413_, lean_object* v_cls_4414_){
_start:
{
lean_object* v___x_4415_; double v___x_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4415_ = lean_box(0);
v___x_4416_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4417_ = 1;
v___x_4418_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4419_, 0, v_cls_4414_);
lean_ctor_set(v___x_4419_, 1, v___x_4415_);
lean_ctor_set(v___x_4419_, 2, v___x_4418_);
lean_ctor_set_float(v___x_4419_, sizeof(void*)*3, v___x_4416_);
lean_ctor_set_float(v___x_4419_, sizeof(void*)*3 + 8, v___x_4416_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*3 + 16, v___x_4417_);
v___x_4420_ = lean_apply_1(v_inst_4412_, v_e_4413_);
v___x_4421_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4422_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4419_);
lean_ctor_set(v___x_4422_, 1, v___x_4420_);
lean_ctor_set(v___x_4422_, 2, v___x_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4423_, lean_object* v_inst_4424_, lean_object* v_e_4425_, lean_object* v_cls_4426_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_toTraceElem___redArg(v_inst_4424_, v_e_4425_, v_cls_4426_);
return v___x_4427_;
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
l_Lean_instInhabitedMessageData_default = _init_l_Lean_instInhabitedMessageData_default();
lean_mark_persistent(l_Lean_instInhabitedMessageData_default);
l_Lean_instInhabitedMessageData = _init_l_Lean_instInhabitedMessageData();
lean_mark_persistent(l_Lean_instInhabitedMessageData);
l_Lean_MessageData_nil = _init_l_Lean_MessageData_nil();
lean_mark_persistent(l_Lean_MessageData_nil);
res = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
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
