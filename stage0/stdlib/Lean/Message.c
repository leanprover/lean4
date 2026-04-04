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
static const lean_ctor_object l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_MessageData_initFn___closed__2_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_948_, lean_object* v_decl_949_, lean_object* v_ref_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
lean_dec_ref(v_decl_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_967_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_968_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_969_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_966_, v___x_967_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
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
v___x_1114_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
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
v___x_1372_ = l_Lean_instInhabitedMessageData_default;
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
v___x_1432_ = l_Lean_instInhabitedMessageData_default;
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
v___x_1493_ = 0;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_a_1495_, lean_object* v_inst_1496_){
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
lean_object* v___y_2402_; lean_object* v___y_2406_; uint8_t v___y_2407_; uint32_t v___y_2408_; lean_object* v_str_2412_; lean_object* v_toBaseMessage_2424_; lean_object* v_kind_2425_; lean_object* v_fileName_2426_; lean_object* v_pos_2427_; lean_object* v_endPos_2428_; uint8_t v_severity_2429_; lean_object* v_caption_2430_; lean_object* v_data_2431_; lean_object* v___y_2433_; lean_object* v_str_2434_; lean_object* v___y_2442_; 
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
v___y_2402_ = v___y_2406_;
goto v___jp_2401_;
}
else
{
if (v___y_2407_ == 0)
{
return v___y_2406_;
}
else
{
v___y_2402_ = v___y_2406_;
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
v___y_2406_ = v_str_2412_;
v___y_2407_ = v___x_2415_;
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
v___y_2406_ = v_str_2412_;
v___y_2407_ = v___x_2415_;
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
v___y_2406_ = v_str_2412_;
v___y_2407_ = v___x_2415_;
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
lean_object* v_fileName_2495_; lean_object* v_pos_2496_; lean_object* v_endPos_2497_; uint8_t v_severity_2498_; lean_object* v_caption_2499_; lean_object* v_data_2500_; lean_object* v___x_2501_; lean_object* v___y_2503_; uint8_t v___y_2507_; lean_object* v___y_2508_; uint32_t v___y_2509_; lean_object* v_str_2513_; lean_object* v___x_2525_; lean_object* v___y_2527_; lean_object* v_str_2528_; lean_object* v___y_2536_; 
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
v___y_2503_ = v___y_2508_;
goto v___jp_2502_;
}
else
{
if (v___y_2507_ == 0)
{
return v___y_2508_;
}
else
{
v___y_2503_ = v___y_2508_;
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
v___y_2507_ = v___x_2516_;
v___y_2508_ = v_str_2513_;
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
v___y_2507_ = v___x_2516_;
v___y_2508_ = v_str_2513_;
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
v___y_2507_ = v___x_2516_;
v___y_2508_ = v_str_2513_;
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
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = l_Lean_NameSet_empty;
v___x_2616_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_2617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
lean_ctor_set(v___x_2617_, 2, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_instInhabitedMessageLog_default;
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__0(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_unsigned_to_nat(32u);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___x_2620_);
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__1(void){
_start:
{
size_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2623_ = ((size_t)5ULL);
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_unsigned_to_nat(32u);
v___x_2626_ = lean_mk_empty_array_with_capacity(v___x_2625_);
v___x_2627_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__0, &l_Lean_MessageLog_empty___closed__0_once, _init_l_Lean_MessageLog_empty___closed__0);
v___x_2628_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___x_2626_);
lean_ctor_set(v___x_2628_, 2, v___x_2624_);
lean_ctor_set(v___x_2628_, 3, v___x_2624_);
lean_ctor_set_usize(v___x_2628_, 4, v___x_2623_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__2(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = l_Lean_NameSet_empty;
v___x_2630_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v___x_2631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
lean_ctor_set(v___x_2631_, 2, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_2633_){
_start:
{
lean_object* v_unreported_2634_; 
v_unreported_2634_ = lean_ctor_get(v_self_2633_, 1);
lean_inc_ref(v_unreported_2634_);
return v_unreported_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_MessageLog_msgs(v_self_2635_);
lean_dec_ref(v_self_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_2637_){
_start:
{
lean_object* v_reported_2638_; lean_object* v_unreported_2639_; lean_object* v___x_2640_; 
v_reported_2638_ = lean_ctor_get(v_x_2637_, 0);
lean_inc_ref(v_reported_2638_);
v_unreported_2639_ = lean_ctor_get(v_x_2637_, 1);
lean_inc_ref(v_unreported_2639_);
lean_dec_ref(v_x_2637_);
v___x_2640_ = l_Lean_PersistentArray_append___redArg(v_reported_2638_, v_unreported_2639_);
lean_dec_ref(v_unreported_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_2641_){
_start:
{
lean_object* v_unreported_2642_; uint8_t v___x_2643_; 
v_unreported_2642_ = lean_ctor_get(v_log_2641_, 1);
v___x_2643_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_2642_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; 
v___x_2644_ = 1;
return v___x_2644_;
}
else
{
uint8_t v___x_2645_; 
v___x_2645_ = 0;
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_2646_){
_start:
{
uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_res_2647_ = l_Lean_MessageLog_hasUnreported(v_log_2646_);
lean_dec_ref(v_log_2646_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_2649_, lean_object* v_log_2650_){
_start:
{
lean_object* v_reported_2651_; lean_object* v_unreported_2652_; lean_object* v_loggedKinds_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2661_; 
v_reported_2651_ = lean_ctor_get(v_log_2650_, 0);
v_unreported_2652_ = lean_ctor_get(v_log_2650_, 1);
v_loggedKinds_2653_ = lean_ctor_get(v_log_2650_, 2);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_log_2650_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2655_ = v_log_2650_;
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_loggedKinds_2653_);
lean_inc(v_unreported_2652_);
lean_inc(v_reported_2651_);
lean_dec(v_log_2650_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = l_Lean_PersistentArray_push___redArg(v_unreported_2652_, v_msg_2649_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2657_);
v___x_2659_ = v___x_2655_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_reported_2651_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_loggedKinds_2653_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_2664_, lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_b_u2082_2664_);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; 
v___x_2667_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2668_, v_x_2669_);
lean_dec(v_x_2669_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_2671_, lean_object* v_k_2672_, lean_object* v_t_2673_){
_start:
{
if (lean_obj_tag(v_t_2673_) == 0)
{
lean_object* v_size_2674_; lean_object* v_k_2675_; lean_object* v_v_2676_; lean_object* v_l_2677_; lean_object* v_r_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2693_; 
v_size_2674_ = lean_ctor_get(v_t_2673_, 0);
v_k_2675_ = lean_ctor_get(v_t_2673_, 1);
v_v_2676_ = lean_ctor_get(v_t_2673_, 2);
v_l_2677_ = lean_ctor_get(v_t_2673_, 3);
v_r_2678_ = lean_ctor_get(v_t_2673_, 4);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_t_2673_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2680_ = v_t_2673_;
v_isShared_2681_ = v_isSharedCheck_2693_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_r_2678_);
lean_inc(v_l_2677_);
lean_inc(v_v_2676_);
lean_inc(v_k_2675_);
lean_inc(v_size_2674_);
lean_dec(v_t_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2693_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
uint8_t v___x_2682_; 
v___x_2682_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2672_, v_k_2675_);
switch(v___x_2682_)
{
case 0:
{
lean_object* v_impl_2683_; lean_object* v___x_2684_; 
lean_del_object(v___x_2680_);
lean_dec(v_size_2674_);
v_impl_2683_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2671_, v_k_2672_, v_l_2677_);
v___x_2684_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2675_, v_v_2676_, v_impl_2683_, v_r_2678_);
return v___x_2684_;
}
case 1:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v_val_2687_; lean_object* v___x_2689_; 
lean_dec(v_k_2675_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_v_2676_);
v___x_2686_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2671_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v_val_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_val_2687_);
lean_dec(v___x_2686_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 2, v_val_2687_);
lean_ctor_set(v___x_2680_, 1, v_k_2672_);
v___x_2689_ = v___x_2680_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_size_2674_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_k_2672_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_val_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_l_2677_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_r_2678_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
default: 
{
lean_object* v_impl_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2680_);
lean_dec(v_size_2674_);
v_impl_2691_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2671_, v_k_2672_, v_r_2678_);
v___x_2692_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2675_, v_v_2676_, v_l_2677_, v_impl_2691_);
return v___x_2692_;
}
}
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v_val_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2671_, v___x_2694_);
v_val_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_val_2696_);
lean_dec(v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_k_2672_);
lean_ctor_set(v___x_2698_, 2, v_val_2696_);
lean_ctor_set(v___x_2698_, 3, v_t_2673_);
lean_ctor_set(v___x_2698_, 4, v_t_2673_);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
lean_object* v_k_2701_; lean_object* v_v_2702_; lean_object* v_l_2703_; lean_object* v_r_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_k_2701_ = lean_ctor_get(v_x_2700_, 1);
lean_inc(v_k_2701_);
v_v_2702_ = lean_ctor_get(v_x_2700_, 2);
lean_inc(v_v_2702_);
v_l_2703_ = lean_ctor_get(v_x_2700_, 3);
lean_inc(v_l_2703_);
v_r_2704_ = lean_ctor_get(v_x_2700_, 4);
lean_inc(v_r_2704_);
lean_dec_ref(v_x_2700_);
v___x_2705_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2699_, v_l_2703_);
v___x_2706_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_2702_, v_k_2701_, v___x_2705_);
v_init_2699_ = v___x_2706_;
v_x_2700_ = v_r_2704_;
goto _start;
}
else
{
return v_init_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_2708_, lean_object* v_l_u2082_2709_){
_start:
{
lean_object* v_reported_2710_; lean_object* v_unreported_2711_; lean_object* v_loggedKinds_2712_; lean_object* v_reported_2713_; lean_object* v_unreported_2714_; lean_object* v_loggedKinds_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2725_; 
v_reported_2710_ = lean_ctor_get(v_l_u2081_2708_, 0);
lean_inc_ref(v_reported_2710_);
v_unreported_2711_ = lean_ctor_get(v_l_u2081_2708_, 1);
lean_inc_ref(v_unreported_2711_);
v_loggedKinds_2712_ = lean_ctor_get(v_l_u2081_2708_, 2);
lean_inc(v_loggedKinds_2712_);
lean_dec_ref(v_l_u2081_2708_);
v_reported_2713_ = lean_ctor_get(v_l_u2082_2709_, 0);
v_unreported_2714_ = lean_ctor_get(v_l_u2082_2709_, 1);
v_loggedKinds_2715_ = lean_ctor_get(v_l_u2082_2709_, 2);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_l_u2082_2709_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2717_ = v_l_u2082_2709_;
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_loggedKinds_2715_);
lean_inc(v_unreported_2714_);
lean_inc(v_reported_2713_);
lean_dec(v_l_u2082_2709_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2719_ = l_Lean_PersistentArray_append___redArg(v_reported_2710_, v_reported_2713_);
lean_dec_ref(v_reported_2713_);
v___x_2720_ = l_Lean_PersistentArray_append___redArg(v_unreported_2711_, v_unreported_2714_);
lean_dec_ref(v_unreported_2714_);
v___x_2721_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_2712_, v_loggedKinds_2715_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 2, v___x_2721_);
lean_ctor_set(v___x_2717_, 1, v___x_2720_);
lean_ctor_set(v___x_2717_, 0, v___x_2719_);
v___x_2723_ = v___x_2717_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_2726_, lean_object* v_k_2727_, lean_object* v_t_2728_, lean_object* v_hl_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2726_, v_k_2727_, v_t_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_2731_, lean_object* v_t_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2731_, v_t_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_2736_, size_t v_i_2737_, size_t v_stop_2738_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_usize_dec_eq(v_i_2737_, v_stop_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; uint8_t v_severity_2741_; uint8_t v___x_2742_; 
v___x_2740_ = lean_array_uget_borrowed(v_as_2736_, v_i_2737_);
v_severity_2741_ = lean_ctor_get_uint8(v___x_2740_, sizeof(void*)*5 + 1);
v___x_2742_ = 1;
if (v_severity_2741_ == 2)
{
return v___x_2742_;
}
else
{
if (v___x_2739_ == 0)
{
size_t v___x_2743_; size_t v___x_2744_; 
v___x_2743_ = ((size_t)1ULL);
v___x_2744_ = lean_usize_add(v_i_2737_, v___x_2743_);
v_i_2737_ = v___x_2744_;
goto _start;
}
else
{
return v___x_2742_;
}
}
}
else
{
uint8_t v___x_2746_; 
v___x_2746_ = 0;
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_2747_, lean_object* v_i_2748_, lean_object* v_stop_2749_){
_start:
{
size_t v_i_boxed_2750_; size_t v_stop_boxed_2751_; uint8_t v_res_2752_; lean_object* v_r_2753_; 
v_i_boxed_2750_ = lean_unbox_usize(v_i_2748_);
lean_dec(v_i_2748_);
v_stop_boxed_2751_ = lean_unbox_usize(v_stop_2749_);
lean_dec(v_stop_2749_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_2747_, v_i_boxed_2750_, v_stop_boxed_2751_);
lean_dec_ref(v_as_2747_);
v_r_2753_ = lean_box(v_res_2752_);
return v_r_2753_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_2754_){
_start:
{
if (lean_obj_tag(v_x_2754_) == 0)
{
lean_object* v_cs_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_cs_2755_ = lean_ctor_get(v_x_2754_, 0);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_array_get_size(v_cs_2755_);
v___x_2758_ = lean_nat_dec_lt(v___x_2756_, v___x_2757_);
if (v___x_2758_ == 0)
{
return v___x_2758_;
}
else
{
if (v___x_2758_ == 0)
{
return v___x_2758_;
}
else
{
size_t v___x_2759_; size_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_of_nat(v___x_2757_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_2755_, v___x_2759_, v___x_2760_);
return v___x_2761_;
}
}
}
else
{
lean_object* v_vs_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_vs_2762_ = lean_ctor_get(v_x_2754_, 0);
v___x_2763_ = lean_unsigned_to_nat(0u);
v___x_2764_ = lean_array_get_size(v_vs_2762_);
v___x_2765_ = lean_nat_dec_lt(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
return v___x_2765_;
}
else
{
if (v___x_2765_ == 0)
{
return v___x_2765_;
}
else
{
size_t v___x_2766_; size_t v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_of_nat(v___x_2764_);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_2762_, v___x_2766_, v___x_2767_);
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_2769_, size_t v_i_2770_, size_t v_stop_2771_){
_start:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_eq(v_i_2770_, v_stop_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = lean_array_uget_borrowed(v_as_2769_, v_i_2770_);
v___x_2774_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_2773_);
if (v___x_2774_ == 0)
{
size_t v___x_2775_; size_t v___x_2776_; 
v___x_2775_ = ((size_t)1ULL);
v___x_2776_ = lean_usize_add(v_i_2770_, v___x_2775_);
v_i_2770_ = v___x_2776_;
goto _start;
}
else
{
return v___x_2774_;
}
}
else
{
uint8_t v___x_2778_; 
v___x_2778_ = 0;
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_2779_, lean_object* v_i_2780_, lean_object* v_stop_2781_){
_start:
{
size_t v_i_boxed_2782_; size_t v_stop_boxed_2783_; uint8_t v_res_2784_; lean_object* v_r_2785_; 
v_i_boxed_2782_ = lean_unbox_usize(v_i_2780_);
lean_dec(v_i_2780_);
v_stop_boxed_2783_ = lean_unbox_usize(v_stop_2781_);
lean_dec(v_stop_2781_);
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_2779_, v_i_boxed_2782_, v_stop_boxed_2783_);
lean_dec_ref(v_as_2779_);
v_r_2785_ = lean_box(v_res_2784_);
return v_r_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_2786_);
lean_dec_ref(v_x_2786_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_2789_){
_start:
{
lean_object* v_root_2790_; lean_object* v_tail_2791_; uint8_t v___x_2792_; 
v_root_2790_ = lean_ctor_get(v_t_2789_, 0);
v_tail_2791_ = lean_ctor_get(v_t_2789_, 1);
v___x_2792_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_2790_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_array_get_size(v_tail_2791_);
v___x_2795_ = lean_nat_dec_lt(v___x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
return v___x_2792_;
}
else
{
if (v___x_2795_ == 0)
{
return v___x_2792_;
}
else
{
size_t v___x_2796_; size_t v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = ((size_t)0ULL);
v___x_2797_ = lean_usize_of_nat(v___x_2794_);
v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_2791_, v___x_2796_, v___x_2797_);
return v___x_2798_;
}
}
}
else
{
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_2799_){
_start:
{
uint8_t v_res_2800_; lean_object* v_r_2801_; 
v_res_2800_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_2799_);
lean_dec_ref(v_t_2799_);
v_r_2801_ = lean_box(v_res_2800_);
return v_r_2801_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_2802_, lean_object* v_as_2803_, size_t v_i_2804_, size_t v_stop_2805_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_eq(v_i_2804_, v_stop_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; uint8_t v_severity_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_array_uget_borrowed(v_as_2803_, v_i_2804_);
v_severity_2808_ = lean_ctor_get_uint8(v___x_2807_, sizeof(void*)*5 + 1);
v___x_2809_ = 1;
if (v_severity_2808_ == 2)
{
return v___x_2809_;
}
else
{
if (v___x_2802_ == 0)
{
size_t v___x_2810_; size_t v___x_2811_; 
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2804_, v___x_2810_);
v_i_2804_ = v___x_2811_;
goto _start;
}
else
{
return v___x_2809_;
}
}
}
else
{
uint8_t v___x_2813_; 
v___x_2813_ = 0;
return v___x_2813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_2814_, lean_object* v_as_2815_, lean_object* v_i_2816_, lean_object* v_stop_2817_){
_start:
{
uint8_t v___x_1884__boxed_2818_; size_t v_i_boxed_2819_; size_t v_stop_boxed_2820_; uint8_t v_res_2821_; lean_object* v_r_2822_; 
v___x_1884__boxed_2818_ = lean_unbox(v___x_2814_);
v_i_boxed_2819_ = lean_unbox_usize(v_i_2816_);
lean_dec(v_i_2816_);
v_stop_boxed_2820_ = lean_unbox_usize(v_stop_2817_);
lean_dec(v_stop_2817_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_2818_, v_as_2815_, v_i_boxed_2819_, v_stop_boxed_2820_);
lean_dec_ref(v_as_2815_);
v_r_2822_ = lean_box(v_res_2821_);
return v_r_2822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v_cs_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_cs_2825_ = lean_ctor_get(v_x_2824_, 0);
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = lean_array_get_size(v_cs_2825_);
v___x_2828_ = lean_nat_dec_lt(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
return v___x_2828_;
}
else
{
if (v___x_2828_ == 0)
{
return v___x_2828_;
}
else
{
size_t v___x_2829_; size_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2827_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_2823_, v_cs_2825_, v___x_2829_, v___x_2830_);
return v___x_2831_;
}
}
}
else
{
lean_object* v_vs_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v_vs_2832_ = lean_ctor_get(v_x_2824_, 0);
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = lean_array_get_size(v_vs_2832_);
v___x_2835_ = lean_nat_dec_lt(v___x_2833_, v___x_2834_);
if (v___x_2835_ == 0)
{
return v___x_2835_;
}
else
{
if (v___x_2835_ == 0)
{
return v___x_2835_;
}
else
{
size_t v___x_2836_; size_t v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = lean_usize_of_nat(v___x_2834_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2823_, v_vs_2832_, v___x_2836_, v___x_2837_);
return v___x_2838_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_2839_, lean_object* v_as_2840_, size_t v_i_2841_, size_t v_stop_2842_){
_start:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_usize_dec_eq(v_i_2841_, v_stop_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = lean_array_uget_borrowed(v_as_2840_, v_i_2841_);
v___x_2845_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2839_, v___x_2844_);
if (v___x_2845_ == 0)
{
size_t v___x_2846_; size_t v___x_2847_; 
v___x_2846_ = ((size_t)1ULL);
v___x_2847_ = lean_usize_add(v_i_2841_, v___x_2846_);
v_i_2841_ = v___x_2847_;
goto _start;
}
else
{
return v___x_2845_;
}
}
else
{
uint8_t v___x_2849_; 
v___x_2849_ = 0;
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2850_, lean_object* v_as_2851_, lean_object* v_i_2852_, lean_object* v_stop_2853_){
_start:
{
uint8_t v___x_1901__boxed_2854_; size_t v_i_boxed_2855_; size_t v_stop_boxed_2856_; uint8_t v_res_2857_; lean_object* v_r_2858_; 
v___x_1901__boxed_2854_ = lean_unbox(v___x_2850_);
v_i_boxed_2855_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_stop_boxed_2856_ = lean_unbox_usize(v_stop_2853_);
lean_dec(v_stop_2853_);
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_2854_, v_as_2851_, v_i_boxed_2855_, v_stop_boxed_2856_);
lean_dec_ref(v_as_2851_);
v_r_2858_ = lean_box(v_res_2857_);
return v_r_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_2859_, lean_object* v_x_2860_){
_start:
{
uint8_t v___x_1909__boxed_2861_; uint8_t v_res_2862_; lean_object* v_r_2863_; 
v___x_1909__boxed_2861_ = lean_unbox(v___x_2859_);
v_res_2862_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_2861_, v_x_2860_);
lean_dec_ref(v_x_2860_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_2864_, lean_object* v_t_2865_){
_start:
{
lean_object* v_root_2866_; lean_object* v_tail_2867_; uint8_t v___x_2868_; 
v_root_2866_ = lean_ctor_get(v_t_2865_, 0);
v_tail_2867_ = lean_ctor_get(v_t_2865_, 1);
v___x_2868_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2864_, v_root_2866_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_array_get_size(v_tail_2867_);
v___x_2871_ = lean_nat_dec_lt(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
return v___x_2868_;
}
else
{
if (v___x_2871_ == 0)
{
return v___x_2868_;
}
else
{
size_t v___x_2872_; size_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = ((size_t)0ULL);
v___x_2873_ = lean_usize_of_nat(v___x_2870_);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2864_, v_tail_2867_, v___x_2872_, v___x_2873_);
return v___x_2874_;
}
}
}
else
{
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_2875_, lean_object* v_t_2876_){
_start:
{
uint8_t v___x_1952__boxed_2877_; uint8_t v_res_2878_; lean_object* v_r_2879_; 
v___x_1952__boxed_2877_ = lean_unbox(v___x_2875_);
v_res_2878_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_2877_, v_t_2876_);
lean_dec_ref(v_t_2876_);
v_r_2879_ = lean_box(v_res_2878_);
return v_r_2879_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_2880_){
_start:
{
lean_object* v_reported_2881_; lean_object* v_unreported_2882_; uint8_t v___x_2883_; 
v_reported_2881_ = lean_ctor_get(v_log_2880_, 0);
v_unreported_2882_ = lean_ctor_get(v_log_2880_, 1);
v___x_2883_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_2881_);
if (v___x_2883_ == 0)
{
uint8_t v___x_2884_; 
v___x_2884_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_2883_, v_unreported_2882_);
return v___x_2884_;
}
else
{
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_2885_){
_start:
{
uint8_t v_res_2886_; lean_object* v_r_2887_; 
v_res_2886_ = l_Lean_MessageLog_hasErrors(v_log_2885_);
lean_dec_ref(v_log_2885_);
v_r_2887_ = lean_box(v_res_2886_);
return v_r_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_2888_){
_start:
{
lean_object* v_reported_2889_; lean_object* v_unreported_2890_; lean_object* v_loggedKinds_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2902_; 
v_reported_2889_ = lean_ctor_get(v_log_2888_, 0);
v_unreported_2890_ = lean_ctor_get(v_log_2888_, 1);
v_loggedKinds_2891_ = lean_ctor_get(v_log_2888_, 2);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_log_2888_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2893_ = v_log_2888_;
v_isShared_2894_ = v_isSharedCheck_2902_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_loggedKinds_2891_);
lean_inc(v_unreported_2890_);
lean_inc(v_reported_2889_);
lean_dec(v_log_2888_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2902_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2895_ = l_Lean_PersistentArray_append___redArg(v_reported_2889_, v_unreported_2890_);
lean_dec_ref(v_unreported_2890_);
v___x_2896_ = lean_unsigned_to_nat(32u);
v___x_2897_ = lean_mk_empty_array_with_capacity(v___x_2896_);
lean_dec_ref(v___x_2897_);
v___x_2898_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2898_);
lean_ctor_set(v___x_2893_, 0, v___x_2895_);
v___x_2900_ = v___x_2893_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_loggedKinds_2891_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_bs_2905_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_lt(v_i_2904_, v_sz_2903_);
if (v___x_2906_ == 0)
{
return v_bs_2905_;
}
else
{
lean_object* v_v_2907_; lean_object* v_fileName_2908_; lean_object* v_pos_2909_; lean_object* v_endPos_2910_; uint8_t v_keepFullRange_2911_; uint8_t v_severity_2912_; uint8_t v_isSilent_2913_; lean_object* v_caption_2914_; lean_object* v_data_2915_; lean_object* v___x_2916_; lean_object* v_bs_x27_2917_; lean_object* v___y_2919_; 
v_v_2907_ = lean_array_uget(v_bs_2905_, v_i_2904_);
v_fileName_2908_ = lean_ctor_get(v_v_2907_, 0);
v_pos_2909_ = lean_ctor_get(v_v_2907_, 1);
v_endPos_2910_ = lean_ctor_get(v_v_2907_, 2);
v_keepFullRange_2911_ = lean_ctor_get_uint8(v_v_2907_, sizeof(void*)*5);
v_severity_2912_ = lean_ctor_get_uint8(v_v_2907_, sizeof(void*)*5 + 1);
v_isSilent_2913_ = lean_ctor_get_uint8(v_v_2907_, sizeof(void*)*5 + 2);
v_caption_2914_ = lean_ctor_get(v_v_2907_, 3);
v_data_2915_ = lean_ctor_get(v_v_2907_, 4);
v___x_2916_ = lean_unsigned_to_nat(0u);
v_bs_x27_2917_ = lean_array_uset(v_bs_2905_, v_i_2904_, v___x_2916_);
if (v_severity_2912_ == 2)
{
lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
lean_inc(v_data_2915_);
lean_inc_ref(v_caption_2914_);
lean_inc(v_endPos_2910_);
lean_inc_ref(v_pos_2909_);
lean_inc_ref(v_fileName_2908_);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_v_2907_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; lean_object* v_unused_2933_; lean_object* v_unused_2934_; lean_object* v_unused_2935_; lean_object* v_unused_2936_; 
v_unused_2932_ = lean_ctor_get(v_v_2907_, 4);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_v_2907_, 3);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_v_2907_, 2);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_v_2907_, 1);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_v_2907_, 0);
lean_dec(v_unused_2936_);
v___x_2925_ = v_v_2907_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v_v_2907_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
uint8_t v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = 1;
if (v_isShared_2926_ == 0)
{
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_fileName_2908_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_pos_2909_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_endPos_2910_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_caption_2914_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_data_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*5, v_keepFullRange_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*5 + 2, v_isSilent_2913_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_ctor_set_uint8(v___x_2929_, sizeof(void*)*5 + 1, v___x_2927_);
v___y_2919_ = v___x_2929_;
goto v___jp_2918_;
}
}
}
else
{
v___y_2919_ = v_v_2907_;
goto v___jp_2918_;
}
v___jp_2918_:
{
size_t v___x_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((size_t)1ULL);
v___x_2921_ = lean_usize_add(v_i_2904_, v___x_2920_);
v___x_2922_ = lean_array_uset(v_bs_x27_2917_, v_i_2904_, v___y_2919_);
v_i_2904_ = v___x_2921_;
v_bs_2905_ = v___x_2922_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_2937_, lean_object* v_i_2938_, lean_object* v_bs_2939_){
_start:
{
size_t v_sz_boxed_2940_; size_t v_i_boxed_2941_; lean_object* v_res_2942_; 
v_sz_boxed_2940_ = lean_unbox_usize(v_sz_2937_);
lean_dec(v_sz_2937_);
v_i_boxed_2941_ = lean_unbox_usize(v_i_2938_);
lean_dec(v_i_2938_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_2940_, v_i_boxed_2941_, v_bs_2939_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_2943_, size_t v_i_2944_, lean_object* v_bs_2945_){
_start:
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
if (v___x_2946_ == 0)
{
return v_bs_2945_;
}
else
{
lean_object* v_v_2947_; lean_object* v___x_2948_; lean_object* v_bs_x27_2949_; lean_object* v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v_v_2947_ = lean_array_uget(v_bs_2945_, v_i_2944_);
v___x_2948_ = lean_unsigned_to_nat(0u);
v_bs_x27_2949_ = lean_array_uset(v_bs_2945_, v_i_2944_, v___x_2948_);
v___x_2950_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_2947_);
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_add(v_i_2944_, v___x_2951_);
v___x_2953_ = lean_array_uset(v_bs_x27_2949_, v_i_2944_, v___x_2950_);
v_i_2944_ = v___x_2952_;
v_bs_2945_ = v___x_2953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
lean_object* v_cs_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2966_; 
v_cs_2956_ = lean_ctor_get(v_x_2955_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2958_ = v_x_2955_;
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_cs_2956_);
lean_dec(v_x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
size_t v_sz_2960_; size_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v_sz_2960_ = lean_array_size(v_cs_2956_);
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_2960_, v___x_2961_, v_cs_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2962_);
v___x_2964_ = v___x_2958_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
else
{
lean_object* v_vs_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2977_; 
v_vs_2967_ = lean_ctor_get(v_x_2955_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2969_ = v_x_2955_;
v_isShared_2970_ = v_isSharedCheck_2977_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_vs_2967_);
lean_dec(v_x_2955_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2977_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
size_t v_sz_2971_; size_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v_sz_2971_ = lean_array_size(v_vs_2967_);
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2971_, v___x_2972_, v_vs_2967_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2973_);
v___x_2975_ = v___x_2969_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2978_, lean_object* v_i_2979_, lean_object* v_bs_2980_){
_start:
{
size_t v_sz_boxed_2981_; size_t v_i_boxed_2982_; lean_object* v_res_2983_; 
v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2978_);
lean_dec(v_sz_2978_);
v_i_boxed_2982_ = lean_unbox_usize(v_i_2979_);
lean_dec(v_i_2979_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_2981_, v_i_boxed_2982_, v_bs_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_2984_){
_start:
{
lean_object* v_root_2985_; lean_object* v_tail_2986_; lean_object* v_size_2987_; size_t v_shift_2988_; lean_object* v_tailOff_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3000_; 
v_root_2985_ = lean_ctor_get(v_t_2984_, 0);
v_tail_2986_ = lean_ctor_get(v_t_2984_, 1);
v_size_2987_ = lean_ctor_get(v_t_2984_, 2);
v_shift_2988_ = lean_ctor_get_usize(v_t_2984_, 4);
v_tailOff_2989_ = lean_ctor_get(v_t_2984_, 3);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_t_2984_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2991_ = v_t_2984_;
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_tailOff_2989_);
lean_inc(v_size_2987_);
lean_inc(v_tail_2986_);
lean_inc(v_root_2985_);
lean_dec(v_t_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; size_t v_sz_2994_; size_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2993_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_2985_);
v_sz_2994_ = lean_array_size(v_tail_2986_);
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2994_, v___x_2995_, v_tail_2986_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_2996_);
lean_ctor_set(v___x_2991_, 0, v___x_2993_);
v___x_2998_ = v___x_2991_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_size_2987_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_tailOff_2989_);
lean_ctor_set_usize(v_reuseFailAlloc_2999_, 4, v_shift_2988_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3001_){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_unreported_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3014_; 
v___x_3002_ = lean_unsigned_to_nat(32u);
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_3002_);
lean_dec_ref(v___x_3003_);
v___x_3004_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3005_ = lean_ctor_get(v_log_3001_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_log_3001_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; lean_object* v_unused_3016_; 
v_unused_3015_ = lean_ctor_get(v_log_3001_, 2);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_log_3001_, 0);
lean_dec(v_unused_3016_);
v___x_3007_ = v_log_3001_;
v_isShared_3008_ = v_isSharedCheck_3014_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_unreported_3005_);
lean_dec(v_log_3001_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3014_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3009_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3005_);
v___x_3010_ = l_Lean_NameSet_empty;
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 2, v___x_3010_);
lean_ctor_set(v___x_3007_, 1, v___x_3009_);
lean_ctor_set(v___x_3007_, 0, v___x_3004_);
v___x_3012_ = v___x_3007_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3017_, size_t v_i_3018_, lean_object* v_bs_3019_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_usize_dec_lt(v_i_3018_, v_sz_3017_);
if (v___x_3020_ == 0)
{
return v_bs_3019_;
}
else
{
lean_object* v_v_3021_; lean_object* v_fileName_3022_; lean_object* v_pos_3023_; lean_object* v_endPos_3024_; uint8_t v_keepFullRange_3025_; uint8_t v_severity_3026_; uint8_t v_isSilent_3027_; lean_object* v_caption_3028_; lean_object* v_data_3029_; lean_object* v___x_3030_; lean_object* v_bs_x27_3031_; lean_object* v___y_3033_; 
v_v_3021_ = lean_array_uget(v_bs_3019_, v_i_3018_);
v_fileName_3022_ = lean_ctor_get(v_v_3021_, 0);
v_pos_3023_ = lean_ctor_get(v_v_3021_, 1);
v_endPos_3024_ = lean_ctor_get(v_v_3021_, 2);
v_keepFullRange_3025_ = lean_ctor_get_uint8(v_v_3021_, sizeof(void*)*5);
v_severity_3026_ = lean_ctor_get_uint8(v_v_3021_, sizeof(void*)*5 + 1);
v_isSilent_3027_ = lean_ctor_get_uint8(v_v_3021_, sizeof(void*)*5 + 2);
v_caption_3028_ = lean_ctor_get(v_v_3021_, 3);
v_data_3029_ = lean_ctor_get(v_v_3021_, 4);
v___x_3030_ = lean_unsigned_to_nat(0u);
v_bs_x27_3031_ = lean_array_uset(v_bs_3019_, v_i_3018_, v___x_3030_);
if (v_severity_3026_ == 2)
{
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3045_; 
lean_inc(v_data_3029_);
lean_inc_ref(v_caption_3028_);
lean_inc(v_endPos_3024_);
lean_inc_ref(v_pos_3023_);
lean_inc_ref(v_fileName_3022_);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_v_3021_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; lean_object* v_unused_3050_; 
v_unused_3046_ = lean_ctor_get(v_v_3021_, 4);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_v_3021_, 3);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v_v_3021_, 2);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v_v_3021_, 1);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v_v_3021_, 0);
lean_dec(v_unused_3050_);
v___x_3039_ = v_v_3021_;
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v_v_3021_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
uint8_t v___x_3041_; lean_object* v___x_3043_; 
v___x_3041_ = 0;
if (v_isShared_3040_ == 0)
{
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_fileName_3022_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_pos_3023_);
lean_ctor_set(v_reuseFailAlloc_3044_, 2, v_endPos_3024_);
lean_ctor_set(v_reuseFailAlloc_3044_, 3, v_caption_3028_);
lean_ctor_set(v_reuseFailAlloc_3044_, 4, v_data_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3044_, sizeof(void*)*5, v_keepFullRange_3025_);
lean_ctor_set_uint8(v_reuseFailAlloc_3044_, sizeof(void*)*5 + 2, v_isSilent_3027_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*5 + 1, v___x_3041_);
v___y_3033_ = v___x_3043_;
goto v___jp_3032_;
}
}
}
else
{
v___y_3033_ = v_v_3021_;
goto v___jp_3032_;
}
v___jp_3032_:
{
size_t v___x_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3018_, v___x_3034_);
v___x_3036_ = lean_array_uset(v_bs_x27_3031_, v_i_3018_, v___y_3033_);
v_i_3018_ = v___x_3035_;
v_bs_3019_ = v___x_3036_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3051_, lean_object* v_i_3052_, lean_object* v_bs_3053_){
_start:
{
size_t v_sz_boxed_3054_; size_t v_i_boxed_3055_; lean_object* v_res_3056_; 
v_sz_boxed_3054_ = lean_unbox_usize(v_sz_3051_);
lean_dec(v_sz_3051_);
v_i_boxed_3055_ = lean_unbox_usize(v_i_3052_);
lean_dec(v_i_3052_);
v_res_3056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3054_, v_i_boxed_3055_, v_bs_3053_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3057_, size_t v_i_3058_, lean_object* v_bs_3059_){
_start:
{
uint8_t v___x_3060_; 
v___x_3060_ = lean_usize_dec_lt(v_i_3058_, v_sz_3057_);
if (v___x_3060_ == 0)
{
return v_bs_3059_;
}
else
{
lean_object* v_v_3061_; lean_object* v___x_3062_; lean_object* v_bs_x27_3063_; lean_object* v___x_3064_; size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v_v_3061_ = lean_array_uget(v_bs_3059_, v_i_3058_);
v___x_3062_ = lean_unsigned_to_nat(0u);
v_bs_x27_3063_ = lean_array_uset(v_bs_3059_, v_i_3058_, v___x_3062_);
v___x_3064_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3061_);
v___x_3065_ = ((size_t)1ULL);
v___x_3066_ = lean_usize_add(v_i_3058_, v___x_3065_);
v___x_3067_ = lean_array_uset(v_bs_x27_3063_, v_i_3058_, v___x_3064_);
v_i_3058_ = v___x_3066_;
v_bs_3059_ = v___x_3067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3069_) == 0)
{
lean_object* v_cs_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3080_; 
v_cs_3070_ = lean_ctor_get(v_x_3069_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_x_3069_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3072_ = v_x_3069_;
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_cs_3070_);
lean_dec(v_x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
size_t v_sz_3074_; size_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v_sz_3074_ = lean_array_size(v_cs_3070_);
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3074_, v___x_3075_, v_cs_3070_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3076_);
v___x_3078_ = v___x_3072_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_object* v_vs_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3091_; 
v_vs_3081_ = lean_ctor_get(v_x_3069_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_x_3069_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3083_ = v_x_3069_;
v_isShared_3084_ = v_isSharedCheck_3091_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_vs_3081_);
lean_dec(v_x_3069_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3091_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v_sz_3085_ = lean_array_size(v_vs_3081_);
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3085_, v___x_3086_, v_vs_3081_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3087_);
v___x_3089_ = v___x_3083_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3092_, lean_object* v_i_3093_, lean_object* v_bs_3094_){
_start:
{
size_t v_sz_boxed_3095_; size_t v_i_boxed_3096_; lean_object* v_res_3097_; 
v_sz_boxed_3095_ = lean_unbox_usize(v_sz_3092_);
lean_dec(v_sz_3092_);
v_i_boxed_3096_ = lean_unbox_usize(v_i_3093_);
lean_dec(v_i_3093_);
v_res_3097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3095_, v_i_boxed_3096_, v_bs_3094_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3098_){
_start:
{
lean_object* v_root_3099_; lean_object* v_tail_3100_; lean_object* v_size_3101_; size_t v_shift_3102_; lean_object* v_tailOff_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3114_; 
v_root_3099_ = lean_ctor_get(v_t_3098_, 0);
v_tail_3100_ = lean_ctor_get(v_t_3098_, 1);
v_size_3101_ = lean_ctor_get(v_t_3098_, 2);
v_shift_3102_ = lean_ctor_get_usize(v_t_3098_, 4);
v_tailOff_3103_ = lean_ctor_get(v_t_3098_, 3);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_t_3098_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3105_ = v_t_3098_;
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_tailOff_3103_);
lean_inc(v_size_3101_);
lean_inc(v_tail_3100_);
lean_inc(v_root_3099_);
lean_dec(v_t_3098_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3114_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; size_t v_sz_3108_; size_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3107_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3099_);
v_sz_3108_ = lean_array_size(v_tail_3100_);
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3108_, v___x_3109_, v_tail_3100_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___x_3110_);
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3112_ = v___x_3105_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_size_3101_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_tailOff_3103_);
lean_ctor_set_usize(v_reuseFailAlloc_3113_, 4, v_shift_3102_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_unreported_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3128_; 
v___x_3116_ = lean_unsigned_to_nat(32u);
v___x_3117_ = lean_mk_empty_array_with_capacity(v___x_3116_);
lean_dec_ref(v___x_3117_);
v___x_3118_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3119_ = lean_ctor_get(v_log_3115_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_log_3115_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3129_ = lean_ctor_get(v_log_3115_, 2);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_log_3115_, 0);
lean_dec(v_unused_3130_);
v___x_3121_ = v_log_3115_;
v_isShared_3122_ = v_isSharedCheck_3128_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_unreported_3119_);
lean_dec(v_log_3115_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3128_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3119_);
v___x_3124_ = l_Lean_NameSet_empty;
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 2, v___x_3124_);
lean_ctor_set(v___x_3121_, 1, v___x_3123_);
lean_ctor_set(v___x_3121_, 0, v___x_3118_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3131_, size_t v_i_3132_, size_t v_stop_3133_, lean_object* v_b_3134_){
_start:
{
lean_object* v___y_3136_; uint8_t v___x_3140_; 
v___x_3140_ = lean_usize_dec_eq(v_i_3132_, v_stop_3133_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; uint8_t v_severity_3142_; 
v___x_3141_ = lean_array_uget_borrowed(v_as_3131_, v_i_3132_);
v_severity_3142_ = lean_ctor_get_uint8(v___x_3141_, sizeof(void*)*5 + 1);
if (v_severity_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_inc(v___x_3141_);
v___x_3143_ = l_Lean_PersistentArray_push___redArg(v_b_3134_, v___x_3141_);
v___y_3136_ = v___x_3143_;
goto v___jp_3135_;
}
else
{
v___y_3136_ = v_b_3134_;
goto v___jp_3135_;
}
}
else
{
return v_b_3134_;
}
v___jp_3135_:
{
size_t v___x_3137_; size_t v___x_3138_; 
v___x_3137_ = ((size_t)1ULL);
v___x_3138_ = lean_usize_add(v_i_3132_, v___x_3137_);
v_i_3132_ = v___x_3138_;
v_b_3134_ = v___y_3136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3144_, lean_object* v_i_3145_, lean_object* v_stop_3146_, lean_object* v_b_3147_){
_start:
{
size_t v_i_boxed_3148_; size_t v_stop_boxed_3149_; lean_object* v_res_3150_; 
v_i_boxed_3148_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_stop_boxed_3149_ = lean_unbox_usize(v_stop_3146_);
lean_dec(v_stop_3146_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3144_, v_i_boxed_3148_, v_stop_boxed_3149_, v_b_3147_);
lean_dec_ref(v_as_3144_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3151_, lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 0)
{
lean_object* v_cs_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v_cs_3153_ = lean_ctor_get(v_x_3151_, 0);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = lean_array_get_size(v_cs_3153_);
v___x_3156_ = lean_nat_dec_lt(v___x_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
return v_x_3152_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_nat_dec_le(v___x_3155_, v___x_3155_);
if (v___x_3157_ == 0)
{
if (v___x_3156_ == 0)
{
return v_x_3152_;
}
else
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((size_t)0ULL);
v___x_3159_ = lean_usize_of_nat(v___x_3155_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3153_, v___x_3158_, v___x_3159_, v_x_3152_);
return v___x_3160_;
}
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = lean_usize_of_nat(v___x_3155_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3153_, v___x_3161_, v___x_3162_, v_x_3152_);
return v___x_3163_;
}
}
}
else
{
lean_object* v_vs_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_vs_3164_ = lean_ctor_get(v_x_3151_, 0);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_array_get_size(v_vs_3164_);
v___x_3167_ = lean_nat_dec_lt(v___x_3165_, v___x_3166_);
if (v___x_3167_ == 0)
{
return v_x_3152_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_nat_dec_le(v___x_3166_, v___x_3166_);
if (v___x_3168_ == 0)
{
if (v___x_3167_ == 0)
{
return v_x_3152_;
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = ((size_t)0ULL);
v___x_3170_ = lean_usize_of_nat(v___x_3166_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3164_, v___x_3169_, v___x_3170_, v_x_3152_);
return v___x_3171_;
}
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = ((size_t)0ULL);
v___x_3173_ = lean_usize_of_nat(v___x_3166_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3164_, v___x_3172_, v___x_3173_, v_x_3152_);
return v___x_3174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3175_, size_t v_i_3176_, size_t v_stop_3177_, lean_object* v_b_3178_){
_start:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_eq(v_i_3176_, v_stop_3177_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; size_t v___x_3182_; size_t v___x_3183_; 
v___x_3180_ = lean_array_uget_borrowed(v_as_3175_, v_i_3176_);
v___x_3181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3180_, v_b_3178_);
v___x_3182_ = ((size_t)1ULL);
v___x_3183_ = lean_usize_add(v_i_3176_, v___x_3182_);
v_i_3176_ = v___x_3183_;
v_b_3178_ = v___x_3181_;
goto _start;
}
else
{
return v_b_3178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3185_, lean_object* v_i_3186_, lean_object* v_stop_3187_, lean_object* v_b_3188_){
_start:
{
size_t v_i_boxed_3189_; size_t v_stop_boxed_3190_; lean_object* v_res_3191_; 
v_i_boxed_3189_ = lean_unbox_usize(v_i_3186_);
lean_dec(v_i_3186_);
v_stop_boxed_3190_ = lean_unbox_usize(v_stop_3187_);
lean_dec(v_stop_3187_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3185_, v_i_boxed_3189_, v_stop_boxed_3190_, v_b_3188_);
lean_dec_ref(v_as_3185_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3192_, v_x_3193_);
lean_dec_ref(v_x_3192_);
return v_res_3194_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3196_, size_t v_x_3197_, size_t v_x_3198_, lean_object* v_x_3199_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_object* v_cs_3200_; lean_object* v___x_3201_; size_t v___x_3202_; lean_object* v_j_3203_; lean_object* v___x_3204_; size_t v___x_3205_; size_t v___x_3206_; size_t v___x_3207_; size_t v___x_3208_; size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_cs_3200_ = lean_ctor_get(v_x_3196_, 0);
v___x_3201_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3202_ = lean_usize_shift_right(v_x_3197_, v_x_3198_);
v_j_3203_ = lean_usize_to_nat(v___x_3202_);
v___x_3204_ = lean_array_get_borrowed(v___x_3201_, v_cs_3200_, v_j_3203_);
v___x_3205_ = ((size_t)1ULL);
v___x_3206_ = lean_usize_shift_left(v___x_3205_, v_x_3198_);
v___x_3207_ = lean_usize_sub(v___x_3206_, v___x_3205_);
v___x_3208_ = lean_usize_land(v_x_3197_, v___x_3207_);
v___x_3209_ = ((size_t)5ULL);
v___x_3210_ = lean_usize_sub(v_x_3198_, v___x_3209_);
v___x_3211_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3204_, v___x_3208_, v___x_3210_, v_x_3199_);
v___x_3212_ = lean_unsigned_to_nat(1u);
v___x_3213_ = lean_nat_add(v_j_3203_, v___x_3212_);
lean_dec(v_j_3203_);
v___x_3214_ = lean_array_get_size(v_cs_3200_);
v___x_3215_ = lean_nat_dec_lt(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_dec(v___x_3213_);
return v___x_3211_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_nat_dec_le(v___x_3214_, v___x_3214_);
if (v___x_3216_ == 0)
{
if (v___x_3215_ == 0)
{
lean_dec(v___x_3213_);
return v___x_3211_;
}
else
{
size_t v___x_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_usize_of_nat(v___x_3213_);
lean_dec(v___x_3213_);
v___x_3218_ = lean_usize_of_nat(v___x_3214_);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3200_, v___x_3217_, v___x_3218_, v___x_3211_);
return v___x_3219_;
}
}
else
{
size_t v___x_3220_; size_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = lean_usize_of_nat(v___x_3213_);
lean_dec(v___x_3213_);
v___x_3221_ = lean_usize_of_nat(v___x_3214_);
v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3200_, v___x_3220_, v___x_3221_, v___x_3211_);
return v___x_3222_;
}
}
}
else
{
lean_object* v_vs_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_vs_3223_ = lean_ctor_get(v_x_3196_, 0);
v___x_3224_ = lean_usize_to_nat(v_x_3197_);
v___x_3225_ = lean_array_get_size(v_vs_3223_);
v___x_3226_ = lean_nat_dec_lt(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_dec(v___x_3224_);
return v_x_3199_;
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_nat_dec_le(v___x_3225_, v___x_3225_);
if (v___x_3227_ == 0)
{
if (v___x_3226_ == 0)
{
lean_dec(v___x_3224_);
return v_x_3199_;
}
else
{
size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_usize_of_nat(v___x_3224_);
lean_dec(v___x_3224_);
v___x_3229_ = lean_usize_of_nat(v___x_3225_);
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3223_, v___x_3228_, v___x_3229_, v_x_3199_);
return v___x_3230_;
}
}
else
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_usize_of_nat(v___x_3224_);
lean_dec(v___x_3224_);
v___x_3232_ = lean_usize_of_nat(v___x_3225_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3223_, v___x_3231_, v___x_3232_, v_x_3199_);
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
size_t v_x_1528__boxed_3238_; size_t v_x_1529__boxed_3239_; lean_object* v_res_3240_; 
v_x_1528__boxed_3238_ = lean_unbox_usize(v_x_3235_);
lean_dec(v_x_3235_);
v_x_1529__boxed_3239_ = lean_unbox_usize(v_x_3236_);
lean_dec(v_x_3236_);
v_res_3240_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3234_, v_x_1528__boxed_3238_, v_x_1529__boxed_3239_, v_x_3237_);
lean_dec_ref(v_x_3234_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3241_, lean_object* v_init_3242_, lean_object* v_start_3243_){
_start:
{
lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = lean_unsigned_to_nat(0u);
v___x_3245_ = lean_nat_dec_eq(v_start_3243_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v_root_3246_; lean_object* v_tail_3247_; size_t v_shift_3248_; lean_object* v_tailOff_3249_; uint8_t v___x_3250_; 
v_root_3246_ = lean_ctor_get(v_t_3241_, 0);
v_tail_3247_ = lean_ctor_get(v_t_3241_, 1);
v_shift_3248_ = lean_ctor_get_usize(v_t_3241_, 4);
v_tailOff_3249_ = lean_ctor_get(v_t_3241_, 3);
v___x_3250_ = lean_nat_dec_le(v_tailOff_3249_, v_start_3243_);
if (v___x_3250_ == 0)
{
size_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3251_ = lean_usize_of_nat(v_start_3243_);
v___x_3252_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3246_, v___x_3251_, v_shift_3248_, v_init_3242_);
v___x_3253_ = lean_array_get_size(v_tail_3247_);
v___x_3254_ = lean_nat_dec_lt(v___x_3244_, v___x_3253_);
if (v___x_3254_ == 0)
{
return v___x_3252_;
}
else
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_nat_dec_le(v___x_3253_, v___x_3253_);
if (v___x_3255_ == 0)
{
if (v___x_3254_ == 0)
{
return v___x_3252_;
}
else
{
size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = ((size_t)0ULL);
v___x_3257_ = lean_usize_of_nat(v___x_3253_);
v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3247_, v___x_3256_, v___x_3257_, v___x_3252_);
return v___x_3258_;
}
}
else
{
size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = lean_usize_of_nat(v___x_3253_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3247_, v___x_3259_, v___x_3260_, v___x_3252_);
return v___x_3261_;
}
}
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_nat_sub(v_start_3243_, v_tailOff_3249_);
v___x_3263_ = lean_array_get_size(v_tail_3247_);
v___x_3264_ = lean_nat_dec_lt(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_dec(v___x_3262_);
return v_init_3242_;
}
else
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_nat_dec_le(v___x_3263_, v___x_3263_);
if (v___x_3265_ == 0)
{
if (v___x_3264_ == 0)
{
lean_dec(v___x_3262_);
return v_init_3242_;
}
else
{
size_t v___x_3266_; size_t v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_usize_of_nat(v___x_3262_);
lean_dec(v___x_3262_);
v___x_3267_ = lean_usize_of_nat(v___x_3263_);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3247_, v___x_3266_, v___x_3267_, v_init_3242_);
return v___x_3268_;
}
}
else
{
size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_usize_of_nat(v___x_3262_);
lean_dec(v___x_3262_);
v___x_3270_ = lean_usize_of_nat(v___x_3263_);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3247_, v___x_3269_, v___x_3270_, v_init_3242_);
return v___x_3271_;
}
}
}
}
else
{
lean_object* v_root_3272_; lean_object* v_tail_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v_root_3272_ = lean_ctor_get(v_t_3241_, 0);
v_tail_3273_ = lean_ctor_get(v_t_3241_, 1);
v___x_3274_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3272_, v_init_3242_);
v___x_3275_ = lean_array_get_size(v_tail_3273_);
v___x_3276_ = lean_nat_dec_lt(v___x_3244_, v___x_3275_);
if (v___x_3276_ == 0)
{
return v___x_3274_;
}
else
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_nat_dec_le(v___x_3275_, v___x_3275_);
if (v___x_3277_ == 0)
{
if (v___x_3276_ == 0)
{
return v___x_3274_;
}
else
{
size_t v___x_3278_; size_t v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = ((size_t)0ULL);
v___x_3279_ = lean_usize_of_nat(v___x_3275_);
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3273_, v___x_3278_, v___x_3279_, v___x_3274_);
return v___x_3280_;
}
}
else
{
size_t v___x_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = lean_usize_of_nat(v___x_3275_);
v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3273_, v___x_3281_, v___x_3282_, v___x_3274_);
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3284_, lean_object* v_init_3285_, lean_object* v_start_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3284_, v_init_3285_, v_start_3286_);
lean_dec(v_start_3286_);
lean_dec_ref(v_t_3284_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3288_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v_unreported_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3302_; 
v___x_3289_ = lean_unsigned_to_nat(32u);
v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
lean_dec_ref(v___x_3290_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3293_ = lean_ctor_get(v_log_3288_, 1);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_log_3288_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; lean_object* v_unused_3304_; 
v_unused_3303_ = lean_ctor_get(v_log_3288_, 2);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_log_3288_, 0);
lean_dec(v_unused_3304_);
v___x_3295_ = v_log_3288_;
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_unreported_3293_);
lean_dec(v_log_3288_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3297_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3293_, v___x_3292_, v___x_3291_);
lean_dec_ref(v_unreported_3293_);
v___x_3298_ = l_Lean_NameSet_empty;
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 2, v___x_3298_);
lean_ctor_set(v___x_3295_, 1, v___x_3297_);
lean_ctor_set(v___x_3295_, 0, v___x_3292_);
v___x_3300_ = v___x_3295_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3305_, size_t v_i_3306_, size_t v_stop_3307_, lean_object* v_b_3308_){
_start:
{
lean_object* v___y_3310_; uint8_t v___x_3314_; 
v___x_3314_ = lean_usize_dec_eq(v_i_3306_, v_stop_3307_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; uint8_t v_severity_3316_; 
v___x_3315_ = lean_array_uget_borrowed(v_as_3305_, v_i_3306_);
v_severity_3316_ = lean_ctor_get_uint8(v___x_3315_, sizeof(void*)*5 + 1);
if (v_severity_3316_ == 1)
{
lean_object* v___x_3317_; 
lean_inc(v___x_3315_);
v___x_3317_ = l_Lean_PersistentArray_push___redArg(v_b_3308_, v___x_3315_);
v___y_3310_ = v___x_3317_;
goto v___jp_3309_;
}
else
{
v___y_3310_ = v_b_3308_;
goto v___jp_3309_;
}
}
else
{
return v_b_3308_;
}
v___jp_3309_:
{
size_t v___x_3311_; size_t v___x_3312_; 
v___x_3311_ = ((size_t)1ULL);
v___x_3312_ = lean_usize_add(v_i_3306_, v___x_3311_);
v_i_3306_ = v___x_3312_;
v_b_3308_ = v___y_3310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3318_, lean_object* v_i_3319_, lean_object* v_stop_3320_, lean_object* v_b_3321_){
_start:
{
size_t v_i_boxed_3322_; size_t v_stop_boxed_3323_; lean_object* v_res_3324_; 
v_i_boxed_3322_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_stop_boxed_3323_ = lean_unbox_usize(v_stop_3320_);
lean_dec(v_stop_3320_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3318_, v_i_boxed_3322_, v_stop_boxed_3323_, v_b_3321_);
lean_dec_ref(v_as_3318_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3325_, lean_object* v_x_3326_){
_start:
{
if (lean_obj_tag(v_x_3325_) == 0)
{
lean_object* v_cs_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_cs_3327_ = lean_ctor_get(v_x_3325_, 0);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_array_get_size(v_cs_3327_);
v___x_3330_ = lean_nat_dec_lt(v___x_3328_, v___x_3329_);
if (v___x_3330_ == 0)
{
return v_x_3326_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_le(v___x_3329_, v___x_3329_);
if (v___x_3331_ == 0)
{
if (v___x_3330_ == 0)
{
return v_x_3326_;
}
else
{
size_t v___x_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = lean_usize_of_nat(v___x_3329_);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3327_, v___x_3332_, v___x_3333_, v_x_3326_);
return v___x_3334_;
}
}
else
{
size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = ((size_t)0ULL);
v___x_3336_ = lean_usize_of_nat(v___x_3329_);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3327_, v___x_3335_, v___x_3336_, v_x_3326_);
return v___x_3337_;
}
}
}
else
{
lean_object* v_vs_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v_vs_3338_ = lean_ctor_get(v_x_3325_, 0);
v___x_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = lean_array_get_size(v_vs_3338_);
v___x_3341_ = lean_nat_dec_lt(v___x_3339_, v___x_3340_);
if (v___x_3341_ == 0)
{
return v_x_3326_;
}
else
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_nat_dec_le(v___x_3340_, v___x_3340_);
if (v___x_3342_ == 0)
{
if (v___x_3341_ == 0)
{
return v_x_3326_;
}
else
{
size_t v___x_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = ((size_t)0ULL);
v___x_3344_ = lean_usize_of_nat(v___x_3340_);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3338_, v___x_3343_, v___x_3344_, v_x_3326_);
return v___x_3345_;
}
}
else
{
size_t v___x_3346_; size_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = ((size_t)0ULL);
v___x_3347_ = lean_usize_of_nat(v___x_3340_);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3338_, v___x_3346_, v___x_3347_, v_x_3326_);
return v___x_3348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3349_, size_t v_i_3350_, size_t v_stop_3351_, lean_object* v_b_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_eq(v_i_3350_, v_stop_3351_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3355_; size_t v___x_3356_; size_t v___x_3357_; 
v___x_3354_ = lean_array_uget_borrowed(v_as_3349_, v_i_3350_);
v___x_3355_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3354_, v_b_3352_);
v___x_3356_ = ((size_t)1ULL);
v___x_3357_ = lean_usize_add(v_i_3350_, v___x_3356_);
v_i_3350_ = v___x_3357_;
v_b_3352_ = v___x_3355_;
goto _start;
}
else
{
return v_b_3352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3359_, lean_object* v_i_3360_, lean_object* v_stop_3361_, lean_object* v_b_3362_){
_start:
{
size_t v_i_boxed_3363_; size_t v_stop_boxed_3364_; lean_object* v_res_3365_; 
v_i_boxed_3363_ = lean_unbox_usize(v_i_3360_);
lean_dec(v_i_3360_);
v_stop_boxed_3364_ = lean_unbox_usize(v_stop_3361_);
lean_dec(v_stop_3361_);
v_res_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3359_, v_i_boxed_3363_, v_stop_boxed_3364_, v_b_3362_);
lean_dec_ref(v_as_3359_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3366_, lean_object* v_x_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3366_, v_x_3367_);
lean_dec_ref(v_x_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3369_, size_t v_x_3370_, size_t v_x_3371_, lean_object* v_x_3372_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v_cs_3373_; lean_object* v___x_3374_; size_t v___x_3375_; lean_object* v_j_3376_; lean_object* v___x_3377_; size_t v___x_3378_; size_t v___x_3379_; size_t v___x_3380_; size_t v___x_3381_; size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v_cs_3373_ = lean_ctor_get(v_x_3369_, 0);
v___x_3374_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3375_ = lean_usize_shift_right(v_x_3370_, v_x_3371_);
v_j_3376_ = lean_usize_to_nat(v___x_3375_);
v___x_3377_ = lean_array_get_borrowed(v___x_3374_, v_cs_3373_, v_j_3376_);
v___x_3378_ = ((size_t)1ULL);
v___x_3379_ = lean_usize_shift_left(v___x_3378_, v_x_3371_);
v___x_3380_ = lean_usize_sub(v___x_3379_, v___x_3378_);
v___x_3381_ = lean_usize_land(v_x_3370_, v___x_3380_);
v___x_3382_ = ((size_t)5ULL);
v___x_3383_ = lean_usize_sub(v_x_3371_, v___x_3382_);
v___x_3384_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3377_, v___x_3381_, v___x_3383_, v_x_3372_);
v___x_3385_ = lean_unsigned_to_nat(1u);
v___x_3386_ = lean_nat_add(v_j_3376_, v___x_3385_);
lean_dec(v_j_3376_);
v___x_3387_ = lean_array_get_size(v_cs_3373_);
v___x_3388_ = lean_nat_dec_lt(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_dec(v___x_3386_);
return v___x_3384_;
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_nat_dec_le(v___x_3387_, v___x_3387_);
if (v___x_3389_ == 0)
{
if (v___x_3388_ == 0)
{
lean_dec(v___x_3386_);
return v___x_3384_;
}
else
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = lean_usize_of_nat(v___x_3386_);
lean_dec(v___x_3386_);
v___x_3391_ = lean_usize_of_nat(v___x_3387_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3373_, v___x_3390_, v___x_3391_, v___x_3384_);
return v___x_3392_;
}
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_usize_of_nat(v___x_3386_);
lean_dec(v___x_3386_);
v___x_3394_ = lean_usize_of_nat(v___x_3387_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3373_, v___x_3393_, v___x_3394_, v___x_3384_);
return v___x_3395_;
}
}
}
else
{
lean_object* v_vs_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_vs_3396_ = lean_ctor_get(v_x_3369_, 0);
v___x_3397_ = lean_usize_to_nat(v_x_3370_);
v___x_3398_ = lean_array_get_size(v_vs_3396_);
v___x_3399_ = lean_nat_dec_lt(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_dec(v___x_3397_);
return v_x_3372_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_nat_dec_le(v___x_3398_, v___x_3398_);
if (v___x_3400_ == 0)
{
if (v___x_3399_ == 0)
{
lean_dec(v___x_3397_);
return v_x_3372_;
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_usize_of_nat(v___x_3397_);
lean_dec(v___x_3397_);
v___x_3402_ = lean_usize_of_nat(v___x_3398_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3396_, v___x_3401_, v___x_3402_, v_x_3372_);
return v___x_3403_;
}
}
else
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = lean_usize_of_nat(v___x_3397_);
lean_dec(v___x_3397_);
v___x_3405_ = lean_usize_of_nat(v___x_3398_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3396_, v___x_3404_, v___x_3405_, v_x_3372_);
return v___x_3406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3407_, lean_object* v_x_3408_, lean_object* v_x_3409_, lean_object* v_x_3410_){
_start:
{
size_t v_x_1527__boxed_3411_; size_t v_x_1528__boxed_3412_; lean_object* v_res_3413_; 
v_x_1527__boxed_3411_ = lean_unbox_usize(v_x_3408_);
lean_dec(v_x_3408_);
v_x_1528__boxed_3412_ = lean_unbox_usize(v_x_3409_);
lean_dec(v_x_3409_);
v_res_3413_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3407_, v_x_1527__boxed_3411_, v_x_1528__boxed_3412_, v_x_3410_);
lean_dec_ref(v_x_3407_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3414_, lean_object* v_init_3415_, lean_object* v_start_3416_){
_start:
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_nat_dec_eq(v_start_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v_root_3419_; lean_object* v_tail_3420_; size_t v_shift_3421_; lean_object* v_tailOff_3422_; uint8_t v___x_3423_; 
v_root_3419_ = lean_ctor_get(v_t_3414_, 0);
v_tail_3420_ = lean_ctor_get(v_t_3414_, 1);
v_shift_3421_ = lean_ctor_get_usize(v_t_3414_, 4);
v_tailOff_3422_ = lean_ctor_get(v_t_3414_, 3);
v___x_3423_ = lean_nat_dec_le(v_tailOff_3422_, v_start_3416_);
if (v___x_3423_ == 0)
{
size_t v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3424_ = lean_usize_of_nat(v_start_3416_);
v___x_3425_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3419_, v___x_3424_, v_shift_3421_, v_init_3415_);
v___x_3426_ = lean_array_get_size(v_tail_3420_);
v___x_3427_ = lean_nat_dec_lt(v___x_3417_, v___x_3426_);
if (v___x_3427_ == 0)
{
return v___x_3425_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
if (v___x_3428_ == 0)
{
if (v___x_3427_ == 0)
{
return v___x_3425_;
}
else
{
size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3426_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3420_, v___x_3429_, v___x_3430_, v___x_3425_);
return v___x_3431_;
}
}
else
{
size_t v___x_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = lean_usize_of_nat(v___x_3426_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3420_, v___x_3432_, v___x_3433_, v___x_3425_);
return v___x_3434_;
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3435_ = lean_nat_sub(v_start_3416_, v_tailOff_3422_);
v___x_3436_ = lean_array_get_size(v_tail_3420_);
v___x_3437_ = lean_nat_dec_lt(v___x_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_dec(v___x_3435_);
return v_init_3415_;
}
else
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_nat_dec_le(v___x_3436_, v___x_3436_);
if (v___x_3438_ == 0)
{
if (v___x_3437_ == 0)
{
lean_dec(v___x_3435_);
return v_init_3415_;
}
else
{
size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = lean_usize_of_nat(v___x_3435_);
lean_dec(v___x_3435_);
v___x_3440_ = lean_usize_of_nat(v___x_3436_);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3420_, v___x_3439_, v___x_3440_, v_init_3415_);
return v___x_3441_;
}
}
else
{
size_t v___x_3442_; size_t v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = lean_usize_of_nat(v___x_3435_);
lean_dec(v___x_3435_);
v___x_3443_ = lean_usize_of_nat(v___x_3436_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3420_, v___x_3442_, v___x_3443_, v_init_3415_);
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_root_3445_; lean_object* v_tail_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_root_3445_ = lean_ctor_get(v_t_3414_, 0);
v_tail_3446_ = lean_ctor_get(v_t_3414_, 1);
v___x_3447_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3445_, v_init_3415_);
v___x_3448_ = lean_array_get_size(v_tail_3446_);
v___x_3449_ = lean_nat_dec_lt(v___x_3417_, v___x_3448_);
if (v___x_3449_ == 0)
{
return v___x_3447_;
}
else
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_nat_dec_le(v___x_3448_, v___x_3448_);
if (v___x_3450_ == 0)
{
if (v___x_3449_ == 0)
{
return v___x_3447_;
}
else
{
size_t v___x_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = ((size_t)0ULL);
v___x_3452_ = lean_usize_of_nat(v___x_3448_);
v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3446_, v___x_3451_, v___x_3452_, v___x_3447_);
return v___x_3453_;
}
}
else
{
size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = lean_usize_of_nat(v___x_3448_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3446_, v___x_3454_, v___x_3455_, v___x_3447_);
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3457_, lean_object* v_init_3458_, lean_object* v_start_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3457_, v_init_3458_, v_start_3459_);
lean_dec(v_start_3459_);
lean_dec_ref(v_t_3457_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3461_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v_unreported_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
v___x_3462_ = lean_unsigned_to_nat(32u);
v___x_3463_ = lean_mk_empty_array_with_capacity(v___x_3462_);
lean_dec_ref(v___x_3463_);
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3466_ = lean_ctor_get(v_log_3461_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_log_3461_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; 
v_unused_3476_ = lean_ctor_get(v_log_3461_, 2);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_log_3461_, 0);
lean_dec(v_unused_3477_);
v___x_3468_ = v_log_3461_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_unreported_3466_);
lean_dec(v_log_3461_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3466_, v___x_3465_, v___x_3464_);
lean_dec_ref(v_unreported_3466_);
v___x_3471_ = l_Lean_NameSet_empty;
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 2, v___x_3471_);
lean_ctor_set(v___x_3468_, 1, v___x_3470_);
lean_ctor_set(v___x_3468_, 0, v___x_3465_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3478_, lean_object* v_log_3479_, lean_object* v_f_3480_){
_start:
{
lean_object* v_unreported_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_unreported_3481_ = lean_ctor_get(v_log_3479_, 1);
lean_inc_ref(v_unreported_3481_);
lean_dec_ref(v_log_3479_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = l_Lean_PersistentArray_forM___redArg(v_inst_3478_, v_unreported_3481_, v_f_3480_, v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3484_, lean_object* v_inst_3485_, lean_object* v_log_3486_, lean_object* v_f_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_MessageLog_forM___redArg(v_inst_3485_, v_log_3486_, v_f_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3489_){
_start:
{
lean_object* v_unreported_3490_; lean_object* v___x_3491_; 
v_unreported_3490_ = lean_ctor_get(v_log_3489_, 1);
v___x_3491_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_MessageLog_toList(v_log_3492_);
lean_dec_ref(v_log_3492_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3494_){
_start:
{
lean_object* v_unreported_3495_; lean_object* v___x_3496_; 
v_unreported_3495_ = lean_ctor_get(v_log_3494_, 1);
v___x_3496_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_MessageLog_toArray(v_log_3497_);
lean_dec_ref(v_log_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3499_){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_unsigned_to_nat(2u);
v___x_3501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v_msg_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v_msg_3502_);
v___x_3505_ = l_Lean_MessageData_nestD(v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = l_Lean_MessageData_ofExpr(v_e_3506_);
v___x_3508_ = l_Lean_indentD(v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3509_, lean_object* v_msg_3510_){
_start:
{
lean_object* v_env_3512_; lean_object* v_mctx_3513_; lean_object* v_lctx_3514_; lean_object* v_opts_3515_; lean_object* v_currNamespace_3516_; lean_object* v_openDecls_3517_; lean_object* v___x_3518_; lean_object* v_msg_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_env_3512_ = lean_ctor_get(v_ctx_3509_, 0);
v_mctx_3513_ = lean_ctor_get(v_ctx_3509_, 1);
v_lctx_3514_ = lean_ctor_get(v_ctx_3509_, 2);
v_opts_3515_ = lean_ctor_get(v_ctx_3509_, 3);
v_currNamespace_3516_ = lean_ctor_get(v_ctx_3509_, 4);
v_openDecls_3517_ = lean_ctor_get(v_ctx_3509_, 5);
lean_inc(v_openDecls_3517_);
lean_inc(v_currNamespace_3516_);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v_currNamespace_3516_);
lean_ctor_set(v___x_3518_, 1, v_openDecls_3517_);
v_msg_3519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3519_, 0, v___x_3518_);
lean_ctor_set(v_msg_3519_, 1, v_msg_3510_);
lean_inc_ref(v_opts_3515_);
lean_inc_ref(v_lctx_3514_);
lean_inc_ref(v_mctx_3513_);
lean_inc_ref(v_env_3512_);
v___x_3520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3520_, 0, v_env_3512_);
lean_ctor_set(v___x_3520_, 1, v_mctx_3513_);
lean_ctor_set(v___x_3520_, 2, v_lctx_3514_);
lean_ctor_set(v___x_3520_, 3, v_opts_3515_);
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_format(v_msg_3519_, v___x_3521_);
v___x_3523_ = l_Std_Format_defWidth;
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = l_Std_Format_pretty(v___x_3522_, v___x_3523_, v___x_3524_, v___x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3526_, lean_object* v_msg_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3526_, v_msg_3527_);
lean_dec_ref(v_ctx_3526_);
return v_res_3529_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object* v_s_3530_, lean_object* v_a_3531_, uint8_t v_b_3532_){
_start:
{
lean_object* v_str_3533_; lean_object* v_startInclusive_3534_; lean_object* v_endExclusive_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_str_3533_ = lean_ctor_get(v_s_3530_, 0);
v_startInclusive_3534_ = lean_ctor_get(v_s_3530_, 1);
v_endExclusive_3535_ = lean_ctor_get(v_s_3530_, 2);
v___x_3536_ = lean_nat_sub(v_endExclusive_3535_, v_startInclusive_3534_);
v___x_3537_ = lean_nat_dec_eq(v_a_3531_, v___x_3536_);
lean_dec(v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; uint32_t v___x_3539_; uint32_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3538_ = lean_nat_add(v_startInclusive_3534_, v_a_3531_);
lean_dec(v_a_3531_);
v___x_3539_ = lean_string_utf8_get_fast(v_str_3533_, v___x_3538_);
v___x_3540_ = 10;
v___x_3541_ = lean_uint32_dec_eq(v___x_3539_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_string_utf8_next_fast(v_str_3533_, v___x_3538_);
lean_dec(v___x_3538_);
v___x_3543_ = lean_nat_sub(v___x_3542_, v_startInclusive_3534_);
v_a_3531_ = v___x_3543_;
v_b_3532_ = v___x_3541_;
goto _start;
}
else
{
lean_dec(v___x_3538_);
return v___x_3541_;
}
}
else
{
lean_dec(v_a_3531_);
return v_b_3532_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object* v_s_3545_, lean_object* v_a_3546_, lean_object* v_b_3547_){
_start:
{
uint8_t v_b_boxed_3548_; uint8_t v_res_3549_; lean_object* v_r_3550_; 
v_b_boxed_3548_ = lean_unbox(v_b_3547_);
v_res_3549_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3545_, v_a_3546_, v_b_boxed_3548_);
lean_dec_ref(v_s_3545_);
v_r_3550_ = lean_box(v_res_3549_);
return v_r_3550_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object* v_s_3551_){
_start:
{
lean_object* v_searcher_3552_; uint8_t v___x_3553_; uint8_t v___x_3554_; 
v_searcher_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = 0;
v___x_3554_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3551_, v_searcher_3552_, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v_s_3555_){
_start:
{
uint8_t v_res_3556_; lean_object* v_r_3557_; 
v_res_3556_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v_s_3555_);
lean_dec_ref(v_s_3555_);
v_r_3557_ = lean_box(v_res_3556_);
return v_r_3557_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_3562_ = l_Lean_MessageData_ofFormat(v___x_3561_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_3567_ = l_Lean_MessageData_ofFormat(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3569_ = l_Lean_MessageData_ofFormat(v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3570_, lean_object* v_maxInlineLength_3571_, lean_object* v_ctx_3572_){
_start:
{
lean_object* v_msg_3574_; lean_object* v___x_3575_; uint8_t v___y_3577_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v_msg_3574_ = l_Lean_MessageData_ofExpr(v_e_3570_);
lean_inc_ref(v_msg_3574_);
v___x_3575_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3572_, v_msg_3574_);
v___x_3585_ = lean_string_length(v___x_3575_);
v___x_3586_ = lean_nat_dec_lt(v_maxInlineLength_3571_, v___x_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3587_ = lean_unsigned_to_nat(0u);
v___x_3588_ = lean_string_utf8_byte_size(v___x_3575_);
v___x_3589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3575_);
lean_ctor_set(v___x_3589_, 1, v___x_3587_);
lean_ctor_set(v___x_3589_, 2, v___x_3588_);
v___x_3590_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3589_);
lean_dec_ref(v___x_3589_);
v___y_3577_ = v___x_3590_;
goto v___jp_3576_;
}
else
{
lean_dec_ref(v___x_3575_);
v___y_3577_ = v___x_3586_;
goto v___jp_3576_;
}
v___jp_3576_:
{
if (v___y_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
lean_ctor_set(v___x_3579_, 1, v_msg_3574_);
v___x_3580_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
return v___x_3581_;
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = l_Lean_indentD(v_msg_3574_);
v___x_3583_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3591_, lean_object* v_maxInlineLength_3592_, lean_object* v_ctx_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_inlineExpr___lam__0(v_e_3591_, v_maxInlineLength_3592_, v_ctx_3593_);
lean_dec_ref(v_ctx_3593_);
lean_dec(v_maxInlineLength_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3599_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3600_ = l_Lean_MessageData_ofExpr(v_e_3596_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_inlineExpr___lam__2(v_e_3604_, v_x_3605_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3608_, lean_object* v_maxInlineLength_3609_){
_start:
{
lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; 
lean_inc_ref_n(v_e_3608_, 2);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3610_, 0, v_e_3608_);
lean_closure_set(v___f_3610_, 1, v_maxInlineLength_3609_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3611_, 0, v_e_3608_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3612_, 0, v_e_3608_);
v___x_3613_ = l_Lean_MessageData_lazy(v___f_3610_, v___f_3611_, v___f_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object* v_s_3614_, lean_object* v_inst_3615_, lean_object* v_R_3616_, lean_object* v_a_3617_, uint8_t v_b_3618_, lean_object* v_c_3619_){
_start:
{
uint8_t v___x_3620_; 
v___x_3620_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3614_, v_a_3617_, v_b_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object* v_s_3621_, lean_object* v_inst_3622_, lean_object* v_R_3623_, lean_object* v_a_3624_, lean_object* v_b_3625_, lean_object* v_c_3626_){
_start:
{
uint8_t v_b_boxed_3627_; uint8_t v_res_3628_; lean_object* v_r_3629_; 
v_b_boxed_3627_ = lean_unbox(v_b_3625_);
v_res_3628_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(v_s_3621_, v_inst_3622_, v_R_3623_, v_a_3624_, v_b_boxed_3627_, v_c_3626_);
lean_dec_ref(v_s_3621_);
v_r_3629_ = lean_box(v_res_3628_);
return v_r_3629_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_3634_ = l_Lean_MessageData_ofFormat(v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_3635_, lean_object* v_maxInlineLength_3636_, lean_object* v_ctx_3637_){
_start:
{
lean_object* v_msg_3639_; lean_object* v___x_3640_; uint8_t v___y_3642_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v_msg_3639_ = l_Lean_MessageData_ofExpr(v_e_3635_);
lean_inc_ref(v_msg_3639_);
v___x_3640_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3637_, v_msg_3639_);
v___x_3648_ = lean_string_length(v___x_3640_);
v___x_3649_ = lean_nat_dec_lt(v_maxInlineLength_3636_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = lean_string_utf8_byte_size(v___x_3640_);
v___x_3652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3640_);
lean_ctor_set(v___x_3652_, 1, v___x_3650_);
lean_ctor_set(v___x_3652_, 2, v___x_3651_);
v___x_3653_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3652_);
lean_dec_ref(v___x_3652_);
v___y_3642_ = v___x_3653_;
goto v___jp_3641_;
}
else
{
lean_dec_ref(v___x_3640_);
v___y_3642_ = v___x_3649_;
goto v___jp_3641_;
}
v___jp_3641_:
{
if (v___y_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3643_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v_msg_3639_);
v___x_3645_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
return v___x_3646_;
}
else
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_indentD(v_msg_3639_);
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_3654_, lean_object* v_maxInlineLength_3655_, lean_object* v_ctx_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_inlineExprTrailing___lam__0(v_e_3654_, v_maxInlineLength_3655_, v_ctx_3656_);
lean_dec_ref(v_ctx_3656_);
lean_dec(v_maxInlineLength_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_3659_, lean_object* v_x_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3662_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3663_ = l_Lean_MessageData_ofExpr(v_e_3659_);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_3667_, lean_object* v_x_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_inlineExprTrailing___lam__2(v_e_3667_, v_x_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_3671_, lean_object* v_maxInlineLength_3672_){
_start:
{
lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; 
lean_inc_ref_n(v_e_3671_, 2);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3673_, 0, v_e_3671_);
lean_closure_set(v___f_3673_, 1, v_maxInlineLength_3672_);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3674_, 0, v_e_3671_);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3675_, 0, v_e_3671_);
v___x_3676_ = l_Lean_MessageData_lazy(v___f_3673_, v___f_3674_, v___f_3675_);
return v___x_3676_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_3681_ = l_Lean_MessageData_ofFormat(v___x_3680_);
return v___x_3681_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_3686_ = l_Lean_MessageData_ofFormat(v___x_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3688_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
lean_ctor_set(v___x_3689_, 1, v_msg_3687_);
v___x_3690_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_3692_, lean_object* v_inst_3693_, lean_object* v_msg_3694_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = lean_apply_1(v_inst_3692_, v_msg_3694_);
v___x_3696_ = lean_apply_2(v_inst_3693_, lean_box(0), v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_3697_, lean_object* v_inst_3698_){
_start:
{
lean_object* v___f_3699_; 
v___f_3699_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3699_, 0, v_inst_3698_);
lean_closure_set(v___f_3699_, 1, v_inst_3697_);
return v___f_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_3700_, lean_object* v_n_3701_, lean_object* v_inst_3702_, lean_object* v_inst_3703_){
_start:
{
lean_object* v___f_3704_; 
v___f_3704_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3704_, 0, v_inst_3703_);
lean_closure_set(v___f_3704_, 1, v_inst_3702_);
return v___f_3704_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_unsigned_to_nat(32u);
v___x_3706_ = lean_mk_empty_array_with_capacity(v___x_3705_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3708_ = ((size_t)5ULL);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = lean_unsigned_to_nat(32u);
v___x_3711_ = lean_mk_empty_array_with_capacity(v___x_3710_);
v___x_3712_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_3713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v___x_3711_);
lean_ctor_set(v___x_3713_, 2, v___x_3709_);
lean_ctor_set(v___x_3713_, 3, v___x_3709_);
lean_ctor_set_usize(v___x_3713_, 4, v___x_3708_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3714_ = lean_box(1);
v___x_3715_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_3716_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_3717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___x_3715_);
lean_ctor_set(v___x_3717_, 2, v___x_3714_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_3718_, lean_object* v_msgData_3719_, lean_object* v_toPure_3720_, lean_object* v_opts_3721_){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_3723_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_3724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3724_, 0, v_env_3718_);
lean_ctor_set(v___x_3724_, 1, v___x_3722_);
lean_ctor_set(v___x_3724_, 2, v___x_3723_);
lean_ctor_set(v___x_3724_, 3, v_opts_3721_);
v___x_3725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set(v___x_3725_, 1, v_msgData_3719_);
v___x_3726_ = lean_apply_2(v_toPure_3720_, lean_box(0), v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_3727_, lean_object* v_toPure_3728_, lean_object* v_toBind_3729_, lean_object* v_inst_3730_, lean_object* v_env_3731_){
_start:
{
lean_object* v___f_3732_; lean_object* v___x_3733_; 
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3732_, 0, v_env_3731_);
lean_closure_set(v___f_3732_, 1, v_msgData_3727_);
lean_closure_set(v___f_3732_, 2, v_toPure_3728_);
v___x_3733_ = lean_apply_4(v_toBind_3729_, lean_box(0), lean_box(0), v_inst_3730_, v___f_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_3734_, lean_object* v_inst_3735_, lean_object* v_inst_3736_, lean_object* v_msgData_3737_){
_start:
{
lean_object* v_toApplicative_3738_; lean_object* v_toBind_3739_; lean_object* v_getEnv_3740_; lean_object* v_toPure_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; 
v_toApplicative_3738_ = lean_ctor_get(v_inst_3734_, 0);
lean_inc_ref(v_toApplicative_3738_);
v_toBind_3739_ = lean_ctor_get(v_inst_3734_, 1);
lean_inc_n(v_toBind_3739_, 2);
lean_dec_ref(v_inst_3734_);
v_getEnv_3740_ = lean_ctor_get(v_inst_3735_, 0);
lean_inc(v_getEnv_3740_);
lean_dec_ref(v_inst_3735_);
v_toPure_3741_ = lean_ctor_get(v_toApplicative_3738_, 1);
lean_inc(v_toPure_3741_);
lean_dec_ref(v_toApplicative_3738_);
v___f_3742_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3742_, 0, v_msgData_3737_);
lean_closure_set(v___f_3742_, 1, v_toPure_3741_);
lean_closure_set(v___f_3742_, 2, v_toBind_3739_);
lean_closure_set(v___f_3742_, 3, v_inst_3736_);
v___x_3743_ = lean_apply_4(v_toBind_3739_, lean_box(0), lean_box(0), v_getEnv_3740_, v___f_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_3744_, lean_object* v_inst_3745_, lean_object* v_inst_3746_, lean_object* v_inst_3747_, lean_object* v_msgData_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_addMessageContextPartial___redArg(v_inst_3745_, v_inst_3746_, v_inst_3747_, v_msgData_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_3750_, lean_object* v_mctx_3751_, lean_object* v_lctx_3752_, lean_object* v_msgData_3753_, lean_object* v_toPure_3754_, lean_object* v_opts_3755_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3756_, 0, v_env_3750_);
lean_ctor_set(v___x_3756_, 1, v_mctx_3751_);
lean_ctor_set(v___x_3756_, 2, v_lctx_3752_);
lean_ctor_set(v___x_3756_, 3, v_opts_3755_);
v___x_3757_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v_msgData_3753_);
v___x_3758_ = lean_apply_2(v_toPure_3754_, lean_box(0), v___x_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_3759_, lean_object* v_mctx_3760_, lean_object* v_msgData_3761_, lean_object* v_toPure_3762_, lean_object* v_toBind_3763_, lean_object* v_inst_3764_, lean_object* v_lctx_3765_){
_start:
{
lean_object* v___f_3766_; lean_object* v___x_3767_; 
v___f_3766_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3766_, 0, v_env_3759_);
lean_closure_set(v___f_3766_, 1, v_mctx_3760_);
lean_closure_set(v___f_3766_, 2, v_lctx_3765_);
lean_closure_set(v___f_3766_, 3, v_msgData_3761_);
lean_closure_set(v___f_3766_, 4, v_toPure_3762_);
v___x_3767_ = lean_apply_4(v_toBind_3763_, lean_box(0), lean_box(0), v_inst_3764_, v___f_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_3768_, lean_object* v_msgData_3769_, lean_object* v_toPure_3770_, lean_object* v_toBind_3771_, lean_object* v_inst_3772_, lean_object* v_inst_3773_, lean_object* v_mctx_3774_){
_start:
{
lean_object* v___f_3775_; lean_object* v___x_3776_; 
lean_inc(v_toBind_3771_);
v___f_3775_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3775_, 0, v_env_3768_);
lean_closure_set(v___f_3775_, 1, v_mctx_3774_);
lean_closure_set(v___f_3775_, 2, v_msgData_3769_);
lean_closure_set(v___f_3775_, 3, v_toPure_3770_);
lean_closure_set(v___f_3775_, 4, v_toBind_3771_);
lean_closure_set(v___f_3775_, 5, v_inst_3772_);
v___x_3776_ = lean_apply_4(v_toBind_3771_, lean_box(0), lean_box(0), v_inst_3773_, v___f_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_3777_, lean_object* v_msgData_3778_, lean_object* v_toPure_3779_, lean_object* v_toBind_3780_, lean_object* v_inst_3781_, lean_object* v_inst_3782_, lean_object* v_env_3783_){
_start:
{
lean_object* v_getMCtx_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; 
v_getMCtx_3784_ = lean_ctor_get(v_inst_3777_, 0);
lean_inc(v_getMCtx_3784_);
lean_dec_ref(v_inst_3777_);
lean_inc(v_toBind_3780_);
v___f_3785_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3785_, 0, v_env_3783_);
lean_closure_set(v___f_3785_, 1, v_msgData_3778_);
lean_closure_set(v___f_3785_, 2, v_toPure_3779_);
lean_closure_set(v___f_3785_, 3, v_toBind_3780_);
lean_closure_set(v___f_3785_, 4, v_inst_3781_);
lean_closure_set(v___f_3785_, 5, v_inst_3782_);
v___x_3786_ = lean_apply_4(v_toBind_3780_, lean_box(0), lean_box(0), v_getMCtx_3784_, v___f_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_3787_, lean_object* v_inst_3788_, lean_object* v_inst_3789_, lean_object* v_inst_3790_, lean_object* v_inst_3791_, lean_object* v_msgData_3792_){
_start:
{
lean_object* v_toApplicative_3793_; lean_object* v_toBind_3794_; lean_object* v_getEnv_3795_; lean_object* v_toPure_3796_; lean_object* v___f_3797_; lean_object* v___x_3798_; 
v_toApplicative_3793_ = lean_ctor_get(v_inst_3787_, 0);
lean_inc_ref(v_toApplicative_3793_);
v_toBind_3794_ = lean_ctor_get(v_inst_3787_, 1);
lean_inc_n(v_toBind_3794_, 2);
lean_dec_ref(v_inst_3787_);
v_getEnv_3795_ = lean_ctor_get(v_inst_3788_, 0);
lean_inc(v_getEnv_3795_);
lean_dec_ref(v_inst_3788_);
v_toPure_3796_ = lean_ctor_get(v_toApplicative_3793_, 1);
lean_inc(v_toPure_3796_);
lean_dec_ref(v_toApplicative_3793_);
v___f_3797_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_3797_, 0, v_inst_3789_);
lean_closure_set(v___f_3797_, 1, v_msgData_3792_);
lean_closure_set(v___f_3797_, 2, v_toPure_3796_);
lean_closure_set(v___f_3797_, 3, v_toBind_3794_);
lean_closure_set(v___f_3797_, 4, v_inst_3791_);
lean_closure_set(v___f_3797_, 5, v_inst_3790_);
v___x_3798_ = lean_apply_4(v_toBind_3794_, lean_box(0), lean_box(0), v_getEnv_3795_, v___f_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_3799_, lean_object* v_inst_3800_, lean_object* v_inst_3801_, lean_object* v_inst_3802_, lean_object* v_inst_3803_, lean_object* v_inst_3804_, lean_object* v_msgData_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_addMessageContextFull___redArg(v_inst_3800_, v_inst_3801_, v_inst_3802_, v_inst_3803_, v_inst_3804_, v_msgData_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_3811_);
lean_dec_ref(v_s_3811_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_3813_, lean_object* v___x_3814_, lean_object* v___x_3815_, lean_object* v_a_3816_, lean_object* v_b_3817_){
_start:
{
lean_object* v_it_3819_; lean_object* v_startInclusive_3820_; lean_object* v_endExclusive_3821_; 
if (lean_obj_tag(v_a_3816_) == 0)
{
lean_object* v_currPos_3827_; lean_object* v_searcher_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3854_; 
v_currPos_3827_ = lean_ctor_get(v_a_3816_, 0);
v_searcher_3828_ = lean_ctor_get(v_a_3816_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_a_3816_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3830_ = v_a_3816_;
v_isShared_3831_ = v_isSharedCheck_3854_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_searcher_3828_);
lean_inc(v_currPos_3827_);
lean_dec(v_a_3816_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3854_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_startInclusive_3832_; lean_object* v_endExclusive_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_startInclusive_3832_ = lean_ctor_get(v___x_3814_, 1);
v_endExclusive_3833_ = lean_ctor_get(v___x_3814_, 2);
v___x_3834_ = lean_nat_sub(v_endExclusive_3833_, v_startInclusive_3832_);
v___x_3835_ = lean_nat_dec_eq(v_searcher_3828_, v___x_3834_);
lean_dec(v___x_3834_);
if (v___x_3835_ == 0)
{
uint32_t v___x_3836_; uint32_t v___x_3837_; uint8_t v___x_3838_; 
v___x_3836_ = 10;
v___x_3837_ = lean_string_utf8_get_fast(v_str_3813_, v_searcher_3828_);
v___x_3838_ = lean_uint32_dec_eq(v___x_3837_, v___x_3836_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3839_ = lean_string_utf8_next_fast(v_str_3813_, v_searcher_3828_);
lean_dec(v_searcher_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___x_3839_);
v___x_3841_ = v___x_3830_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_currPos_3827_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
v_a_3816_ = v___x_3841_;
goto _start;
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_slice_3847_; lean_object* v_nextIt_3849_; 
v___x_3844_ = lean_string_utf8_next_fast(v_str_3813_, v_searcher_3828_);
v___x_3845_ = lean_nat_sub(v___x_3844_, v_searcher_3828_);
v___x_3846_ = lean_nat_add(v_searcher_3828_, v___x_3845_);
lean_dec(v___x_3845_);
v_slice_3847_ = l_String_Slice_subslice_x21(v___x_3814_, v_currPos_3827_, v_searcher_3828_);
lean_inc(v___x_3846_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___x_3846_);
lean_ctor_set(v___x_3830_, 0, v___x_3846_);
v_nextIt_3849_ = v___x_3830_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v___x_3846_);
v_nextIt_3849_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v_startInclusive_3850_; lean_object* v_endExclusive_3851_; 
v_startInclusive_3850_ = lean_ctor_get(v_slice_3847_, 0);
lean_inc(v_startInclusive_3850_);
v_endExclusive_3851_ = lean_ctor_get(v_slice_3847_, 1);
lean_inc(v_endExclusive_3851_);
lean_dec_ref(v_slice_3847_);
v_it_3819_ = v_nextIt_3849_;
v_startInclusive_3820_ = v_startInclusive_3850_;
v_endExclusive_3821_ = v_endExclusive_3851_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v___x_3853_; 
lean_del_object(v___x_3830_);
lean_dec(v_searcher_3828_);
v___x_3853_ = lean_box(1);
lean_inc(v___x_3815_);
v_it_3819_ = v___x_3853_;
v_startInclusive_3820_ = v_currPos_3827_;
v_endExclusive_3821_ = v___x_3815_;
goto v___jp_3818_;
}
}
}
else
{
lean_dec(v___x_3815_);
return v_b_3817_;
}
v___jp_3818_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3822_ = lean_string_utf8_extract(v_str_3813_, v_startInclusive_3820_, v_endExclusive_3821_);
lean_dec(v_endExclusive_3821_);
lean_dec(v_startInclusive_3820_);
v___x_3823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
v___x_3824_ = l_Lean_MessageData_ofFormat(v___x_3823_);
v___x_3825_ = lean_array_push(v_b_3817_, v___x_3824_);
v_a_3816_ = v_it_3819_;
v_b_3817_ = v___x_3825_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_3855_, lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v_a_3858_, lean_object* v_b_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3855_, v___x_3856_, v___x_3857_, v_a_3858_, v_b_3859_);
lean_dec_ref(v___x_3856_);
lean_dec_ref(v_str_3855_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_3863_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_lines_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_string_utf8_byte_size(v_str_3863_);
lean_inc_ref(v_str_3863_);
v___x_3866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3866_, 0, v_str_3863_);
lean_ctor_set(v___x_3866_, 1, v___x_3864_);
lean_ctor_set(v___x_3866_, 2, v___x_3865_);
v_lines_3867_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_3869_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3863_, v___x_3866_, v___x_3865_, v_lines_3867_, v___x_3868_);
lean_dec_ref(v___x_3866_);
lean_dec_ref(v_str_3863_);
v___x_3870_ = lean_array_to_list(v___x_3869_);
v___x_3871_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3872_ = l_Lean_MessageData_joinSep(v___x_3870_, v___x_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v_inst_3876_, lean_object* v_R_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3873_, v___x_3874_, v___x_3875_, v_a_3878_, v_b_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_3881_, lean_object* v___x_3882_, lean_object* v___x_3883_, lean_object* v_inst_3884_, lean_object* v_R_3885_, lean_object* v_a_3886_, lean_object* v_b_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_3881_, v___x_3882_, v___x_3883_, v_inst_3884_, v_R_3885_, v_a_3886_, v_b_3887_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v_str_3881_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_3889_){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_3891_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_3891_, 0, lean_box(0));
lean_closure_set(v___x_3891_, 1, lean_box(0));
lean_closure_set(v___x_3891_, 2, lean_box(0));
lean_closure_set(v___x_3891_, 3, v___x_3890_);
lean_closure_set(v___x_3891_, 4, v_inst_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_3892_, lean_object* v_inst_3893_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_3901_){
_start:
{
lean_object* v___f_3902_; 
v___f_3902_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_instToMessageDataTSyntax(v_k_3903_);
lean_dec(v_k_3903_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_3909_, lean_object* v_as_3910_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = lean_box(0);
v___x_3912_ = l_List_mapTR_loop___redArg(v_inst_3909_, v_as_3910_, v___x_3911_);
v___x_3913_ = l_Lean_MessageData_ofList(v___x_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_3914_){
_start:
{
lean_object* v___f_3915_; 
v___f_3915_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3915_, 0, v_inst_3914_);
return v___f_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_3916_, lean_object* v_inst_3917_){
_start:
{
lean_object* v___f_3918_; 
v___f_3918_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3918_, 0, v_inst_3917_);
return v___f_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_3919_, lean_object* v_as_3920_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3921_ = lean_array_to_list(v_as_3920_);
v___x_3922_ = lean_box(0);
v___x_3923_ = l_List_mapTR_loop___redArg(v_inst_3919_, v___x_3921_, v___x_3922_);
v___x_3924_ = l_Lean_MessageData_ofList(v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_3925_){
_start:
{
lean_object* v___f_3926_; 
v___f_3926_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3926_, 0, v_inst_3925_);
return v___f_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_3927_, lean_object* v_inst_3928_){
_start:
{
lean_object* v___f_3929_; 
v___f_3929_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3929_, 0, v_inst_3928_);
return v___f_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_3930_, lean_object* v_acc_3931_, lean_object* v_recur_3932_){
_start:
{
lean_object* v_array_3933_; lean_object* v_start_3934_; lean_object* v_stop_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3948_; 
v_array_3933_ = lean_ctor_get(v_it_3930_, 0);
v_start_3934_ = lean_ctor_get(v_it_3930_, 1);
v_stop_3935_ = lean_ctor_get(v_it_3930_, 2);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_it_3930_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3937_ = v_it_3930_;
v_isShared_3938_ = v_isSharedCheck_3948_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_stop_3935_);
lean_inc(v_start_3934_);
lean_inc(v_array_3933_);
lean_dec(v_it_3930_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3948_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_nat_dec_lt(v_start_3934_, v_stop_3935_);
if (v___x_3939_ == 0)
{
lean_del_object(v___x_3937_);
lean_dec(v_stop_3935_);
lean_dec(v_start_3934_);
lean_dec_ref(v_array_3933_);
lean_dec_ref(v_recur_3932_);
return v_acc_3931_;
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_add(v_start_3934_, v___x_3940_);
lean_inc_ref(v_array_3933_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v___x_3941_);
v___x_3943_ = v___x_3937_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_array_3933_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_stop_3935_);
v___x_3943_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_array_fget(v_array_3933_, v_start_3934_);
lean_dec(v_start_3934_);
lean_dec_ref(v_array_3933_);
v___x_3945_ = lean_array_push(v_acc_3931_, v___x_3944_);
v___x_3946_ = lean_apply_3(v_recur_3932_, v___x_3943_, v___x_3945_, lean_box(0));
return v___x_3946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_3951_, lean_object* v_inst_3952_, lean_object* v_as_3953_){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3954_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_3955_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_3951_, v_as_3953_, v___x_3954_);
v___x_3956_ = lean_array_to_list(v___x_3955_);
v___x_3957_ = lean_box(0);
v___x_3958_ = l_List_mapTR_loop___redArg(v_inst_3952_, v___x_3956_, v___x_3957_);
v___x_3959_ = l_Lean_MessageData_ofList(v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_3961_){
_start:
{
lean_object* v___f_3962_; lean_object* v___f_3963_; 
v___f_3962_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_3963_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3963_, 0, v___f_3962_);
lean_closure_set(v___f_3963_, 1, v_inst_3961_);
return v___f_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_3964_, lean_object* v_inst_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_3965_);
return v___x_3966_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_3971_ = l_Lean_MessageData_ofFormat(v___x_3970_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_3975_ = l_Lean_MessageData_ofFormat(v___x_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_3976_, lean_object* v_x_3977_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 0)
{
lean_object* v___x_3978_; 
lean_dec_ref(v_inst_3976_);
v___x_3978_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_3978_;
}
else
{
lean_object* v_val_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_val_3979_ = lean_ctor_get(v_x_3977_, 0);
lean_inc(v_val_3979_);
lean_dec_ref(v_x_3977_);
v___x_3980_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_3981_ = lean_apply_1(v_inst_3976_, v_val_3979_);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
return v___x_3984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_3985_){
_start:
{
lean_object* v___f_3986_; 
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3986_, 0, v_inst_3985_);
return v___f_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_3987_, lean_object* v_inst_3988_){
_start:
{
lean_object* v___f_3989_; 
v___f_3989_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3989_, 0, v_inst_3988_);
return v___f_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_3990_, lean_object* v_inst_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v_fst_3993_; lean_object* v_snd_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4008_; 
v_fst_3993_ = lean_ctor_get(v_x_3992_, 0);
v_snd_3994_ = lean_ctor_get(v_x_3992_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_x_3992_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3996_ = v_x_3992_;
v_isShared_3997_ = v_isSharedCheck_4008_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_snd_3994_);
lean_inc(v_fst_3993_);
lean_dec(v_x_3992_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4008_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3998_ = lean_apply_1(v_inst_3990_, v_fst_3993_);
v___x_3999_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_3997_ == 0)
{
lean_ctor_set_tag(v___x_3996_, 7);
lean_ctor_set(v___x_3996_, 1, v___x_3999_);
lean_ctor_set(v___x_3996_, 0, v___x_3998_);
v___x_4001_ = v___x_3996_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4002_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = lean_apply_1(v_inst_3991_, v_snd_3994_);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = l_Lean_MessageData_paren(v___x_4005_);
return v___x_4006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4009_, lean_object* v_inst_4010_){
_start:
{
lean_object* v___f_4011_; 
v___f_4011_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4011_, 0, v_inst_4009_);
lean_closure_set(v___f_4011_, 1, v_inst_4010_);
return v___f_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4012_, lean_object* v_00_u03b2_4013_, lean_object* v_inst_4014_, lean_object* v_inst_4015_){
_start:
{
lean_object* v___f_4016_; 
v___f_4016_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4016_, 0, v_inst_4014_);
lean_closure_set(v___f_4016_, 1, v_inst_4015_);
return v___f_4016_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4021_ = l_Lean_MessageData_ofFormat(v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4022_){
_start:
{
if (lean_obj_tag(v_x_4022_) == 0)
{
lean_object* v___x_4023_; 
v___x_4023_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4023_;
}
else
{
lean_object* v_val_4024_; lean_object* v___x_4025_; 
v_val_4024_ = lean_ctor_get(v_x_4022_, 0);
lean_inc(v_val_4024_);
lean_dec_ref(v_x_4022_);
v___x_4025_ = l_Lean_MessageData_ofExpr(v_val_4024_);
return v___x_4025_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
v___x_4060_ = l_String_toRawSubstring_x27(v___x_4059_);
return v___x_4060_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4076_ = l_String_toRawSubstring_x27(v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4093_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4090_);
v___x_4094_ = l_Lean_Syntax_isOfKind(v_x_4090_, v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v_x_4090_);
v___x_4095_ = lean_box(1);
v___x_4096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v_a_4092_);
return v___x_4096_;
}
else
{
lean_object* v_quotContext_4097_; lean_object* v_currMacroScope_4098_; lean_object* v_ref_4099_; lean_object* v___x_4100_; lean_object* v_interpStr_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_quotContext_4097_ = lean_ctor_get(v_a_4091_, 1);
v_currMacroScope_4098_ = lean_ctor_get(v_a_4091_, 2);
v_ref_4099_ = lean_ctor_get(v_a_4091_, 5);
v___x_4100_ = lean_unsigned_to_nat(1u);
v_interpStr_4101_ = l_Lean_Syntax_getArg(v_x_4090_, v___x_4100_);
lean_dec(v_x_4090_);
v___x_4102_ = 0;
v___x_4103_ = l_Lean_SourceInfo_fromRef(v_ref_4099_, v___x_4102_);
v___x_4104_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4105_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4098_, 2);
lean_inc_n(v_quotContext_4097_, 2);
v___x_4106_ = l_Lean_addMacroScope(v_quotContext_4097_, v___x_4105_, v_currMacroScope_4098_);
v___x_4107_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4103_);
v___x_4108_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4103_);
lean_ctor_set(v___x_4108_, 1, v___x_4104_);
lean_ctor_set(v___x_4108_, 2, v___x_4106_);
lean_ctor_set(v___x_4108_, 3, v___x_4107_);
v___x_4109_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4110_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4111_ = l_Lean_addMacroScope(v_quotContext_4097_, v___x_4110_, v_currMacroScope_4098_);
v___x_4112_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4103_);
lean_ctor_set(v___x_4113_, 1, v___x_4109_);
lean_ctor_set(v___x_4113_, 2, v___x_4111_);
lean_ctor_set(v___x_4113_, 3, v___x_4112_);
lean_inc_ref(v___x_4113_);
v___x_4114_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4101_, v___x_4108_, v___x_4113_, v___x_4113_, v_a_4091_, v_a_4092_);
lean_dec(v_interpStr_4101_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
v_a_4116_ = lean_ctor_get(v___x_4114_, 1);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4114_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_inc(v_a_4115_);
lean_dec(v___x_4114_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4115_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
v_a_4124_ = lean_ctor_get(v___x_4114_, 0);
v_a_4125_ = lean_ctor_get(v___x_4114_, 1);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4114_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_inc(v_a_4124_);
lean_dec(v___x_4114_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4124_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4133_, v_a_4134_, v_a_4135_);
lean_dec_ref(v_a_4134_);
return v_res_4136_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4139_ = l_Lean_stringToMessageData(v___x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4140_){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4141_ = lean_array_to_list(v_msgs_4140_);
v___x_4142_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4143_ = l_Lean_MessageData_joinSep(v___x_4141_, v___x_4142_);
v___x_4144_ = l_Lean_indentD(v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4145_, lean_object* v_lctx_4146_, lean_object* v_opts_4147_, lean_object* v_msg_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = lean_elab_environment_of_kernel_env(v_env_4145_);
v___x_4150_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
lean_ctor_set(v___x_4151_, 2, v_lctx_4146_);
lean_ctor_set(v___x_4151_, 3, v_opts_4147_);
v___x_4152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
lean_ctor_set(v___x_4152_, 1, v_msg_4148_);
return v___x_4152_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4155_ = l_Lean_stringToMessageData(v___x_4154_);
return v___x_4155_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
return v___x_4158_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4161_ = l_Lean_stringToMessageData(v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4162_, lean_object* v_n_4163_, lean_object* v_expectedType_4164_){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4165_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4166_ = l_Lean_MessageData_ofName(v_n_4163_);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4167_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = l_Lean_indentExpr(v_givenType_4162_);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4171_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = l_Lean_indentExpr(v_expectedType_4164_);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
return v___x_4175_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4179_ = lean_box(1);
v___x_4180_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4181_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___x_4180_);
lean_ctor_set(v___x_4182_, 2, v___x_4179_);
return v___x_4182_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4185_ = l_Lean_stringToMessageData(v___x_4184_);
return v___x_4185_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4188_ = l_Lean_stringToMessageData(v___x_4187_);
return v___x_4188_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4196_ = l_Lean_MessageData_ofFormat(v___x_4195_);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4199_ = l_Lean_stringToMessageData(v___x_4198_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4202_ = l_Lean_stringToMessageData(v___x_4201_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4205_ = l_Lean_stringToMessageData(v___x_4204_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4211_ = l_Lean_stringToMessageData(v___x_4210_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4214_ = l_Lean_stringToMessageData(v___x_4213_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4217_ = l_Lean_stringToMessageData(v___x_4216_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4220_ = l_Lean_stringToMessageData(v___x_4219_);
return v___x_4220_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4223_ = l_Lean_stringToMessageData(v___x_4222_);
return v___x_4223_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4226_ = l_Lean_stringToMessageData(v___x_4225_);
return v___x_4226_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4229_ = l_Lean_stringToMessageData(v___x_4228_);
return v___x_4229_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4232_ = l_Lean_stringToMessageData(v___x_4231_);
return v___x_4232_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4235_ = l_Lean_stringToMessageData(v___x_4234_);
return v___x_4235_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4238_ = l_Lean_stringToMessageData(v___x_4237_);
return v___x_4238_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4243_ = l_Lean_MessageData_ofFormat(v___x_4242_);
return v___x_4243_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4248_ = l_Lean_MessageData_ofFormat(v___x_4247_);
return v___x_4248_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4253_ = l_Lean_MessageData_ofFormat(v___x_4252_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4258_ = l_Lean_MessageData_ofFormat(v___x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4259_, lean_object* v_opts_4260_){
_start:
{
switch(lean_obj_tag(v_e_4259_))
{
case 0:
{
lean_object* v_env_4261_; lean_object* v_name_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4275_; 
v_env_4261_ = lean_ctor_get(v_e_4259_, 0);
v_name_4262_ = lean_ctor_get(v_e_4259_, 1);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_e_4259_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4264_ = v_e_4259_;
v_isShared_4265_ = v_isSharedCheck_4275_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_name_4262_);
lean_inc(v_env_4261_);
lean_dec(v_e_4259_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4275_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4266_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4267_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4268_ = l_Lean_MessageData_ofName(v_name_4262_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set_tag(v___x_4264_, 7);
lean_ctor_set(v___x_4264_, 1, v___x_4268_);
lean_ctor_set(v___x_4264_, 0, v___x_4267_);
v___x_4270_ = v___x_4264_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4261_, v___x_4266_, v_opts_4260_, v___x_4272_);
return v___x_4273_;
}
}
}
case 1:
{
lean_object* v_env_4276_; lean_object* v_name_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4291_; 
v_env_4276_ = lean_ctor_get(v_e_4259_, 0);
v_name_4277_ = lean_ctor_get(v_e_4259_, 1);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_e_4259_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4279_ = v_e_4259_;
v_isShared_4280_ = v_isSharedCheck_4291_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_name_4277_);
lean_inc(v_env_4276_);
lean_dec(v_e_4259_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4291_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4281_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4282_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4283_ = 1;
v___x_4284_ = l_Lean_MessageData_ofConstName(v_name_4277_, v___x_4283_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 7);
lean_ctor_set(v___x_4279_, 1, v___x_4284_);
lean_ctor_set(v___x_4279_, 0, v___x_4282_);
v___x_4286_ = v___x_4279_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v___x_4284_);
v___x_4286_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4287_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4276_, v___x_4281_, v_opts_4260_, v___x_4288_);
return v___x_4289_;
}
}
}
case 2:
{
lean_object* v_env_4292_; lean_object* v_decl_4293_; lean_object* v_givenType_4294_; lean_object* v___x_4295_; 
v_env_4292_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4292_);
v_decl_4293_ = lean_ctor_get(v_e_4259_, 1);
lean_inc(v_decl_4293_);
v_givenType_4294_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_givenType_4294_);
lean_dec_ref(v_e_4259_);
v___x_4295_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4293_))
{
case 1:
{
lean_object* v_val_4296_; lean_object* v_toConstantVal_4297_; lean_object* v_name_4298_; lean_object* v_type_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_val_4296_ = lean_ctor_get(v_decl_4293_, 0);
lean_inc_ref(v_val_4296_);
lean_dec_ref(v_decl_4293_);
v_toConstantVal_4297_ = lean_ctor_get(v_val_4296_, 0);
lean_inc_ref(v_toConstantVal_4297_);
lean_dec_ref(v_val_4296_);
v_name_4298_ = lean_ctor_get(v_toConstantVal_4297_, 0);
lean_inc(v_name_4298_);
v_type_4299_ = lean_ctor_get(v_toConstantVal_4297_, 2);
lean_inc_ref(v_type_4299_);
lean_dec_ref(v_toConstantVal_4297_);
v___x_4300_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4294_, v_name_4298_, v_type_4299_);
v___x_4301_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4292_, v___x_4295_, v_opts_4260_, v___x_4300_);
return v___x_4301_;
}
case 2:
{
lean_object* v_val_4302_; lean_object* v_toConstantVal_4303_; lean_object* v_name_4304_; lean_object* v_type_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_val_4302_ = lean_ctor_get(v_decl_4293_, 0);
lean_inc_ref(v_val_4302_);
lean_dec_ref(v_decl_4293_);
v_toConstantVal_4303_ = lean_ctor_get(v_val_4302_, 0);
lean_inc_ref(v_toConstantVal_4303_);
lean_dec_ref(v_val_4302_);
v_name_4304_ = lean_ctor_get(v_toConstantVal_4303_, 0);
lean_inc(v_name_4304_);
v_type_4305_ = lean_ctor_get(v_toConstantVal_4303_, 2);
lean_inc_ref(v_type_4305_);
lean_dec_ref(v_toConstantVal_4303_);
v___x_4306_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4294_, v_name_4304_, v_type_4305_);
v___x_4307_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4292_, v___x_4295_, v_opts_4260_, v___x_4306_);
return v___x_4307_;
}
default: 
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_dec_ref(v_givenType_4294_);
lean_dec(v_decl_4293_);
v___x_4308_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4309_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4292_, v___x_4295_, v_opts_4260_, v___x_4308_);
return v___x_4309_;
}
}
}
case 3:
{
lean_object* v_env_4310_; lean_object* v_name_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_env_4310_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4310_);
v_name_4311_ = lean_ctor_get(v_e_4259_, 1);
lean_inc(v_name_4311_);
lean_dec_ref(v_e_4259_);
v___x_4312_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4313_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4314_ = 1;
v___x_4315_ = l_Lean_MessageData_ofConstName(v_name_4311_, v___x_4314_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4313_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4310_, v___x_4312_, v_opts_4260_, v___x_4318_);
return v___x_4319_;
}
case 4:
{
lean_object* v_env_4320_; lean_object* v_name_4321_; lean_object* v_expr_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_env_4320_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4320_);
v_name_4321_ = lean_ctor_get(v_e_4259_, 1);
lean_inc(v_name_4321_);
v_expr_4322_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_expr_4322_);
lean_dec_ref(v_e_4259_);
v___x_4323_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4324_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4325_ = 1;
v___x_4326_ = l_Lean_MessageData_ofConstName(v_name_4321_, v___x_4325_);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4324_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = l_Lean_indentExpr(v_expr_4322_);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4320_, v___x_4323_, v_opts_4260_, v___x_4331_);
return v___x_4332_;
}
case 5:
{
lean_object* v_env_4333_; lean_object* v_lctx_4334_; lean_object* v_expr_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v_env_4333_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4333_);
v_lctx_4334_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4334_);
v_expr_4335_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_expr_4335_);
lean_dec_ref(v_e_4259_);
v___x_4336_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4337_ = l_Lean_indentExpr(v_expr_4335_);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4333_, v_lctx_4334_, v_opts_4260_, v___x_4338_);
return v___x_4339_;
}
case 6:
{
lean_object* v_env_4340_; lean_object* v_lctx_4341_; lean_object* v_expr_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_env_4340_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4340_);
v_lctx_4341_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4341_);
v_expr_4342_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_expr_4342_);
lean_dec_ref(v_e_4259_);
v___x_4343_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4344_ = l_Lean_indentExpr(v_expr_4342_);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4343_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4340_, v_lctx_4341_, v_opts_4260_, v___x_4345_);
return v___x_4346_;
}
case 7:
{
lean_object* v_env_4347_; lean_object* v_lctx_4348_; lean_object* v_name_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_env_4347_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4347_);
v_lctx_4348_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4348_);
v_name_4349_ = lean_ctor_get(v_e_4259_, 2);
lean_inc(v_name_4349_);
lean_dec_ref(v_e_4259_);
v___x_4350_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4351_ = l_Lean_MessageData_ofName(v_name_4349_);
v___x_4352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4350_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
v___x_4353_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4352_);
lean_ctor_set(v___x_4354_, 1, v___x_4353_);
v___x_4355_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4347_, v_lctx_4348_, v_opts_4260_, v___x_4354_);
return v___x_4355_;
}
case 8:
{
lean_object* v_env_4356_; lean_object* v_lctx_4357_; lean_object* v_expr_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_env_4356_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4356_);
v_lctx_4357_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4357_);
v_expr_4358_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_expr_4358_);
lean_dec_ref(v_e_4259_);
v___x_4359_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4360_ = l_Lean_indentExpr(v_expr_4358_);
v___x_4361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4359_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4356_, v_lctx_4357_, v_opts_4260_, v___x_4361_);
return v___x_4362_;
}
case 9:
{
lean_object* v_env_4363_; lean_object* v_lctx_4364_; lean_object* v_app_4365_; lean_object* v_funType_4366_; lean_object* v_argType_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v_env_4363_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4363_);
v_lctx_4364_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4364_);
v_app_4365_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_app_4365_);
v_funType_4366_ = lean_ctor_get(v_e_4259_, 3);
lean_inc_ref(v_funType_4366_);
v_argType_4367_ = lean_ctor_get(v_e_4259_, 4);
lean_inc_ref(v_argType_4367_);
lean_dec_ref(v_e_4259_);
v___x_4368_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4369_ = l_Lean_indentExpr(v_app_4365_);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = l_Lean_indentExpr(v_argType_4367_);
v___x_4374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = l_Lean_indentExpr(v_funType_4366_);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4363_, v_lctx_4364_, v_opts_4260_, v___x_4378_);
return v___x_4379_;
}
case 10:
{
lean_object* v_env_4380_; lean_object* v_lctx_4381_; lean_object* v_proj_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_env_4380_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4380_);
v_lctx_4381_ = lean_ctor_get(v_e_4259_, 1);
lean_inc_ref(v_lctx_4381_);
v_proj_4382_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_proj_4382_);
lean_dec_ref(v_e_4259_);
v___x_4383_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4384_ = l_Lean_indentExpr(v_proj_4382_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4380_, v_lctx_4381_, v_opts_4260_, v___x_4385_);
return v___x_4386_;
}
case 11:
{
lean_object* v_env_4387_; lean_object* v_name_4388_; lean_object* v_type_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_env_4387_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_env_4387_);
v_name_4388_ = lean_ctor_get(v_e_4259_, 1);
lean_inc(v_name_4388_);
v_type_4389_ = lean_ctor_get(v_e_4259_, 2);
lean_inc_ref(v_type_4389_);
lean_dec_ref(v_e_4259_);
v___x_4390_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4391_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4392_ = 1;
v___x_4393_ = l_Lean_MessageData_ofConstName(v_name_4388_, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4391_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = l_Lean_indentExpr(v_type_4389_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4387_, v___x_4390_, v_opts_4260_, v___x_4398_);
return v___x_4399_;
}
case 12:
{
lean_object* v_msg_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
lean_dec_ref(v_opts_4260_);
v_msg_4400_ = lean_ctor_get(v_e_4259_, 0);
lean_inc_ref(v_msg_4400_);
lean_dec_ref(v_e_4259_);
v___x_4401_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4402_ = l_Lean_stringToMessageData(v_msg_4400_);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4401_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
return v___x_4403_;
}
case 13:
{
lean_object* v___x_4404_; 
lean_dec_ref(v_opts_4260_);
v___x_4404_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4404_;
}
case 14:
{
lean_object* v___x_4405_; 
lean_dec_ref(v_opts_4260_);
v___x_4405_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4405_;
}
case 15:
{
lean_object* v___x_4406_; 
lean_dec_ref(v_opts_4260_);
v___x_4406_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4406_;
}
default: 
{
lean_object* v___x_4407_; 
lean_dec_ref(v_opts_4260_);
v___x_4407_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4408_, lean_object* v_e_4409_, lean_object* v_cls_4410_){
_start:
{
lean_object* v___x_4411_; double v___x_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4411_ = lean_box(0);
v___x_4412_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4413_ = 1;
v___x_4414_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4415_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4415_, 0, v_cls_4410_);
lean_ctor_set(v___x_4415_, 1, v___x_4411_);
lean_ctor_set(v___x_4415_, 2, v___x_4414_);
lean_ctor_set_float(v___x_4415_, sizeof(void*)*3, v___x_4412_);
lean_ctor_set_float(v___x_4415_, sizeof(void*)*3 + 8, v___x_4412_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*3 + 16, v___x_4413_);
v___x_4416_ = lean_apply_1(v_inst_4408_, v_e_4409_);
v___x_4417_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4418_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4415_);
lean_ctor_set(v___x_4418_, 1, v___x_4416_);
lean_ctor_set(v___x_4418_, 2, v___x_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4419_, lean_object* v_inst_4420_, lean_object* v_e_4421_, lean_object* v_cls_4422_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_toTraceElem___redArg(v_inst_4420_, v_e_4421_, v_cls_4422_);
return v___x_4423_;
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
