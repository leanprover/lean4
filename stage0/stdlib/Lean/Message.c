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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_43_ = lean_string_append(v___y_40_, v___y_42_);
lean_dec_ref(v___y_42_);
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
lean_inc(v_val_51_);
lean_dec_ref(v_kind_11_);
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
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1(lean_object* v___x_729_, lean_object* v_l_730_, lean_object* v_ctx_x3f_731_){
_start:
{
lean_object* v_val_734_; 
if (lean_obj_tag(v_ctx_x3f_731_) == 0)
{
uint8_t v___x_737_; lean_object* v___x_738_; 
v___x_737_ = 1;
v___x_738_ = l_Lean_Level_format(v_l_730_, v___x_737_);
v_val_734_ = v___x_738_;
goto v___jp_733_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_740_; 
v_val_739_ = lean_ctor_get(v_ctx_x3f_731_, 0);
lean_inc(v_val_739_);
lean_dec_ref(v_ctx_x3f_731_);
v___x_740_ = l_Lean_ppLevel(v_val_739_, v_l_730_);
v_val_734_ = v___x_740_;
goto v___jp_733_;
}
v___jp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = l_Lean_MessageData_ofFormat(v_val_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_729_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__1___boxed(lean_object* v___x_741_, lean_object* v_l_742_, lean_object* v_ctx_x3f_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MessageData_ofLevel___lam__1(v___x_741_, v_l_742_, v_ctx_x3f_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v___f_747_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_748_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
v___f_749_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__1___boxed), 4, 2);
lean_closure_set(v___f_749_, 0, v___x_748_);
lean_closure_set(v___f_749_, 1, v_l_746_);
v___x_750_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_750_, 0, v___f_749_);
lean_ctor_set(v___x_750_, 1, v___f_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_751_){
_start:
{
uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = 1;
v___x_753_ = l_Lean_Name_toString(v_n_751_, v___x_752_);
v___x_754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = l_Lean_MessageData_ofFormat(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_759_, lean_object* v_k_760_, uint8_t v_v_761_){
_start:
{
lean_object* v_map_762_; uint8_t v_hasTrace_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_777_; 
v_map_762_ = lean_ctor_get(v_o_759_, 0);
v_hasTrace_763_ = lean_ctor_get_uint8(v_o_759_, sizeof(void*)*1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_o_759_);
if (v_isSharedCheck_777_ == 0)
{
v___x_765_ = v_o_759_;
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_map_762_);
lean_dec(v_o_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_767_, 0, v_v_761_);
lean_inc(v_k_760_);
v___x_768_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_760_, v___x_767_, v_map_762_);
if (v_hasTrace_763_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_772_; 
v___x_769_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_770_ = l_Lean_Name_isPrefixOf(v___x_769_, v_k_760_);
lean_dec(v_k_760_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_768_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_770_);
return v___x_772_;
}
}
else
{
lean_object* v___x_775_; 
lean_dec(v_k_760_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*1, v_hasTrace_763_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_778_, lean_object* v_k_779_, lean_object* v_v_780_){
_start:
{
uint8_t v_v_boxed_781_; lean_object* v_res_782_; 
v_v_boxed_781_ = lean_unbox(v_v_780_);
v_res_782_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_778_, v_k_779_, v_v_boxed_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_788_, lean_object* v_constName_789_, uint8_t v_fullNames_790_, lean_object* v_ctx_x3f_791_){
_start:
{
lean_object* v_val_794_; lean_object* v___y_798_; 
if (lean_obj_tag(v_ctx_x3f_791_) == 0)
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_799_ = 1;
v___x_800_ = l_Lean_Name_toString(v_constName_789_, v___x_799_);
v___x_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_box(1);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v_val_794_ = v___x_803_;
goto v___jp_793_;
}
else
{
if (v_fullNames_790_ == 0)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v_ctx_x3f_791_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v_ctx_x3f_791_);
v___x_805_ = l_Lean_ppConstNameWithInfos(v_val_804_, v_constName_789_);
v___y_798_ = v___x_805_;
goto v___jp_797_;
}
else
{
lean_object* v_val_806_; lean_object* v_env_807_; lean_object* v_mctx_808_; lean_object* v_lctx_809_; lean_object* v_opts_810_; lean_object* v_currNamespace_811_; lean_object* v_openDecls_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
v_val_806_ = lean_ctor_get(v_ctx_x3f_791_, 0);
lean_inc(v_val_806_);
lean_dec_ref(v_ctx_x3f_791_);
v_env_807_ = lean_ctor_get(v_val_806_, 0);
v_mctx_808_ = lean_ctor_get(v_val_806_, 1);
v_lctx_809_ = lean_ctor_get(v_val_806_, 2);
v_opts_810_ = lean_ctor_get(v_val_806_, 3);
v_currNamespace_811_ = lean_ctor_get(v_val_806_, 4);
v_openDecls_812_ = lean_ctor_get(v_val_806_, 5);
v_isSharedCheck_822_ = !lean_is_exclusive(v_val_806_);
if (v_isSharedCheck_822_ == 0)
{
v___x_814_ = v_val_806_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_openDecls_812_);
lean_inc(v_currNamespace_811_);
lean_inc(v_opts_810_);
lean_inc(v_lctx_809_);
lean_inc(v_mctx_808_);
lean_inc(v_env_807_);
lean_dec(v_val_806_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_817_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_810_, v___x_816_, v_fullNames_790_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 3, v___x_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_env_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_mctx_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_lctx_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_currNamespace_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 5, v_openDecls_812_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_ppConstNameWithInfos(v___x_819_, v_constName_789_);
v___y_798_ = v___x_820_;
goto v___jp_797_;
}
}
}
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_val_794_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_788_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
return v___x_796_;
}
v___jp_797_:
{
v_val_794_ = v___y_798_;
goto v___jp_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_823_, lean_object* v_constName_824_, lean_object* v_fullNames_825_, lean_object* v_ctx_x3f_826_, lean_object* v___y_827_){
_start:
{
uint8_t v_fullNames_boxed_828_; lean_object* v_res_829_; 
v_fullNames_boxed_828_ = lean_unbox(v_fullNames_825_);
v_res_829_ = l_Lean_MessageData_ofConstName___lam__1(v___x_823_, v_constName_824_, v_fullNames_boxed_828_, v_ctx_x3f_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_830_, uint8_t v_fullNames_831_){
_start:
{
lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
v___f_832_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_833_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
v___x_834_ = lean_box(v_fullNames_831_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_835_, 0, v___x_833_);
lean_closure_set(v___f_835_, 1, v_constName_830_);
lean_closure_set(v___f_835_, 2, v___x_834_);
v___x_836_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_836_, 0, v___f_835_);
lean_ctor_set(v___x_836_, 1, v___f_832_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_837_, lean_object* v_fullNames_838_){
_start:
{
uint8_t v_fullNames_boxed_839_; lean_object* v_res_840_; 
v_fullNames_boxed_839_ = lean_unbox(v_fullNames_838_);
v_res_840_ = l_Lean_MessageData_ofConstName(v_constName_837_, v_fullNames_boxed_839_);
return v_res_840_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
lean_ctor_set(v___x_846_, 2, v___x_845_);
lean_ctor_set(v___x_846_, 3, v___x_844_);
lean_ctor_set(v___x_846_, 4, v___x_844_);
lean_ctor_set(v___x_846_, 5, v___x_844_);
lean_ctor_set(v___x_846_, 6, v___x_844_);
lean_ctor_set(v___x_846_, 7, v___x_844_);
lean_ctor_set(v___x_846_, 8, v___x_844_);
return v___x_846_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_847_, lean_object* v_a_848_){
_start:
{
switch(lean_obj_tag(v_a_848_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_847_) == 0)
{
lean_object* v_hasSyntheticSorry_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_hasSyntheticSorry_849_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_hasSyntheticSorry_849_);
lean_dec_ref(v_a_848_);
v___x_850_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_851_ = lean_apply_1(v_hasSyntheticSorry_849_, v___x_850_);
v___x_852_ = lean_unbox(v___x_851_);
return v___x_852_;
}
else
{
lean_object* v_hasSyntheticSorry_853_; lean_object* v_val_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_hasSyntheticSorry_853_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_hasSyntheticSorry_853_);
lean_dec_ref(v_a_848_);
v_val_854_ = lean_ctor_get(v_mctx_x3f_847_, 0);
lean_inc(v_val_854_);
lean_dec_ref(v_mctx_x3f_847_);
v___x_855_ = lean_apply_1(v_hasSyntheticSorry_853_, v_val_854_);
v___x_856_ = lean_unbox(v___x_855_);
return v___x_856_;
}
}
case 3:
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v_mctx_859_; lean_object* v___x_860_; 
lean_dec(v_mctx_x3f_847_);
v_a_857_ = lean_ctor_get(v_a_848_, 0);
lean_inc_ref(v_a_857_);
v_a_858_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_a_858_);
lean_dec_ref(v_a_848_);
v_mctx_859_ = lean_ctor_get(v_a_857_, 1);
lean_inc_ref(v_mctx_859_);
lean_dec_ref(v_a_857_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_mctx_859_);
v_mctx_x3f_847_ = v___x_860_;
v_a_848_ = v_a_858_;
goto _start;
}
case 4:
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_a_862_);
lean_dec_ref(v_a_848_);
v_a_848_ = v_a_862_;
goto _start;
}
case 5:
{
lean_object* v_a_864_; 
v_a_864_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_a_864_);
lean_dec_ref(v_a_848_);
v_a_848_ = v_a_864_;
goto _start;
}
case 6:
{
lean_object* v_a_866_; 
v_a_866_ = lean_ctor_get(v_a_848_, 0);
lean_inc_ref(v_a_866_);
lean_dec_ref(v_a_848_);
v_a_848_ = v_a_866_;
goto _start;
}
case 7:
{
lean_object* v_a_868_; lean_object* v_a_869_; uint8_t v___x_870_; 
v_a_868_ = lean_ctor_get(v_a_848_, 0);
lean_inc_ref(v_a_868_);
v_a_869_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_a_869_);
lean_dec_ref(v_a_848_);
lean_inc(v_mctx_x3f_847_);
v___x_870_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_847_, v_a_868_);
if (v___x_870_ == 0)
{
v_a_848_ = v_a_869_;
goto _start;
}
else
{
lean_dec_ref(v_a_869_);
lean_dec(v_mctx_x3f_847_);
return v___x_870_;
}
}
case 8:
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_a_872_);
lean_dec_ref(v_a_848_);
v_a_848_ = v_a_872_;
goto _start;
}
case 9:
{
lean_object* v_msg_874_; lean_object* v_children_875_; uint8_t v___x_876_; 
v_msg_874_ = lean_ctor_get(v_a_848_, 1);
lean_inc_ref(v_msg_874_);
v_children_875_ = lean_ctor_get(v_a_848_, 2);
lean_inc_ref(v_children_875_);
lean_dec_ref(v_a_848_);
lean_inc(v_mctx_x3f_847_);
v___x_876_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_847_, v_msg_874_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_children_875_);
v___x_879_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_children_875_);
lean_dec(v_mctx_x3f_847_);
return v___x_876_;
}
else
{
if (v___x_879_ == 0)
{
lean_dec_ref(v_children_875_);
lean_dec(v_mctx_x3f_847_);
return v___x_876_;
}
else
{
size_t v___x_880_; size_t v___x_881_; uint8_t v___x_882_; 
v___x_880_ = ((size_t)0ULL);
v___x_881_ = lean_usize_of_nat(v___x_878_);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_847_, v_children_875_, v___x_880_, v___x_881_);
lean_dec_ref(v_children_875_);
return v___x_882_;
}
}
}
else
{
lean_dec_ref(v_children_875_);
lean_dec(v_mctx_x3f_847_);
return v___x_876_;
}
}
default: 
{
uint8_t v___x_883_; 
lean_dec_ref(v_a_848_);
lean_dec(v_mctx_x3f_847_);
v___x_883_ = 0;
return v___x_883_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_884_, lean_object* v_as_885_, size_t v_i_886_, size_t v_stop_887_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_eq(v_i_886_, v_stop_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_uget_borrowed(v_as_885_, v_i_886_);
lean_inc(v___x_889_);
lean_inc(v_mctx_x3f_884_);
v___x_890_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_884_, v___x_889_);
if (v___x_890_ == 0)
{
size_t v___x_891_; size_t v___x_892_; 
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_886_, v___x_891_);
v_i_886_ = v___x_892_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_884_);
return v___x_890_;
}
}
else
{
uint8_t v___x_894_; 
lean_dec(v_mctx_x3f_884_);
v___x_894_ = 0;
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_895_, lean_object* v_as_896_, lean_object* v_i_897_, lean_object* v_stop_898_){
_start:
{
size_t v_i_boxed_899_; size_t v_stop_boxed_900_; uint8_t v_res_901_; lean_object* v_r_902_; 
v_i_boxed_899_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_stop_boxed_900_ = lean_unbox_usize(v_stop_898_);
lean_dec(v_stop_898_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_895_, v_as_896_, v_i_boxed_899_, v_stop_boxed_900_);
lean_dec_ref(v_as_896_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_903_, lean_object* v_a_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_903_, v_a_904_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_907_){
_start:
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = lean_box(0);
v___x_909_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_908_, v_msg_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_910_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_913_, lean_object* v_decl_914_, lean_object* v_ref_915_){
_start:
{
lean_object* v_defValue_917_; lean_object* v_descr_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_944_; 
v_defValue_917_ = lean_ctor_get(v_decl_914_, 0);
v_descr_918_ = lean_ctor_get(v_decl_914_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_decl_914_);
if (v_isSharedCheck_944_ == 0)
{
v___x_920_ = v_decl_914_;
v_isShared_921_ = v_isSharedCheck_944_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_descr_918_);
lean_inc(v_defValue_917_);
lean_dec(v_decl_914_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_944_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_inc(v_defValue_917_);
v___x_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_922_, 0, v_defValue_917_);
lean_inc(v_name_913_);
v___x_923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_923_, 0, v_name_913_);
lean_ctor_set(v___x_923_, 1, v_ref_915_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set(v___x_923_, 3, v_descr_918_);
lean_inc(v_name_913_);
v___x_924_ = lean_register_option(v_name_913_, v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_935_);
v___x_926_ = v___x_924_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_924_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v_defValue_917_);
lean_ctor_set(v___x_920_, 0, v_name_913_);
v___x_929_ = v___x_920_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_name_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_defValue_917_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_del_object(v___x_920_);
lean_dec(v_defValue_917_);
lean_dec(v_name_913_);
v_a_936_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_924_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_924_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_945_, lean_object* v_decl_946_, lean_object* v_ref_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_945_, v_decl_946_, v_ref_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_963_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_964_ = ((lean_object*)(l_Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_965_ = l_Lean_Option_register___at___00Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_962_, v___x_963_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_nat_to_int(v_a_968_);
return v___x_969_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_box(0);
v___x_971_ = l_instMonadBaseIO;
v___x_972_ = l_instInhabitedOfMonad___redArg(v___x_971_, v___x_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_2068__overap_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2068__overap_976_ = lean_panic_fn(v___x_975_, v_msg_973_);
v___x_977_ = lean_apply_1(v___x_2068__overap_976_, lean_box(0));
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_dec(v_x_981_);
return v_x_982_;
}
else
{
lean_object* v_head_984_; lean_object* v_tail_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v_head_984_ = lean_ctor_get(v_x_983_, 0);
v_tail_985_ = lean_ctor_get(v_x_983_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_983_);
if (v_isSharedCheck_994_ == 0)
{
v___x_987_ = v_x_983_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_tail_985_);
lean_inc(v_head_984_);
lean_dec(v_x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
lean_inc(v_x_981_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 5);
lean_ctor_set(v___x_987_, 1, v_x_981_);
lean_ctor_set(v___x_987_, 0, v_x_982_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_x_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_x_981_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v_head_984_);
v_x_982_ = v___x_991_;
v_x_983_ = v_tail_985_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
lean_object* v___x_997_; 
lean_dec(v_x_996_);
v___x_997_ = lean_box(0);
return v___x_997_;
}
else
{
lean_object* v_tail_998_; 
v_tail_998_ = lean_ctor_get(v_x_995_, 1);
if (lean_obj_tag(v_tail_998_) == 0)
{
lean_object* v_head_999_; 
lean_dec(v_x_996_);
v_head_999_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_head_999_);
lean_dec_ref(v_x_995_);
return v_head_999_;
}
else
{
lean_object* v_head_1000_; lean_object* v___x_1001_; 
lean_inc(v_tail_998_);
v_head_1000_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_head_1000_);
lean_dec_ref(v_x_995_);
v___x_1001_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_996_, v_head_1000_, v_tail_998_);
return v___x_1001_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1016_; double v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_float_of_nat(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
switch(lean_obj_tag(v_x_1023_))
{
case 0:
{
lean_object* v_a_1025_; lean_object* v_fmt_1026_; 
lean_dec(v_x_1022_);
lean_dec_ref(v_x_1021_);
v_a_1025_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_a_1025_);
lean_dec_ref(v_x_1023_);
v_fmt_1026_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_fmt_1026_);
lean_dec_ref(v_a_1025_);
return v_fmt_1026_;
}
case 1:
{
if (lean_obj_tag(v_x_1022_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_x_1021_);
v_a_1027_ = lean_ctor_get(v_x_1023_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v_x_1023_);
v___x_1028_ = l_Lean_formatRawGoal(v_a_1027_);
return v___x_1028_;
}
else
{
lean_object* v_a_1029_; lean_object* v_val_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1029_ = lean_ctor_get(v_x_1023_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v_x_1023_);
v_val_1030_ = lean_ctor_get(v_x_1022_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v_x_1022_);
v___x_1031_ = l_Lean_MessageData_mkPPContext(v_x_1021_, v_val_1030_);
lean_dec(v_val_1030_);
lean_dec_ref(v_x_1021_);
v___x_1032_ = l_Lean_ppGoal(v___x_1031_, v_a_1029_);
return v___x_1032_;
}
}
case 3:
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1035_; 
lean_dec(v_x_1022_);
v_a_1033_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_a_1033_);
v_a_1034_ = lean_ctor_get(v_x_1023_, 1);
lean_inc_ref(v_a_1034_);
lean_dec_ref(v_x_1023_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1033_);
v_x_1022_ = v___x_1035_;
v_x_1023_ = v_a_1034_;
goto _start;
}
case 4:
{
lean_object* v_a_1037_; lean_object* v_a_1038_; 
lean_dec_ref(v_x_1021_);
v_a_1037_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_a_1037_);
v_a_1038_ = lean_ctor_get(v_x_1023_, 1);
lean_inc_ref(v_a_1038_);
lean_dec_ref(v_x_1023_);
v_x_1021_ = v_a_1037_;
v_x_1023_ = v_a_1038_;
goto _start;
}
case 5:
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
v_a_1040_ = lean_ctor_get(v_x_1023_, 0);
v_a_1041_ = lean_ctor_get(v_x_1023_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1023_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1043_ = v_x_1023_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_inc(v_a_1040_);
lean_dec(v_x_1023_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = l_Lean_MessageData_formatAux(v_x_1021_, v_x_1022_, v_a_1041_);
v___x_1046_ = lean_nat_to_int(v_a_1040_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 4);
lean_ctor_set(v___x_1043_, 1, v___x_1045_);
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1045_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
case 6:
{
lean_object* v_a_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v_a_1051_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_a_1051_);
lean_dec_ref(v_x_1023_);
v___x_1052_ = l_Lean_MessageData_formatAux(v_x_1021_, v_x_1022_, v_a_1051_);
v___x_1053_ = 0;
v___x_1054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_1053_);
return v___x_1054_;
}
case 7:
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_a_1055_ = lean_ctor_get(v_x_1023_, 0);
v_a_1056_ = lean_ctor_get(v_x_1023_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_1023_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v_x_1023_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_inc(v_a_1055_);
lean_dec(v_x_1023_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_inc(v_x_1022_);
lean_inc_ref(v_x_1021_);
v___x_1060_ = l_Lean_MessageData_formatAux(v_x_1021_, v_x_1022_, v_a_1055_);
v___x_1061_ = l_Lean_MessageData_formatAux(v_x_1021_, v_x_1022_, v_a_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 5);
lean_ctor_set(v___x_1058_, 1, v___x_1061_);
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
case 9:
{
lean_object* v_data_1066_; lean_object* v_msg_1067_; lean_object* v_children_1068_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v_msg_1073_; lean_object* v_cls_1085_; double v_startTime_1086_; double v_stopTime_1087_; uint8_t v___x_1088_; 
v_data_1066_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_data_1066_);
v_msg_1067_ = lean_ctor_get(v_x_1023_, 1);
lean_inc_ref(v_msg_1067_);
v_children_1068_ = lean_ctor_get(v_x_1023_, 2);
lean_inc_ref(v_children_1068_);
lean_dec_ref(v_x_1023_);
v_sz_1069_ = lean_array_size(v_children_1068_);
v___x_1070_ = ((size_t)0ULL);
lean_inc(v_x_1022_);
lean_inc_ref(v_x_1021_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1021_, v_x_1022_, v_sz_1069_, v___x_1070_, v_children_1068_);
v_cls_1085_ = lean_ctor_get(v_data_1066_, 0);
lean_inc(v_cls_1085_);
v_startTime_1086_ = lean_ctor_get_float(v_data_1066_, sizeof(void*)*3);
v_stopTime_1087_ = lean_ctor_get_float(v_data_1066_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1066_);
v___x_1088_ = l_Lean_Name_isAnonymous(v_cls_1085_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; double v___x_1104_; uint8_t v___x_1105_; 
v___x_1089_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1090_ = 1;
v___x_1091_ = l_Lean_Name_toString(v_cls_1085_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1089_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1104_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1105_ = lean_float_beq(v_startTime_1086_, v___x_1104_);
if (v___x_1105_ == 0)
{
goto v___jp_1096_;
}
else
{
if (v___x_1088_ == 0)
{
v_msg_1073_ = v___x_1095_;
goto v___jp_1072_;
}
else
{
goto v___jp_1096_;
}
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; double v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1097_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1095_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_float_sub(v_stopTime_1087_, v_startTime_1086_);
v___x_1100_ = lean_float_to_string(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1098_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1094_);
v_msg_1073_ = v___x_1103_;
goto v___jp_1072_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_cls_1085_);
lean_dec_ref(v_msg_1067_);
lean_dec(v_x_1022_);
lean_dec_ref(v_x_1021_);
v___x_1106_ = lean_array_to_list(v___x_1071_);
v___x_1107_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1108_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1106_, v___x_1107_);
return v___x_1108_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1074_ = l_Lean_MessageData_formatAux(v_x_1021_, v_x_1022_, v_msg_1067_);
v___x_1075_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_msg_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1074_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_array_to_list(v___x_1071_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1083_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1081_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1077_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
return v___x_1084_;
}
}
case 10:
{
lean_object* v_f_1109_; lean_object* v___x_1110_; lean_object* v___y_1112_; 
v_f_1109_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_f_1109_);
lean_dec_ref(v_x_1023_);
v___x_1110_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
if (lean_obj_tag(v_x_1022_) == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_box(0);
v___y_1112_ = v___x_1128_;
goto v___jp_1111_;
}
else
{
lean_object* v_val_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_val_1129_ = lean_ctor_get(v_x_1022_, 0);
v___x_1130_ = l_Lean_MessageData_mkPPContext(v_x_1021_, v_val_1129_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___y_1112_ = v___x_1131_;
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_apply_2(v_f_1109_, v___y_1112_, lean_box(0));
v___x_1114_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1113_, v___x_1110_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; 
lean_dec(v___x_1113_);
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref(v___x_1114_);
v_x_1023_ = v_val_1115_;
goto _start;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v___x_1114_);
lean_dec(v_x_1022_);
lean_dec_ref(v_x_1021_);
v___x_1117_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1118_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1119_ = lean_unsigned_to_nat(330u);
v___x_1120_ = lean_unsigned_to_nat(8u);
v___x_1121_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1122_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1113_);
lean_dec(v___x_1113_);
v___x_1123_ = 1;
v___x_1124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1122_, v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1121_, v___x_1124_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = l_mkPanicMessageWithDecl(v___x_1117_, v___x_1118_, v___x_1119_, v___x_1120_, v___x_1125_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1126_);
return v___x_1127_;
}
}
}
default: 
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v_x_1023_, 1);
lean_inc_ref(v_a_1132_);
lean_dec_ref(v_x_1023_);
v_x_1023_ = v_a_1132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1134_, lean_object* v_x_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_bs_1138_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1140_ == 0)
{
lean_dec(v_x_1135_);
lean_dec_ref(v_x_1134_);
return v_bs_1138_;
}
else
{
lean_object* v_v_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_bs_x27_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v_v_1141_ = lean_array_uget_borrowed(v_bs_1138_, v_i_1137_);
lean_inc(v_v_1141_);
lean_inc(v_x_1135_);
lean_inc_ref(v_x_1134_);
v___x_1142_ = l_Lean_MessageData_formatAux(v_x_1134_, v_x_1135_, v_v_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v_bs_x27_1144_ = lean_array_uset(v_bs_1138_, v_i_1137_, v___x_1143_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1137_, v___x_1145_);
v___x_1147_ = lean_array_uset(v_bs_x27_1144_, v_i_1137_, v___x_1142_);
v_i_1137_ = v___x_1146_;
v_bs_1138_ = v___x_1147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_bs_1153_, lean_object* v___y_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1149_, v_x_1150_, v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_MessageData_formatAux(v_x_1158_, v_x_1159_, v_x_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1166_, lean_object* v_ctx_x3f_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1170_ = l_Lean_MessageData_formatAux(v___x_1169_, v_ctx_x3f_1167_, v_msgData_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1171_, lean_object* v_ctx_x3f_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_MessageData_format(v_msgData_1171_, v_ctx_x3f_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = l_Lean_MessageData_format(v_msgData_1175_, v___x_1177_);
v___x_1179_ = l_Std_Format_defWidth;
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Std_Format_pretty(v___x_1178_, v___x_1179_, v___x_1180_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_MessageData_toString(v_msgData_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1185_);
lean_ctor_set(v___x_1187_, 1, v_a_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_s_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1215_ = l_Lean_MessageData_ofFormat(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1216_){
_start:
{
if (lean_obj_tag(v_o_1216_) == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1217_;
}
else
{
lean_object* v_val_1218_; lean_object* v___x_1219_; 
v_val_1218_ = lean_ctor_get(v_o_1216_, 0);
lean_inc(v_val_1218_);
lean_dec_ref(v_o_1216_);
v___x_1219_ = l_Lean_MessageData_ofExpr(v_val_1218_);
return v___x_1219_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1223_ = l_Lean_MessageData_ofFormat(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1228_ = l_Lean_MessageData_ofFormat(v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1229_, lean_object* v_i_1230_, lean_object* v_acc_1231_){
_start:
{
lean_object* v___y_1233_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_array_get_size(v_es_1229_);
v___x_1238_ = lean_nat_dec_lt(v_i_1230_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_i_1230_);
v___x_1239_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_acc_1231_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v_e_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_e_1241_ = lean_array_fget_borrowed(v_es_1229_, v_i_1230_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_nat_dec_eq(v_i_1230_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_acc_1231_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
lean_inc(v_e_1241_);
v___x_1246_ = l_Lean_MessageData_ofExpr(v_e_1241_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___y_1233_ = v___x_1247_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc(v_e_1241_);
v___x_1248_ = l_Lean_MessageData_ofExpr(v_e_1241_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_acc_1231_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___y_1233_ = v___x_1249_;
goto v___jp_1232_;
}
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_i_1230_, v___x_1234_);
lean_dec(v_i_1230_);
v_i_1230_ = v___x_1235_;
v_acc_1231_ = v___y_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1250_, lean_object* v_i_1251_, lean_object* v_acc_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1250_, v_i_1251_, v_acc_1252_);
lean_dec_ref(v_es_1250_);
return v_res_1253_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1258_ = l_Lean_MessageData_ofFormat(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1262_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1259_, v___x_1260_, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1263_);
lean_dec_ref(v_es_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1267_, lean_object* v_f_1268_, lean_object* v_r_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1270_ = lean_string_length(v_l_1267_);
v___x_1271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_l_1267_);
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v_f_1268_);
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_r_1269_);
v___x_1275_ = l_Lean_MessageData_ofFormat(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1270_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1281_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1282_ = l_Lean_MessageData_bracket(v___x_1280_, v_f_1279_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1285_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1286_ = l_Lean_MessageData_bracket(v___x_1284_, v_f_1283_, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v_x_1288_);
v___x_1289_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1289_;
}
else
{
lean_object* v_tail_1290_; 
v_tail_1290_ = lean_ctor_get(v_x_1287_, 1);
if (lean_obj_tag(v_tail_1290_) == 0)
{
lean_object* v_head_1291_; 
lean_dec_ref(v_x_1288_);
v_head_1291_ = lean_ctor_get(v_x_1287_, 0);
lean_inc(v_head_1291_);
lean_dec_ref(v_x_1287_);
return v_head_1291_;
}
else
{
lean_object* v_head_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1301_; 
lean_inc(v_tail_1290_);
v_head_1292_ = lean_ctor_get(v_x_1287_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_x_1287_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_x_1287_, 1);
lean_dec(v_unused_1302_);
v___x_1294_ = v_x_1287_;
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_head_1292_);
lean_dec(v_x_1287_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1301_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
lean_inc_ref(v_x_1288_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 7);
lean_ctor_set(v___x_1294_, 1, v_x_1288_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_head_1292_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_x_1288_);
v___x_1297_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = l_Lean_MessageData_joinSep(v_tail_1290_, v_x_1288_);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
return v___x_1299_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1307_ = l_Lean_MessageData_ofFormat(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1312_ = l_Lean_MessageData_ofFormat(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_box(1);
v___x_1314_ = l_Lean_MessageData_ofFormat(v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1316_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1318_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1321_ = l_Lean_MessageData_joinSep(v_x_1318_, v___x_1320_);
v___x_1322_ = l_Lean_MessageData_sbracket(v___x_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_array_to_list(v_msgs_1323_);
v___x_1325_ = l_Lean_MessageData_ofList(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1330_ = l_Lean_MessageData_ofFormat(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1335_ = l_Lean_MessageData_ofFormat(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1340_ = l_Lean_MessageData_ofFormat(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1341_){
_start:
{
if (lean_obj_tag(v_xs_1341_) == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1342_;
}
else
{
lean_object* v_tail_1343_; 
v_tail_1343_ = lean_ctor_get(v_xs_1341_, 1);
lean_inc(v_tail_1343_);
if (lean_obj_tag(v_tail_1343_) == 0)
{
lean_object* v_head_1344_; 
v_head_1344_ = lean_ctor_get(v_xs_1341_, 0);
lean_inc(v_head_1344_);
lean_dec_ref(v_xs_1341_);
return v_head_1344_;
}
else
{
lean_object* v_tail_1345_; 
v_tail_1345_ = lean_ctor_get(v_tail_1343_, 1);
if (lean_obj_tag(v_tail_1345_) == 0)
{
lean_object* v_head_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1363_; 
v_head_1346_ = lean_ctor_get(v_xs_1341_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_xs_1341_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v_xs_1341_, 1);
lean_dec(v_unused_1364_);
v___x_1348_ = v_xs_1341_;
v_isShared_1349_ = v_isSharedCheck_1363_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_head_1346_);
lean_dec(v_xs_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1363_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_head_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v_head_1350_ = lean_ctor_get(v_tail_1343_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_tail_1343_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_tail_1343_, 1);
lean_dec(v_unused_1362_);
v___x_1352_ = v_tail_1343_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_head_1350_);
lean_dec(v_tail_1343_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 7);
lean_ctor_set(v___x_1352_, 1, v___x_1354_);
lean_ctor_set(v___x_1352_, 0, v_head_1346_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_head_1346_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 7);
lean_ctor_set(v___x_1348_, 1, v_head_1350_);
lean_ctor_set(v___x_1348_, 0, v___x_1356_);
v___x_1358_ = v___x_1348_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_head_1350_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v_tail_1343_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1389_ = lean_ctor_get(v_tail_1343_, 1);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_tail_1343_, 0);
lean_dec(v_unused_1390_);
v___x_1366_ = v_tail_1343_;
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_tail_1343_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1368_ = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(v_xs_1341_);
v___x_1369_ = lean_array_mk(v_xs_1341_);
v___x_1370_ = lean_array_pop(v___x_1369_);
v___x_1371_ = lean_array_to_list(v___x_1370_);
v___x_1372_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1373_ = l_Lean_MessageData_joinSep(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 7);
lean_ctor_set(v___x_1366_, 1, v___x_1374_);
lean_ctor_set(v___x_1366_, 0, v___x_1373_);
v___x_1376_ = v___x_1366_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v___x_1377_ = l_List_getLast_x21___redArg(v___x_1368_, v_xs_1341_);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_xs_1341_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; lean_object* v_unused_1386_; 
v_unused_1385_ = lean_ctor_get(v_xs_1341_, 1);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_xs_1341_, 0);
lean_dec(v_unused_1386_);
v___x_1379_ = v_xs_1341_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v_xs_1341_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 7);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set(v___x_1379_, 0, v___x_1376_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
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
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1395_ = l_Lean_MessageData_ofFormat(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1400_ = l_Lean_MessageData_ofFormat(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1401_){
_start:
{
if (lean_obj_tag(v_xs_1401_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1402_;
}
else
{
lean_object* v_tail_1403_; 
v_tail_1403_ = lean_ctor_get(v_xs_1401_, 1);
lean_inc(v_tail_1403_);
if (lean_obj_tag(v_tail_1403_) == 0)
{
lean_object* v_head_1404_; 
v_head_1404_ = lean_ctor_get(v_xs_1401_, 0);
lean_inc(v_head_1404_);
lean_dec_ref(v_xs_1401_);
return v_head_1404_;
}
else
{
lean_object* v_tail_1405_; 
v_tail_1405_ = lean_ctor_get(v_tail_1403_, 1);
if (lean_obj_tag(v_tail_1405_) == 0)
{
lean_object* v_head_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1423_; 
v_head_1406_ = lean_ctor_get(v_xs_1401_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_xs_1401_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_xs_1401_, 1);
lean_dec(v_unused_1424_);
v___x_1408_ = v_xs_1401_;
v_isShared_1409_ = v_isSharedCheck_1423_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_head_1406_);
lean_dec(v_xs_1401_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1423_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_head_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
v_head_1410_ = lean_ctor_get(v_tail_1403_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_tail_1403_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_tail_1403_, 1);
lean_dec(v_unused_1422_);
v___x_1412_ = v_tail_1403_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_head_1410_);
lean_dec(v_tail_1403_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 7);
lean_ctor_set(v___x_1412_, 1, v___x_1414_);
lean_ctor_set(v___x_1412_, 0, v_head_1406_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_head_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 7);
lean_ctor_set(v___x_1408_, 1, v_head_1410_);
lean_ctor_set(v___x_1408_, 0, v___x_1416_);
v___x_1418_ = v___x_1408_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_head_1410_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v_tail_1403_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_tail_1403_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_tail_1403_, 0);
lean_dec(v_unused_1450_);
v___x_1426_ = v_tail_1403_;
v_isShared_1427_ = v_isSharedCheck_1448_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_tail_1403_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1448_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1428_ = l_Lean_instInhabitedMessageData_default;
lean_inc_ref(v_xs_1401_);
v___x_1429_ = lean_array_mk(v_xs_1401_);
v___x_1430_ = lean_array_pop(v___x_1429_);
v___x_1431_ = lean_array_to_list(v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1433_ = l_Lean_MessageData_joinSep(v___x_1431_, v___x_1432_);
v___x_1434_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 7);
lean_ctor_set(v___x_1426_, 1, v___x_1434_);
lean_ctor_set(v___x_1426_, 0, v___x_1433_);
v___x_1436_ = v___x_1426_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v___x_1437_ = l_List_getLast_x21___redArg(v___x_1428_, v_xs_1401_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_xs_1401_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; 
v_unused_1445_ = lean_ctor_get(v_xs_1401_, 1);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_xs_1401_, 0);
lean_dec(v_unused_1446_);
v___x_1439_ = v_xs_1401_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_xs_1401_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 7);
lean_ctor_set(v___x_1439_, 1, v___x_1437_);
lean_ctor_set(v___x_1439_, 0, v___x_1436_);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
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
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_1457_ = l_Lean_MessageData_ofFormat(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_1459_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v_note_1461_);
return v___x_1463_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_1468_ = l_Lean_MessageData_ofFormat(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_1470_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_hint_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_1479_ = lean_box(0);
v___x_1480_ = l_List_mapTR_loop___redArg(v___x_1478_, v_es_1477_, v___x_1479_);
v___x_1481_ = l_Lean_MessageData_ofList(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_1484_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_1486_ = l_Lean_instInhabitedPosition_default;
v___x_1487_ = lean_box(0);
v___x_1488_ = 0;
v___x_1489_ = 0;
v___x_1490_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1490_, 0, v___x_1485_);
lean_ctor_set(v___x_1490_, 1, v___x_1486_);
lean_ctor_set(v___x_1490_, 2, v___x_1487_);
lean_ctor_set(v___x_1490_, 3, v___x_1485_);
lean_ctor_set(v___x_1490_, 4, v_inst_1484_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*5, v___x_1488_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*5 + 1, v___x_1489_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*5 + 2, v___x_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_a_1491_, lean_object* v_inst_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_1496_, lean_object* v_inst_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v_fileName_1513_; lean_object* v_pos_1514_; lean_object* v_endPos_1515_; uint8_t v_keepFullRange_1516_; uint8_t v_severity_1517_; uint8_t v_isSilent_1518_; lean_object* v_caption_1519_; lean_object* v_data_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_fileName_1513_ = lean_ctor_get(v_x_1512_, 0);
lean_inc_ref(v_fileName_1513_);
v_pos_1514_ = lean_ctor_get(v_x_1512_, 1);
lean_inc_ref(v_pos_1514_);
v_endPos_1515_ = lean_ctor_get(v_x_1512_, 2);
lean_inc(v_endPos_1515_);
v_keepFullRange_1516_ = lean_ctor_get_uint8(v_x_1512_, sizeof(void*)*5);
v_severity_1517_ = lean_ctor_get_uint8(v_x_1512_, sizeof(void*)*5 + 1);
v_isSilent_1518_ = lean_ctor_get_uint8(v_x_1512_, sizeof(void*)*5 + 2);
v_caption_1519_ = lean_ctor_get(v_x_1512_, 3);
lean_inc_ref(v_caption_1519_);
v_data_1520_ = lean_ctor_get(v_x_1512_, 4);
lean_inc(v_data_1520_);
lean_dec_ref(v_x_1512_);
v___x_1521_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_1522_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_fileName_1513_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1528_ = l_Lean_instToJsonPosition_toJson(v_pos_1514_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1525_);
v___x_1531_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1532_ = l_Option_toJson___redArg(v___x_1521_, v_endPos_1515_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1525_);
v___x_1535_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1536_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1536_, 0, v_keepFullRange_1516_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1525_);
v___x_1539_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1540_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1517_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1525_);
v___x_1543_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1544_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1544_, 0, v_isSilent_1518_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1525_);
v___x_1547_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_caption_1519_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1525_);
v___x_1551_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1552_ = lean_apply_1(v_inst_1511_, v_data_1520_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1525_);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1525_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1550_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1546_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1542_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1538_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1534_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1530_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1526_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_1564_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1565_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_1563_, v___x_1562_, v___x_1564_);
v___x_1566_ = l_Lean_Json_mkObj(v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_1567_, lean_object* v_inst_1568_, lean_object* v_x_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_1568_, v_x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1572_, 0, lean_box(0));
lean_closure_set(v___x_1572_, 1, v_inst_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_1573_, lean_object* v_inst_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_1575_, 0, lean_box(0));
lean_closure_set(v___x_1575_, 1, v_inst_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = 1;
v___x_1582_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_1583_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_1586_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_1587_ = lean_string_append(v___x_1586_, v___x_1585_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = 1;
v___x_1591_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_1592_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1591_, v___x_1590_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_1594_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1595_ = lean_string_append(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1598_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_1599_ = lean_string_append(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = 1;
v___x_1606_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_1607_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1606_, v___x_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_1609_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1610_ = lean_string_append(v___x_1609_, v___x_1608_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1612_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_1613_ = lean_string_append(v___x_1612_, v___x_1611_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = 1;
v___x_1617_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_1618_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_1620_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1621_ = lean_string_append(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1623_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_1624_ = lean_string_append(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = 1;
v___x_1629_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_1630_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_1632_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1633_ = lean_string_append(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1635_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_1636_ = lean_string_append(v___x_1635_, v___x_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = 1;
v___x_1640_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_1641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_1643_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1644_ = lean_string_append(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1646_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_1647_ = lean_string_append(v___x_1646_, v___x_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = 1;
v___x_1651_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_1652_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1651_, v___x_1650_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_1654_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1655_ = lean_string_append(v___x_1654_, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1657_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_1658_ = lean_string_append(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = 1;
v___x_1662_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_1663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1662_, v___x_1661_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_1665_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1666_ = lean_string_append(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1668_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_1669_ = lean_string_append(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = 1;
v___x_1673_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_1674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1673_, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_1676_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_1677_ = lean_string_append(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_1679_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_1680_ = lean_string_append(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_1681_, lean_object* v_json_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_1684_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_1682_);
v___x_1685_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1683_, v___x_1684_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1690_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_1691_ = lean_string_append(v___x_1690_, v_a_1686_);
lean_dec(v_a_1686_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1696_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1685_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1685_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 0);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
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
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1704_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1685_);
v___x_1705_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_1706_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_1707_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_1682_);
v___x_1708_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1705_, v___x_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1713_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_1714_ = lean_string_append(v___x_1713_, v_a_1709_);
lean_dec(v_a_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1719_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1708_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1708_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 0);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
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
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1708_);
v___x_1728_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_1682_);
v___x_1729_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1706_, v___x_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1734_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_1735_ = lean_string_append(v___x_1734_, v_a_1730_);
lean_dec(v_a_1730_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1740_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1729_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1729_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
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
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1748_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1729_);
v___x_1749_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_1750_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_1682_);
v___x_1751_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1749_, v___x_1750_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1756_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_1757_ = lean_string_append(v___x_1756_, v_a_1752_);
lean_dec(v_a_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1762_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1751_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1751_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 0);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
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
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_a_1770_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1751_);
v___x_1771_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_1772_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_1682_);
v___x_1773_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1771_, v___x_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_1779_ = lean_string_append(v___x_1778_, v_a_1774_);
lean_dec(v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1784_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1773_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1773_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
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
lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_a_1792_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1773_);
v___x_1793_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_1682_);
v___x_1794_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1749_, v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1804_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1804_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_1800_ = lean_string_append(v___x_1799_, v_a_1795_);
lean_dec(v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1800_);
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1805_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1794_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1794_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 0);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
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
lean_object* v_a_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v___x_1794_);
v___x_1814_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_1682_);
v___x_1815_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v___x_1683_, v___x_1814_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1813_);
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1825_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1825_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_1821_ = lean_string_append(v___x_1820_, v_a_1816_);
lean_dec(v_a_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_a_1813_);
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
lean_dec(v_json_1682_);
lean_dec_ref(v_inst_1681_);
v_a_1826_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1815_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1815_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 0);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
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
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_a_1834_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1815_);
v___x_1835_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1836_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1682_, v_inst_1681_, v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1834_);
lean_dec(v_a_1813_);
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_1842_ = lean_string_append(v___x_1841_, v_a_1837_);
lean_dec(v_a_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1834_);
lean_dec(v_a_1813_);
lean_dec(v_a_1792_);
lean_dec(v_a_1770_);
lean_dec(v_a_1748_);
lean_dec(v_a_1727_);
lean_dec(v_a_1704_);
v_a_1847_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1836_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1836_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
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
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1866_; 
v_a_1855_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1857_ = v___x_1836_;
v_isShared_1858_ = v_isSharedCheck_1866_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1836_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1866_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; uint8_t v___x_1860_; uint8_t v___x_1861_; uint8_t v___x_1862_; lean_object* v___x_1864_; 
v___x_1859_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1859_, 0, v_a_1704_);
lean_ctor_set(v___x_1859_, 1, v_a_1727_);
lean_ctor_set(v___x_1859_, 2, v_a_1748_);
lean_ctor_set(v___x_1859_, 3, v_a_1834_);
lean_ctor_set(v___x_1859_, 4, v_a_1855_);
v___x_1860_ = lean_unbox(v_a_1770_);
lean_dec(v_a_1770_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*5, v___x_1860_);
v___x_1861_ = lean_unbox(v_a_1792_);
lean_dec(v_a_1792_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*5 + 1, v___x_1861_);
v___x_1862_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*5 + 2, v___x_1862_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1864_ = v___x_1857_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_1867_, lean_object* v_inst_1868_, lean_object* v_json_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_1868_, v_json_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1872_, 0, lean_box(0));
lean_closure_set(v___x_1872_, 1, v_inst_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_1873_, lean_object* v_inst_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_1875_, 0, lean_box(0));
lean_closure_set(v___x_1875_, 1, v_inst_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_box(0);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1879_; 
v_val_1878_ = lean_ctor_get(v_x_1876_, 0);
lean_inc(v_val_1878_);
lean_dec_ref(v_x_1876_);
v___x_1879_ = l_Lean_instToJsonPosition_toJson(v_val_1878_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
if (lean_obj_tag(v_a_1880_) == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_array_to_list(v_a_1881_);
return v___x_1882_;
}
else
{
lean_object* v_head_1883_; lean_object* v_tail_1884_; lean_object* v___x_1885_; 
v_head_1883_ = lean_ctor_get(v_a_1880_, 0);
lean_inc(v_head_1883_);
v_tail_1884_ = lean_ctor_get(v_a_1880_, 1);
lean_inc(v_tail_1884_);
lean_dec_ref(v_a_1880_);
v___x_1885_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1881_, v_head_1883_);
v_a_1880_ = v_tail_1884_;
v_a_1881_ = v___x_1885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_1888_){
_start:
{
lean_object* v_toBaseMessage_1889_; lean_object* v_kind_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1955_; 
v_toBaseMessage_1889_ = lean_ctor_get(v_x_1888_, 0);
v_kind_1890_ = lean_ctor_get(v_x_1888_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1892_ = v_x_1888_;
v_isShared_1893_ = v_isSharedCheck_1955_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_kind_1890_);
lean_inc(v_toBaseMessage_1889_);
lean_dec(v_x_1888_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1955_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_fileName_1894_; lean_object* v_pos_1895_; lean_object* v_endPos_1896_; uint8_t v_keepFullRange_1897_; uint8_t v_severity_1898_; uint8_t v_isSilent_1899_; lean_object* v_caption_1900_; lean_object* v_data_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v_fileName_1894_ = lean_ctor_get(v_toBaseMessage_1889_, 0);
lean_inc_ref(v_fileName_1894_);
v_pos_1895_ = lean_ctor_get(v_toBaseMessage_1889_, 1);
lean_inc_ref(v_pos_1895_);
v_endPos_1896_ = lean_ctor_get(v_toBaseMessage_1889_, 2);
lean_inc(v_endPos_1896_);
v_keepFullRange_1897_ = lean_ctor_get_uint8(v_toBaseMessage_1889_, sizeof(void*)*5);
v_severity_1898_ = lean_ctor_get_uint8(v_toBaseMessage_1889_, sizeof(void*)*5 + 1);
v_isSilent_1899_ = lean_ctor_get_uint8(v_toBaseMessage_1889_, sizeof(void*)*5 + 2);
v_caption_1900_ = lean_ctor_get(v_toBaseMessage_1889_, 3);
lean_inc_ref(v_caption_1900_);
v_data_1901_ = lean_ctor_get(v_toBaseMessage_1889_, 4);
lean_inc(v_data_1901_);
lean_dec_ref(v_toBaseMessage_1889_);
v___x_1902_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_1903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_fileName_1894_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1903_);
lean_ctor_set(v___x_1892_, 0, v___x_1902_);
v___x_1905_ = v___x_1892_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_1909_ = l_Lean_instToJsonPosition_toJson(v_pos_1895_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1906_);
v___x_1912_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_1913_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_1896_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1906_);
v___x_1916_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_1917_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1917_, 0, v_keepFullRange_1897_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1906_);
v___x_1920_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_1921_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_1898_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1906_);
v___x_1924_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_1925_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1925_, 0, v_isSilent_1899_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1906_);
v___x_1928_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_caption_1900_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1906_);
v___x_1932_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_1933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_data_1901_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1906_);
v___x_1936_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_1937_ = 1;
v___x_1938_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1890_, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1936_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1906_);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1906_);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1935_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1931_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1927_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1923_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1919_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1915_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1911_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1907_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_1952_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_1950_, v___x_1951_);
v___x_1953_ = l_Lean_Json_mkObj(v___x_1952_);
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_1958_, lean_object* v_k_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = l_Lean_Json_getObjValD(v_j_1958_, v_k_1959_);
v___x_1961_ = l_Lean_Json_getStr_x3f(v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_1962_, lean_object* v_k_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_1962_, v_k_1963_);
lean_dec_ref(v_k_1963_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_1965_, lean_object* v_k_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = l_Lean_Json_getObjValD(v_j_1965_, v_k_1966_);
v___x_1968_ = l_Lean_instFromJsonPosition_fromJson(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_1969_, v_k_1970_);
lean_dec_ref(v_k_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_1972_, lean_object* v_k_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Lean_Json_getObjValD(v_j_1972_, v_k_1973_);
v___x_1975_ = l_Lean_Json_getBool_x3f(v___x_1974_);
lean_dec(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_1976_, lean_object* v_k_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_1976_, v_k_1977_);
lean_dec_ref(v_k_1977_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_1979_, lean_object* v_k_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = l_Lean_Json_getObjValD(v_j_1979_, v_k_1980_);
v___x_1982_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_1983_, lean_object* v_k_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_1983_, v_k_1984_);
lean_dec_ref(v_k_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_1986_, lean_object* v_k_1987_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = l_Lean_Json_getObjValD(v_j_1986_, v_k_1987_);
v___x_1989_ = l_Lean_Name_fromJson_x3f(v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_1990_, lean_object* v_k_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_1990_, v_k_1991_);
lean_dec_ref(v_k_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_instFromJsonPosition_fromJson(v_x_1995_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2014_; 
v_a_2006_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2008_ = v___x_1997_;
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1997_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2014_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_a_2006_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2010_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2015_, lean_object* v_k_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = l_Lean_Json_getObjValD(v_j_2015_, v_k_2016_);
v___x_2018_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2019_, lean_object* v_k_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2019_, v_k_2020_);
lean_dec_ref(v_k_2020_);
return v_res_2021_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = 1;
v___x_2027_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2027_, v___x_2026_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2030_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2031_ = lean_string_append(v___x_2030_, v___x_2029_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2033_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2034_ = lean_string_append(v___x_2033_, v___x_2032_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2036_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2037_ = lean_string_append(v___x_2036_, v___x_2035_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2039_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2040_ = lean_string_append(v___x_2039_, v___x_2038_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2042_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2043_ = lean_string_append(v___x_2042_, v___x_2041_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2045_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2046_ = lean_string_append(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2048_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2049_ = lean_string_append(v___x_2048_, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2051_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2052_ = lean_string_append(v___x_2051_, v___x_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2054_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2055_ = lean_string_append(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2057_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2058_ = lean_string_append(v___x_2057_, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2060_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2061_ = lean_string_append(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2063_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2064_ = lean_string_append(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2066_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2067_ = lean_string_append(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2069_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2070_ = lean_string_append(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2072_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2073_ = lean_string_append(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2075_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2076_ = lean_string_append(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2078_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2079_ = lean_string_append(v___x_2078_, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = 1;
v___x_2083_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2083_, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2086_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2087_ = lean_string_append(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2089_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2090_ = lean_string_append(v___x_2089_, v___x_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2091_);
v___x_2093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2091_, v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_json_2091_);
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2098_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2099_ = lean_string_append(v___x_2098_, v_a_2094_);
lean_dec(v_a_2094_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2099_);
v___x_2101_ = v___x_2096_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_json_2091_);
v_a_2104_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2093_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2093_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 0);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
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
lean_object* v_a_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_a_2112_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2093_);
v___x_2113_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2091_);
v___x_2114_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2091_, v___x_2113_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2124_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2124_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2119_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2120_ = lean_string_append(v___x_2119_, v_a_2115_);
lean_dec(v_a_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2120_);
v___x_2122_ = v___x_2117_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2125_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2114_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2114_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 0);
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
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
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2114_);
v___x_2134_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2091_);
v___x_2135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2091_, v___x_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2140_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2141_ = lean_string_append(v___x_2140_, v_a_2136_);
lean_dec(v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2146_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2135_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2135_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 0);
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
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
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_a_2154_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2135_);
v___x_2155_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2091_);
v___x_2156_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2091_, v___x_2155_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2166_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2166_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2161_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2162_ = lean_string_append(v___x_2161_, v_a_2157_);
lean_dec(v_a_2157_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2162_);
v___x_2164_ = v___x_2159_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2167_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2156_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2156_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 0);
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
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
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2156_);
v___x_2176_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2091_);
v___x_2177_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2091_, v___x_2176_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2183_ = lean_string_append(v___x_2182_, v_a_2178_);
lean_dec(v_a_2178_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2183_);
v___x_2185_ = v___x_2180_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2188_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2177_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2177_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set_tag(v___x_2190_, 0);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
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
lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_a_2196_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2177_);
v___x_2197_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2091_);
v___x_2198_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2091_, v___x_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2204_ = lean_string_append(v___x_2203_, v_a_2199_);
lean_dec(v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2204_);
v___x_2206_ = v___x_2201_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2209_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2198_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2198_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 0);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
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
lean_object* v_a_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_a_2217_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2198_);
v___x_2218_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2091_);
v___x_2219_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2091_, v___x_2218_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2225_ = lean_string_append(v___x_2224_, v_a_2220_);
lean_dec(v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2230_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2219_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2219_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
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
lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_a_2238_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2219_);
v___x_2239_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2091_);
v___x_2240_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2091_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2238_);
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2246_ = lean_string_append(v___x_2245_, v_a_2241_);
lean_dec(v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2238_);
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
lean_dec(v_json_2091_);
v_a_2251_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2240_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2240_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set_tag(v___x_2253_, 0);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
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
lean_object* v_a_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_a_2259_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2240_);
v___x_2260_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2261_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2091_, v___x_2260_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2259_);
lean_dec(v_a_2238_);
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2266_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2267_ = lean_string_append(v___x_2266_, v_a_2262_);
lean_dec(v_a_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2267_);
v___x_2269_ = v___x_2264_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2259_);
lean_dec(v_a_2238_);
lean_dec(v_a_2217_);
lean_dec(v_a_2196_);
lean_dec(v_a_2175_);
lean_dec(v_a_2154_);
lean_dec(v_a_2133_);
lean_dec(v_a_2112_);
v_a_2272_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2261_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2261_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 0);
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
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
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2292_; 
v_a_2280_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2282_ = v___x_2261_;
v_isShared_2283_ = v_isSharedCheck_2292_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2261_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2292_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; uint8_t v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2284_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2284_, 0, v_a_2112_);
lean_ctor_set(v___x_2284_, 1, v_a_2133_);
lean_ctor_set(v___x_2284_, 2, v_a_2154_);
lean_ctor_set(v___x_2284_, 3, v_a_2238_);
lean_ctor_set(v___x_2284_, 4, v_a_2259_);
v___x_2285_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5, v___x_2285_);
v___x_2286_ = lean_unbox(v_a_2196_);
lean_dec(v_a_2196_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5 + 1, v___x_2286_);
v___x_2287_ = lean_unbox(v_a_2217_);
lean_dec(v_a_2217_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*5 + 2, v___x_2287_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2284_);
lean_ctor_set(v___x_2288_, 1, v_a_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2288_);
v___x_2290_ = v___x_2282_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2299_ = l_Lean_Name_str___override(v_errorName_2297_, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2300_, lean_object* v_name_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = l_Lean_kindOfErrorName(v_name_2301_);
v___x_2303_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_msg_2300_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2305_){
_start:
{
switch(lean_obj_tag(v_a_2305_))
{
case 0:
{
return v_a_2305_;
}
case 1:
{
lean_object* v_pre_2306_; lean_object* v_str_2307_; lean_object* v_p_x27_2308_; uint8_t v___y_2310_; uint8_t v___x_2313_; 
v_pre_2306_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_pre_2306_);
v_str_2307_ = lean_ctor_get(v_a_2305_, 1);
lean_inc_ref(v_str_2307_);
lean_dec_ref(v_a_2305_);
v_p_x27_2308_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2306_);
v___x_2313_ = l_Lean_Name_isAnonymous(v_p_x27_2308_);
if (v___x_2313_ == 0)
{
v___y_2310_ = v___x_2313_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2315_ = lean_string_dec_eq(v_str_2307_, v___x_2314_);
v___y_2310_ = v___x_2315_;
goto v___jp_2309_;
}
v___jp_2309_:
{
if (v___y_2310_ == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Name_str___override(v_p_x27_2308_, v_str_2307_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; 
lean_dec(v_p_x27_2308_);
lean_dec_ref(v_str_2307_);
v___x_2312_ = lean_box(0);
return v___x_2312_;
}
}
}
default: 
{
lean_object* v_pre_2316_; lean_object* v_i_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_pre_2316_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_pre_2316_);
v_i_2317_ = lean_ctor_get(v_a_2305_, 1);
lean_inc(v_i_2317_);
lean_dec_ref(v_a_2305_);
v___x_2318_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2316_);
v___x_2319_ = l_Lean_Name_num___override(v___x_2318_, v_i_2317_);
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2320_){
_start:
{
switch(lean_obj_tag(v_x_2320_))
{
case 3:
{
lean_object* v_a_2321_; lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2330_; 
v_a_2321_ = lean_ctor_get(v_x_2320_, 0);
v_a_2322_ = lean_ctor_get(v_x_2320_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_x_2320_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2324_ = v_x_2320_;
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_inc(v_a_2321_);
lean_dec(v_x_2320_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = l_Lean_MessageData_stripNestedTags(v_a_2322_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2321_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
case 4:
{
lean_object* v_a_2331_; lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_a_2331_ = lean_ctor_get(v_x_2320_, 0);
v_a_2332_ = lean_ctor_get(v_x_2320_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_x_2320_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v_x_2320_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_inc(v_a_2331_);
lean_dec(v_x_2320_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_MessageData_stripNestedTags(v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___x_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2331_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
case 8:
{
lean_object* v_a_2341_; lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2350_; 
v_a_2341_ = lean_ctor_get(v_x_2320_, 0);
v_a_2342_ = lean_ctor_get(v_x_2320_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_x_2320_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2344_ = v_x_2320_;
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_inc(v_a_2341_);
lean_dec(v_x_2320_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2346_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2341_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2346_);
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_a_2342_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
default: 
{
return v_x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 1)
{
lean_object* v_pre_2352_; lean_object* v_str_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_pre_2352_ = lean_ctor_get(v_x_2351_, 0);
v_str_2353_ = lean_ctor_get(v_x_2351_, 1);
v___x_2354_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2355_ = lean_string_dec_eq(v_str_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_box(0);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; 
lean_inc(v_pre_2352_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_pre_2352_);
return v___x_2357_;
}
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_box(0);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_errorNameOfKind_x3f(v_x_2359_);
lean_dec(v_x_2359_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = l_Lean_MessageData_kind(v_msg_2361_);
v___x_2363_ = l_Lean_errorNameOfKind_x3f(v___x_2362_);
lean_dec(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_MessageData_errorName_x3f(v_msg_2364_);
lean_dec_ref(v_msg_2364_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2366_){
_start:
{
lean_object* v_data_2367_; lean_object* v___x_2368_; 
v_data_2367_ = lean_ctor_get(v_msg_2366_, 4);
v___x_2368_ = l_Lean_MessageData_errorName_x3f(v_data_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Message_errorName_x3f(v_msg_2369_);
lean_dec_ref(v_msg_2369_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2371_){
_start:
{
lean_object* v_toBaseMessage_2372_; lean_object* v_fileName_2373_; lean_object* v_pos_2374_; lean_object* v_endPos_2375_; uint8_t v_keepFullRange_2376_; uint8_t v_severity_2377_; uint8_t v_isSilent_2378_; lean_object* v_caption_2379_; lean_object* v_data_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2389_; 
v_toBaseMessage_2372_ = lean_ctor_get(v_msg_2371_, 0);
lean_inc_ref(v_toBaseMessage_2372_);
lean_dec_ref(v_msg_2371_);
v_fileName_2373_ = lean_ctor_get(v_toBaseMessage_2372_, 0);
v_pos_2374_ = lean_ctor_get(v_toBaseMessage_2372_, 1);
v_endPos_2375_ = lean_ctor_get(v_toBaseMessage_2372_, 2);
v_keepFullRange_2376_ = lean_ctor_get_uint8(v_toBaseMessage_2372_, sizeof(void*)*5);
v_severity_2377_ = lean_ctor_get_uint8(v_toBaseMessage_2372_, sizeof(void*)*5 + 1);
v_isSilent_2378_ = lean_ctor_get_uint8(v_toBaseMessage_2372_, sizeof(void*)*5 + 2);
v_caption_2379_ = lean_ctor_get(v_toBaseMessage_2372_, 3);
v_data_2380_ = lean_ctor_get(v_toBaseMessage_2372_, 4);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_toBaseMessage_2372_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2382_ = v_toBaseMessage_2372_;
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_data_2380_);
lean_inc(v_caption_2379_);
lean_inc(v_endPos_2375_);
lean_inc(v_pos_2374_);
lean_inc(v_fileName_2373_);
lean_dec(v_toBaseMessage_2372_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_data_2380_);
v___x_2385_ = l_Lean_MessageData_ofFormat(v___x_2384_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2385_);
v___x_2387_ = v___x_2382_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_fileName_2373_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_pos_2374_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_endPos_2375_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_caption_2379_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v___x_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2388_, sizeof(void*)*5, v_keepFullRange_2376_);
lean_ctor_set_uint8(v_reuseFailAlloc_2388_, sizeof(void*)*5 + 1, v_severity_2377_);
lean_ctor_set_uint8(v_reuseFailAlloc_2388_, sizeof(void*)*5 + 2, v_isSilent_2378_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2395_, uint8_t v_includeEndPos_2396_){
_start:
{
lean_object* v___y_2398_; lean_object* v___y_2402_; uint8_t v___y_2403_; uint32_t v___y_2404_; lean_object* v_str_2408_; lean_object* v_toBaseMessage_2420_; lean_object* v_kind_2421_; lean_object* v_fileName_2422_; lean_object* v_pos_2423_; lean_object* v_endPos_2424_; uint8_t v_severity_2425_; lean_object* v_caption_2426_; lean_object* v_data_2427_; lean_object* v___y_2429_; lean_object* v_str_2430_; lean_object* v___y_2438_; 
v_toBaseMessage_2420_ = lean_ctor_get(v_msg_2395_, 0);
lean_inc_ref(v_toBaseMessage_2420_);
v_kind_2421_ = lean_ctor_get(v_msg_2395_, 1);
lean_inc(v_kind_2421_);
lean_dec_ref(v_msg_2395_);
v_fileName_2422_ = lean_ctor_get(v_toBaseMessage_2420_, 0);
lean_inc_ref(v_fileName_2422_);
v_pos_2423_ = lean_ctor_get(v_toBaseMessage_2420_, 1);
lean_inc_ref(v_pos_2423_);
v_endPos_2424_ = lean_ctor_get(v_toBaseMessage_2420_, 2);
lean_inc(v_endPos_2424_);
v_severity_2425_ = lean_ctor_get_uint8(v_toBaseMessage_2420_, sizeof(void*)*5 + 1);
v_caption_2426_ = lean_ctor_get(v_toBaseMessage_2420_, 3);
lean_inc_ref(v_caption_2426_);
v_data_2427_ = lean_ctor_get(v_toBaseMessage_2420_, 4);
lean_inc(v_data_2427_);
lean_dec_ref(v_toBaseMessage_2420_);
if (v_includeEndPos_2396_ == 0)
{
lean_object* v___x_2444_; 
lean_dec(v_endPos_2424_);
v___x_2444_ = lean_box(0);
v___y_2438_ = v___x_2444_;
goto v___jp_2437_;
}
else
{
v___y_2438_ = v_endPos_2424_;
goto v___jp_2437_;
}
v___jp_2397_:
{
lean_object* v___x_2399_; lean_object* v_str_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2400_ = lean_string_append(v___y_2398_, v___x_2399_);
return v_str_2400_;
}
v___jp_2401_:
{
uint32_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = 10;
v___x_2406_ = lean_uint32_dec_eq(v___y_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
v___y_2398_ = v___y_2402_;
goto v___jp_2397_;
}
else
{
if (v___y_2403_ == 0)
{
return v___y_2402_;
}
else
{
v___y_2398_ = v___y_2402_;
goto v___jp_2397_;
}
}
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2409_ = lean_string_utf8_byte_size(v_str_2408_);
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_nat_dec_eq(v___x_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_inc_ref(v_str_2408_);
v___x_2412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2412_, 0, v_str_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2410_);
lean_ctor_set(v___x_2412_, 2, v___x_2409_);
v___x_2413_ = l_String_Slice_Pos_prev_x3f(v___x_2412_, v___x_2409_);
if (lean_obj_tag(v___x_2413_) == 0)
{
uint32_t v___x_2414_; 
lean_dec_ref(v___x_2412_);
v___x_2414_ = 65;
v___y_2402_ = v_str_2408_;
v___y_2403_ = v___x_2411_;
v___y_2404_ = v___x_2414_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2415_; lean_object* v___x_2416_; 
v_val_2415_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_val_2415_);
lean_dec_ref(v___x_2413_);
v___x_2416_ = l_String_Slice_Pos_get_x3f(v___x_2412_, v_val_2415_);
lean_dec(v_val_2415_);
lean_dec_ref(v___x_2412_);
if (lean_obj_tag(v___x_2416_) == 0)
{
uint32_t v___x_2417_; 
v___x_2417_ = 65;
v___y_2402_ = v_str_2408_;
v___y_2403_ = v___x_2411_;
v___y_2404_ = v___x_2417_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2418_; uint32_t v___x_2419_; 
v_val_2418_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_val_2418_);
lean_dec_ref(v___x_2416_);
v___x_2419_ = lean_unbox_uint32(v_val_2418_);
lean_dec(v_val_2418_);
v___y_2402_ = v_str_2408_;
v___y_2403_ = v___x_2411_;
v___y_2404_ = v___x_2419_;
goto v___jp_2401_;
}
}
}
else
{
v___y_2398_ = v_str_2408_;
goto v___jp_2397_;
}
}
v___jp_2428_:
{
switch(v_severity_2425_)
{
case 0:
{
lean_dec(v___y_2429_);
lean_dec_ref(v_pos_2423_);
lean_dec_ref(v_fileName_2422_);
lean_dec(v_kind_2421_);
v_str_2408_ = v_str_2430_;
goto v___jp_2407_;
}
case 1:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_str_2433_; 
v___x_2431_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2432_ = l_Lean_errorNameOfKind_x3f(v_kind_2421_);
lean_dec(v_kind_2421_);
v_str_2433_ = l_Lean_mkErrorStringWithPos(v_fileName_2422_, v_pos_2423_, v_str_2430_, v___y_2429_, v___x_2431_, v___x_2432_);
lean_dec_ref(v_str_2430_);
v_str_2408_ = v_str_2433_;
goto v___jp_2407_;
}
default: 
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_str_2436_; 
v___x_2434_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2435_ = l_Lean_errorNameOfKind_x3f(v_kind_2421_);
lean_dec(v_kind_2421_);
v_str_2436_ = l_Lean_mkErrorStringWithPos(v_fileName_2422_, v_pos_2423_, v_str_2430_, v___y_2429_, v___x_2434_, v___x_2435_);
lean_dec_ref(v_str_2430_);
v_str_2408_ = v_str_2436_;
goto v___jp_2407_;
}
}
}
v___jp_2437_:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2440_ = lean_string_dec_eq(v_caption_2426_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_str_2443_; 
v___x_2441_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2442_ = lean_string_append(v_caption_2426_, v___x_2441_);
v_str_2443_ = lean_string_append(v___x_2442_, v_data_2427_);
lean_dec(v_data_2427_);
v___y_2429_ = v___y_2438_;
v_str_2430_ = v_str_2443_;
goto v___jp_2428_;
}
else
{
lean_dec_ref(v_caption_2426_);
v___y_2429_ = v___y_2438_;
v_str_2430_ = v_data_2427_;
goto v___jp_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2445_, lean_object* v_includeEndPos_2446_){
_start:
{
uint8_t v_includeEndPos_boxed_2447_; lean_object* v_res_2448_; 
v_includeEndPos_boxed_2447_ = lean_unbox(v_includeEndPos_2446_);
v_res_2448_ = l_Lean_SerialMessage_toString(v_msg_2445_, v_includeEndPos_boxed_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2449_){
_start:
{
uint8_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = 0;
v___x_2451_ = l_Lean_SerialMessage_toString(v_msg_2449_, v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2454_){
_start:
{
lean_object* v_data_2455_; lean_object* v___x_2456_; 
v_data_2455_ = lean_ctor_get(v_msg_2454_, 4);
v___x_2456_ = l_Lean_MessageData_kind(v_data_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Message_kind(v_msg_2457_);
lean_dec_ref(v_msg_2457_);
return v_res_2458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2459_){
_start:
{
lean_object* v_data_2460_; uint8_t v___x_2461_; 
v_data_2460_ = lean_ctor_get(v_msg_2459_, 4);
v___x_2461_ = l_Lean_MessageData_isTrace(v_data_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2462_){
_start:
{
uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_res_2463_ = l_Lean_Message_isTrace(v_msg_2462_);
lean_dec_ref(v_msg_2462_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2465_){
_start:
{
lean_object* v_fileName_2467_; lean_object* v_pos_2468_; lean_object* v_endPos_2469_; uint8_t v_keepFullRange_2470_; uint8_t v_severity_2471_; uint8_t v_isSilent_2472_; lean_object* v_caption_2473_; lean_object* v_data_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2484_; 
v_fileName_2467_ = lean_ctor_get(v_msg_2465_, 0);
v_pos_2468_ = lean_ctor_get(v_msg_2465_, 1);
v_endPos_2469_ = lean_ctor_get(v_msg_2465_, 2);
v_keepFullRange_2470_ = lean_ctor_get_uint8(v_msg_2465_, sizeof(void*)*5);
v_severity_2471_ = lean_ctor_get_uint8(v_msg_2465_, sizeof(void*)*5 + 1);
v_isSilent_2472_ = lean_ctor_get_uint8(v_msg_2465_, sizeof(void*)*5 + 2);
v_caption_2473_ = lean_ctor_get(v_msg_2465_, 3);
v_data_2474_ = lean_ctor_get(v_msg_2465_, 4);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_msg_2465_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2476_ = v_msg_2465_;
v_isShared_2477_ = v_isSharedCheck_2484_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_data_2474_);
lean_inc(v_caption_2473_);
lean_inc(v_endPos_2469_);
lean_inc(v_pos_2468_);
lean_inc(v_fileName_2467_);
lean_dec(v_msg_2465_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2484_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_inc(v_data_2474_);
v___x_2478_ = l_Lean_MessageData_toString(v_data_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v___x_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_fileName_2467_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_pos_2468_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_endPos_2469_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_caption_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v___x_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*5, v_keepFullRange_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*5 + 1, v_severity_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*5 + 2, v_isSilent_2472_);
v___x_2480_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = l_Lean_MessageData_kind(v_data_2474_);
lean_dec(v_data_2474_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Message_serialize(v_msg_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2488_, uint8_t v_includeEndPos_2489_){
_start:
{
lean_object* v_fileName_2491_; lean_object* v_pos_2492_; lean_object* v_endPos_2493_; uint8_t v_severity_2494_; lean_object* v_caption_2495_; lean_object* v_data_2496_; lean_object* v___x_2497_; lean_object* v___y_2499_; lean_object* v___y_2503_; uint8_t v___y_2504_; uint32_t v___y_2505_; lean_object* v_str_2509_; lean_object* v___x_2521_; lean_object* v___y_2523_; lean_object* v_str_2524_; lean_object* v___y_2532_; 
v_fileName_2491_ = lean_ctor_get(v_msg_2488_, 0);
lean_inc_ref(v_fileName_2491_);
v_pos_2492_ = lean_ctor_get(v_msg_2488_, 1);
lean_inc_ref(v_pos_2492_);
v_endPos_2493_ = lean_ctor_get(v_msg_2488_, 2);
lean_inc(v_endPos_2493_);
v_severity_2494_ = lean_ctor_get_uint8(v_msg_2488_, sizeof(void*)*5 + 1);
v_caption_2495_ = lean_ctor_get(v_msg_2488_, 3);
lean_inc_ref(v_caption_2495_);
v_data_2496_ = lean_ctor_get(v_msg_2488_, 4);
lean_inc(v_data_2496_);
lean_dec_ref(v_msg_2488_);
lean_inc(v_data_2496_);
v___x_2497_ = l_Lean_MessageData_toString(v_data_2496_);
v___x_2521_ = l_Lean_MessageData_kind(v_data_2496_);
lean_dec(v_data_2496_);
if (v_includeEndPos_2489_ == 0)
{
lean_object* v___x_2538_; 
lean_dec(v_endPos_2493_);
v___x_2538_ = lean_box(0);
v___y_2532_ = v___x_2538_;
goto v___jp_2531_;
}
else
{
v___y_2532_ = v_endPos_2493_;
goto v___jp_2531_;
}
v___jp_2498_:
{
lean_object* v___x_2500_; lean_object* v_str_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2501_ = lean_string_append(v___y_2499_, v___x_2500_);
return v_str_2501_;
}
v___jp_2502_:
{
uint32_t v___x_2506_; uint8_t v___x_2507_; 
v___x_2506_ = 10;
v___x_2507_ = lean_uint32_dec_eq(v___y_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
v___y_2499_ = v___y_2503_;
goto v___jp_2498_;
}
else
{
if (v___y_2504_ == 0)
{
return v___y_2503_;
}
else
{
v___y_2499_ = v___y_2503_;
goto v___jp_2498_;
}
}
}
v___jp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2510_ = lean_string_utf8_byte_size(v_str_2509_);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_nat_dec_eq(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_inc_ref(v_str_2509_);
v___x_2513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2513_, 0, v_str_2509_);
lean_ctor_set(v___x_2513_, 1, v___x_2511_);
lean_ctor_set(v___x_2513_, 2, v___x_2510_);
v___x_2514_ = l_String_Slice_Pos_prev_x3f(v___x_2513_, v___x_2510_);
if (lean_obj_tag(v___x_2514_) == 0)
{
uint32_t v___x_2515_; 
lean_dec_ref(v___x_2513_);
v___x_2515_ = 65;
v___y_2503_ = v_str_2509_;
v___y_2504_ = v___x_2512_;
v___y_2505_ = v___x_2515_;
goto v___jp_2502_;
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2517_; 
v_val_2516_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_val_2516_);
lean_dec_ref(v___x_2514_);
v___x_2517_ = l_String_Slice_Pos_get_x3f(v___x_2513_, v_val_2516_);
lean_dec(v_val_2516_);
lean_dec_ref(v___x_2513_);
if (lean_obj_tag(v___x_2517_) == 0)
{
uint32_t v___x_2518_; 
v___x_2518_ = 65;
v___y_2503_ = v_str_2509_;
v___y_2504_ = v___x_2512_;
v___y_2505_ = v___x_2518_;
goto v___jp_2502_;
}
else
{
lean_object* v_val_2519_; uint32_t v___x_2520_; 
v_val_2519_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v___x_2517_);
v___x_2520_ = lean_unbox_uint32(v_val_2519_);
lean_dec(v_val_2519_);
v___y_2503_ = v_str_2509_;
v___y_2504_ = v___x_2512_;
v___y_2505_ = v___x_2520_;
goto v___jp_2502_;
}
}
}
else
{
v___y_2499_ = v_str_2509_;
goto v___jp_2498_;
}
}
v___jp_2522_:
{
switch(v_severity_2494_)
{
case 0:
{
lean_dec(v___y_2523_);
lean_dec(v___x_2521_);
lean_dec_ref(v_pos_2492_);
lean_dec_ref(v_fileName_2491_);
v_str_2509_ = v_str_2524_;
goto v___jp_2508_;
}
case 1:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v_str_2527_; 
v___x_2525_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2526_ = l_Lean_errorNameOfKind_x3f(v___x_2521_);
lean_dec(v___x_2521_);
v_str_2527_ = l_Lean_mkErrorStringWithPos(v_fileName_2491_, v_pos_2492_, v_str_2524_, v___y_2523_, v___x_2525_, v___x_2526_);
lean_dec_ref(v_str_2524_);
v_str_2509_ = v_str_2527_;
goto v___jp_2508_;
}
default: 
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_str_2530_; 
v___x_2528_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2529_ = l_Lean_errorNameOfKind_x3f(v___x_2521_);
lean_dec(v___x_2521_);
v_str_2530_ = l_Lean_mkErrorStringWithPos(v_fileName_2491_, v_pos_2492_, v_str_2524_, v___y_2523_, v___x_2528_, v___x_2529_);
lean_dec_ref(v_str_2524_);
v_str_2509_ = v_str_2530_;
goto v___jp_2508_;
}
}
}
v___jp_2531_:
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2534_ = lean_string_dec_eq(v_caption_2495_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_str_2537_; 
v___x_2535_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2536_ = lean_string_append(v_caption_2495_, v___x_2535_);
v_str_2537_ = lean_string_append(v___x_2536_, v___x_2497_);
lean_dec_ref(v___x_2497_);
v___y_2523_ = v___y_2532_;
v_str_2524_ = v_str_2537_;
goto v___jp_2522_;
}
else
{
lean_dec_ref(v_caption_2495_);
v___y_2523_ = v___y_2532_;
v_str_2524_ = v___x_2497_;
goto v___jp_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2539_, lean_object* v_includeEndPos_2540_, lean_object* v_a_2541_){
_start:
{
uint8_t v_includeEndPos_boxed_2542_; lean_object* v_res_2543_; 
v_includeEndPos_boxed_2542_ = lean_unbox(v_includeEndPos_2540_);
v_res_2543_ = l_Lean_Message_toString(v_msg_2539_, v_includeEndPos_boxed_2542_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2544_){
_start:
{
lean_object* v_fileName_2546_; lean_object* v_pos_2547_; lean_object* v_endPos_2548_; uint8_t v_keepFullRange_2549_; uint8_t v_severity_2550_; uint8_t v_isSilent_2551_; lean_object* v_caption_2552_; lean_object* v_data_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_fileName_2546_ = lean_ctor_get(v_msg_2544_, 0);
lean_inc_ref(v_fileName_2546_);
v_pos_2547_ = lean_ctor_get(v_msg_2544_, 1);
lean_inc_ref(v_pos_2547_);
v_endPos_2548_ = lean_ctor_get(v_msg_2544_, 2);
lean_inc(v_endPos_2548_);
v_keepFullRange_2549_ = lean_ctor_get_uint8(v_msg_2544_, sizeof(void*)*5);
v_severity_2550_ = lean_ctor_get_uint8(v_msg_2544_, sizeof(void*)*5 + 1);
v_isSilent_2551_ = lean_ctor_get_uint8(v_msg_2544_, sizeof(void*)*5 + 2);
v_caption_2552_ = lean_ctor_get(v_msg_2544_, 3);
lean_inc_ref(v_caption_2552_);
v_data_2553_ = lean_ctor_get(v_msg_2544_, 4);
lean_inc(v_data_2553_);
lean_dec_ref(v_msg_2544_);
lean_inc(v_data_2553_);
v___x_2554_ = l_Lean_MessageData_toString(v_data_2553_);
v___x_2555_ = l_Lean_MessageData_kind(v_data_2553_);
lean_dec(v_data_2553_);
v___x_2556_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_fileName_2546_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2562_ = l_Lean_instToJsonPosition_toJson(v_pos_2547_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v___x_2559_);
v___x_2565_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2566_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2548_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2559_);
v___x_2569_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2570_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2570_, 0, v_keepFullRange_2549_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2559_);
v___x_2573_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2574_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2550_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___x_2559_);
v___x_2577_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2578_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2578_, 0, v_isSilent_2551_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2559_);
v___x_2581_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_caption_2552_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2559_);
v___x_2585_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2554_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2559_);
v___x_2589_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2590_ = 1;
v___x_2591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2555_, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2589_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2559_);
v___x_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2559_);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2588_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2584_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2580_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2576_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2572_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2568_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2564_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2560_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2605_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2603_, v___x_2604_);
v___x_2606_ = l_Lean_Json_mkObj(v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Message_toJson(v_msg_2607_);
return v_res_2609_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = l_Lean_NameSet_empty;
v___x_2612_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_ctor_set(v___x_2613_, 2, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_instInhabitedMessageLog_default;
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__0(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_unsigned_to_nat(32u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__1(void){
_start:
{
size_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = ((size_t)5ULL);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_unsigned_to_nat(32u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2623_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__0, &l_Lean_MessageLog_empty___closed__0_once, _init_l_Lean_MessageLog_empty___closed__0);
v___x_2624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
lean_ctor_set(v___x_2624_, 2, v___x_2620_);
lean_ctor_set(v___x_2624_, 3, v___x_2620_);
lean_ctor_set_usize(v___x_2624_, 4, v___x_2619_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty___closed__2(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = l_Lean_NameSet_empty;
v___x_2626_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
lean_ctor_set(v___x_2627_, 2, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__2, &l_Lean_MessageLog_empty___closed__2_once, _init_l_Lean_MessageLog_empty___closed__2);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_2629_){
_start:
{
lean_object* v_unreported_2630_; 
v_unreported_2630_ = lean_ctor_get(v_self_2629_, 1);
lean_inc_ref(v_unreported_2630_);
return v_unreported_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_MessageLog_msgs(v_self_2631_);
lean_dec_ref(v_self_2631_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_2633_){
_start:
{
lean_object* v_reported_2634_; lean_object* v_unreported_2635_; lean_object* v___x_2636_; 
v_reported_2634_ = lean_ctor_get(v_x_2633_, 0);
lean_inc_ref(v_reported_2634_);
v_unreported_2635_ = lean_ctor_get(v_x_2633_, 1);
lean_inc_ref(v_unreported_2635_);
lean_dec_ref(v_x_2633_);
v___x_2636_ = l_Lean_PersistentArray_append___redArg(v_reported_2634_, v_unreported_2635_);
lean_dec_ref(v_unreported_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_2637_){
_start:
{
lean_object* v_unreported_2638_; uint8_t v___x_2639_; 
v_unreported_2638_ = lean_ctor_get(v_log_2637_, 1);
v___x_2639_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_2638_);
if (v___x_2639_ == 0)
{
uint8_t v___x_2640_; 
v___x_2640_ = 1;
return v___x_2640_;
}
else
{
uint8_t v___x_2641_; 
v___x_2641_ = 0;
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Lean_MessageLog_hasUnreported(v_log_2642_);
lean_dec_ref(v_log_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_2645_, lean_object* v_log_2646_){
_start:
{
lean_object* v_reported_2647_; lean_object* v_unreported_2648_; lean_object* v_loggedKinds_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2657_; 
v_reported_2647_ = lean_ctor_get(v_log_2646_, 0);
v_unreported_2648_ = lean_ctor_get(v_log_2646_, 1);
v_loggedKinds_2649_ = lean_ctor_get(v_log_2646_, 2);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_log_2646_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2651_ = v_log_2646_;
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_loggedKinds_2649_);
lean_inc(v_unreported_2648_);
lean_inc(v_reported_2647_);
lean_dec(v_log_2646_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = l_Lean_PersistentArray_push___redArg(v_unreported_2648_, v_msg_2645_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_reported_2647_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_loggedKinds_2649_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_2660_, lean_object* v_x_2661_){
_start:
{
if (lean_obj_tag(v_x_2661_) == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_b_u2082_2660_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; 
v___x_2663_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2664_, v_x_2665_);
lean_dec(v_x_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_2667_, lean_object* v_k_2668_, lean_object* v_t_2669_){
_start:
{
if (lean_obj_tag(v_t_2669_) == 0)
{
lean_object* v_size_2670_; lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v_l_2673_; lean_object* v_r_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2689_; 
v_size_2670_ = lean_ctor_get(v_t_2669_, 0);
v_k_2671_ = lean_ctor_get(v_t_2669_, 1);
v_v_2672_ = lean_ctor_get(v_t_2669_, 2);
v_l_2673_ = lean_ctor_get(v_t_2669_, 3);
v_r_2674_ = lean_ctor_get(v_t_2669_, 4);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_t_2669_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2676_ = v_t_2669_;
v_isShared_2677_ = v_isSharedCheck_2689_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_r_2674_);
lean_inc(v_l_2673_);
lean_inc(v_v_2672_);
lean_inc(v_k_2671_);
lean_inc(v_size_2670_);
lean_dec(v_t_2669_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2689_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; 
v___x_2678_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2668_, v_k_2671_);
switch(v___x_2678_)
{
case 0:
{
lean_object* v_impl_2679_; lean_object* v___x_2680_; 
lean_del_object(v___x_2676_);
lean_dec(v_size_2670_);
v_impl_2679_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2667_, v_k_2668_, v_l_2673_);
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2671_, v_v_2672_, v_impl_2679_, v_r_2674_);
return v___x_2680_;
}
case 1:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_val_2683_; lean_object* v___x_2685_; 
lean_dec(v_k_2671_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_v_2672_);
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2667_, v___x_2681_);
lean_dec_ref(v___x_2681_);
v_val_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_val_2683_);
lean_dec(v___x_2682_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 2, v_val_2683_);
lean_ctor_set(v___x_2676_, 1, v_k_2668_);
v___x_2685_ = v___x_2676_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_size_2670_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_k_2668_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_val_2683_);
lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_l_2673_);
lean_ctor_set(v_reuseFailAlloc_2686_, 4, v_r_2674_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
default: 
{
lean_object* v_impl_2687_; lean_object* v___x_2688_; 
lean_del_object(v___x_2676_);
lean_dec(v_size_2670_);
v_impl_2687_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2667_, v_k_2668_, v_r_2674_);
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2671_, v_v_2672_, v_l_2673_, v_impl_2687_);
return v___x_2688_;
}
}
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_val_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_2667_, v___x_2690_);
v_val_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_val_2692_);
lean_dec(v___x_2691_);
v___x_2693_ = lean_unsigned_to_nat(1u);
v___x_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_k_2668_);
lean_ctor_set(v___x_2694_, 2, v_val_2692_);
lean_ctor_set(v___x_2694_, 3, v_t_2669_);
lean_ctor_set(v___x_2694_, 4, v_t_2669_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_2695_, lean_object* v_x_2696_){
_start:
{
if (lean_obj_tag(v_x_2696_) == 0)
{
lean_object* v_k_2697_; lean_object* v_v_2698_; lean_object* v_l_2699_; lean_object* v_r_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_k_2697_ = lean_ctor_get(v_x_2696_, 1);
lean_inc(v_k_2697_);
v_v_2698_ = lean_ctor_get(v_x_2696_, 2);
lean_inc(v_v_2698_);
v_l_2699_ = lean_ctor_get(v_x_2696_, 3);
lean_inc(v_l_2699_);
v_r_2700_ = lean_ctor_get(v_x_2696_, 4);
lean_inc(v_r_2700_);
lean_dec_ref(v_x_2696_);
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2695_, v_l_2699_);
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_2698_, v_k_2697_, v___x_2701_);
v_init_2695_ = v___x_2702_;
v_x_2696_ = v_r_2700_;
goto _start;
}
else
{
return v_init_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_2704_, lean_object* v_l_u2082_2705_){
_start:
{
lean_object* v_reported_2706_; lean_object* v_unreported_2707_; lean_object* v_loggedKinds_2708_; lean_object* v_reported_2709_; lean_object* v_unreported_2710_; lean_object* v_loggedKinds_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2721_; 
v_reported_2706_ = lean_ctor_get(v_l_u2081_2704_, 0);
lean_inc_ref(v_reported_2706_);
v_unreported_2707_ = lean_ctor_get(v_l_u2081_2704_, 1);
lean_inc_ref(v_unreported_2707_);
v_loggedKinds_2708_ = lean_ctor_get(v_l_u2081_2704_, 2);
lean_inc(v_loggedKinds_2708_);
lean_dec_ref(v_l_u2081_2704_);
v_reported_2709_ = lean_ctor_get(v_l_u2082_2705_, 0);
v_unreported_2710_ = lean_ctor_get(v_l_u2082_2705_, 1);
v_loggedKinds_2711_ = lean_ctor_get(v_l_u2082_2705_, 2);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_l_u2082_2705_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2713_ = v_l_u2082_2705_;
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_loggedKinds_2711_);
lean_inc(v_unreported_2710_);
lean_inc(v_reported_2709_);
lean_dec(v_l_u2082_2705_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2721_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2715_ = l_Lean_PersistentArray_append___redArg(v_reported_2706_, v_reported_2709_);
lean_dec_ref(v_reported_2709_);
v___x_2716_ = l_Lean_PersistentArray_append___redArg(v_unreported_2707_, v_unreported_2710_);
lean_dec_ref(v_unreported_2710_);
v___x_2717_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_2708_, v_loggedKinds_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 2, v___x_2717_);
lean_ctor_set(v___x_2713_, 1, v___x_2716_);
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2719_ = v___x_2713_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_2722_, lean_object* v_k_2723_, lean_object* v_t_2724_, lean_object* v_hl_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_2722_, v_k_2723_, v_t_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_2727_, lean_object* v_t_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_2727_, v_t_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_2732_, size_t v_i_2733_, size_t v_stop_2734_){
_start:
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_usize_dec_eq(v_i_2733_, v_stop_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; uint8_t v_severity_2737_; uint8_t v___x_2738_; 
v___x_2736_ = lean_array_uget_borrowed(v_as_2732_, v_i_2733_);
v_severity_2737_ = lean_ctor_get_uint8(v___x_2736_, sizeof(void*)*5 + 1);
v___x_2738_ = 1;
if (v_severity_2737_ == 2)
{
return v___x_2738_;
}
else
{
if (v___x_2735_ == 0)
{
size_t v___x_2739_; size_t v___x_2740_; 
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2733_, v___x_2739_);
v_i_2733_ = v___x_2740_;
goto _start;
}
else
{
return v___x_2738_;
}
}
}
else
{
uint8_t v___x_2742_; 
v___x_2742_ = 0;
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_2743_, lean_object* v_i_2744_, lean_object* v_stop_2745_){
_start:
{
size_t v_i_boxed_2746_; size_t v_stop_boxed_2747_; uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_i_boxed_2746_ = lean_unbox_usize(v_i_2744_);
lean_dec(v_i_2744_);
v_stop_boxed_2747_ = lean_unbox_usize(v_stop_2745_);
lean_dec(v_stop_2745_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_2743_, v_i_boxed_2746_, v_stop_boxed_2747_);
lean_dec_ref(v_as_2743_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_cs_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_cs_2751_ = lean_ctor_get(v_x_2750_, 0);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v_cs_2751_);
v___x_2754_ = lean_nat_dec_lt(v___x_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
return v___x_2754_;
}
else
{
if (v___x_2754_ == 0)
{
return v___x_2754_;
}
else
{
size_t v___x_2755_; size_t v___x_2756_; uint8_t v___x_2757_; 
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = lean_usize_of_nat(v___x_2753_);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_2751_, v___x_2755_, v___x_2756_);
return v___x_2757_;
}
}
}
else
{
lean_object* v_vs_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_vs_2758_ = lean_ctor_get(v_x_2750_, 0);
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = lean_array_get_size(v_vs_2758_);
v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
return v___x_2761_;
}
else
{
if (v___x_2761_ == 0)
{
return v___x_2761_;
}
else
{
size_t v___x_2762_; size_t v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = lean_usize_of_nat(v___x_2760_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_2758_, v___x_2762_, v___x_2763_);
return v___x_2764_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_2765_, size_t v_i_2766_, size_t v_stop_2767_){
_start:
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_usize_dec_eq(v_i_2766_, v_stop_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = lean_array_uget_borrowed(v_as_2765_, v_i_2766_);
v___x_2770_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_2769_);
if (v___x_2770_ == 0)
{
size_t v___x_2771_; size_t v___x_2772_; 
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_add(v_i_2766_, v___x_2771_);
v_i_2766_ = v___x_2772_;
goto _start;
}
else
{
return v___x_2770_;
}
}
else
{
uint8_t v___x_2774_; 
v___x_2774_ = 0;
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_2775_, lean_object* v_i_2776_, lean_object* v_stop_2777_){
_start:
{
size_t v_i_boxed_2778_; size_t v_stop_boxed_2779_; uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_i_boxed_2778_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_stop_boxed_2779_ = lean_unbox_usize(v_stop_2777_);
lean_dec(v_stop_2777_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_2775_, v_i_boxed_2778_, v_stop_boxed_2779_);
lean_dec_ref(v_as_2775_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_2782_){
_start:
{
uint8_t v_res_2783_; lean_object* v_r_2784_; 
v_res_2783_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_2782_);
lean_dec_ref(v_x_2782_);
v_r_2784_ = lean_box(v_res_2783_);
return v_r_2784_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_2785_){
_start:
{
lean_object* v_root_2786_; lean_object* v_tail_2787_; uint8_t v___x_2788_; 
v_root_2786_ = lean_ctor_get(v_t_2785_, 0);
v_tail_2787_ = lean_ctor_get(v_t_2785_, 1);
v___x_2788_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_2786_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_array_get_size(v_tail_2787_);
v___x_2791_ = lean_nat_dec_lt(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
return v___x_2788_;
}
else
{
if (v___x_2791_ == 0)
{
return v___x_2788_;
}
else
{
size_t v___x_2792_; size_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = ((size_t)0ULL);
v___x_2793_ = lean_usize_of_nat(v___x_2790_);
v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_2787_, v___x_2792_, v___x_2793_);
return v___x_2794_;
}
}
}
else
{
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_2795_){
_start:
{
uint8_t v_res_2796_; lean_object* v_r_2797_; 
v_res_2796_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_2795_);
lean_dec_ref(v_t_2795_);
v_r_2797_ = lean_box(v_res_2796_);
return v_r_2797_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_2798_, lean_object* v_as_2799_, size_t v_i_2800_, size_t v_stop_2801_){
_start:
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_usize_dec_eq(v_i_2800_, v_stop_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; uint8_t v_severity_2804_; uint8_t v___x_2805_; 
v___x_2803_ = lean_array_uget_borrowed(v_as_2799_, v_i_2800_);
v_severity_2804_ = lean_ctor_get_uint8(v___x_2803_, sizeof(void*)*5 + 1);
v___x_2805_ = 1;
if (v_severity_2804_ == 2)
{
return v___x_2805_;
}
else
{
if (v___x_2798_ == 0)
{
size_t v___x_2806_; size_t v___x_2807_; 
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_add(v_i_2800_, v___x_2806_);
v_i_2800_ = v___x_2807_;
goto _start;
}
else
{
return v___x_2805_;
}
}
}
else
{
uint8_t v___x_2809_; 
v___x_2809_ = 0;
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_2810_, lean_object* v_as_2811_, lean_object* v_i_2812_, lean_object* v_stop_2813_){
_start:
{
uint8_t v___x_1884__boxed_2814_; size_t v_i_boxed_2815_; size_t v_stop_boxed_2816_; uint8_t v_res_2817_; lean_object* v_r_2818_; 
v___x_1884__boxed_2814_ = lean_unbox(v___x_2810_);
v_i_boxed_2815_ = lean_unbox_usize(v_i_2812_);
lean_dec(v_i_2812_);
v_stop_boxed_2816_ = lean_unbox_usize(v_stop_2813_);
lean_dec(v_stop_2813_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_2814_, v_as_2811_, v_i_boxed_2815_, v_stop_boxed_2816_);
lean_dec_ref(v_as_2811_);
v_r_2818_ = lean_box(v_res_2817_);
return v_r_2818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_2819_, lean_object* v_x_2820_){
_start:
{
if (lean_obj_tag(v_x_2820_) == 0)
{
lean_object* v_cs_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_cs_2821_ = lean_ctor_get(v_x_2820_, 0);
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = lean_array_get_size(v_cs_2821_);
v___x_2824_ = lean_nat_dec_lt(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
return v___x_2824_;
}
else
{
if (v___x_2824_ == 0)
{
return v___x_2824_;
}
else
{
size_t v___x_2825_; size_t v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = lean_usize_of_nat(v___x_2823_);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_2819_, v_cs_2821_, v___x_2825_, v___x_2826_);
return v___x_2827_;
}
}
}
else
{
lean_object* v_vs_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_vs_2828_ = lean_ctor_get(v_x_2820_, 0);
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = lean_array_get_size(v_vs_2828_);
v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
return v___x_2831_;
}
else
{
if (v___x_2831_ == 0)
{
return v___x_2831_;
}
else
{
size_t v___x_2832_; size_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = lean_usize_of_nat(v___x_2830_);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2819_, v_vs_2828_, v___x_2832_, v___x_2833_);
return v___x_2834_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_2835_, lean_object* v_as_2836_, size_t v_i_2837_, size_t v_stop_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_eq(v_i_2837_, v_stop_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = lean_array_uget_borrowed(v_as_2836_, v_i_2837_);
v___x_2841_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2835_, v___x_2840_);
if (v___x_2841_ == 0)
{
size_t v___x_2842_; size_t v___x_2843_; 
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2837_, v___x_2842_);
v_i_2837_ = v___x_2843_;
goto _start;
}
else
{
return v___x_2841_;
}
}
else
{
uint8_t v___x_2845_; 
v___x_2845_ = 0;
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2846_, lean_object* v_as_2847_, lean_object* v_i_2848_, lean_object* v_stop_2849_){
_start:
{
uint8_t v___x_1901__boxed_2850_; size_t v_i_boxed_2851_; size_t v_stop_boxed_2852_; uint8_t v_res_2853_; lean_object* v_r_2854_; 
v___x_1901__boxed_2850_ = lean_unbox(v___x_2846_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2848_);
lean_dec(v_i_2848_);
v_stop_boxed_2852_ = lean_unbox_usize(v_stop_2849_);
lean_dec(v_stop_2849_);
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_2850_, v_as_2847_, v_i_boxed_2851_, v_stop_boxed_2852_);
lean_dec_ref(v_as_2847_);
v_r_2854_ = lean_box(v_res_2853_);
return v_r_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_2855_, lean_object* v_x_2856_){
_start:
{
uint8_t v___x_1909__boxed_2857_; uint8_t v_res_2858_; lean_object* v_r_2859_; 
v___x_1909__boxed_2857_ = lean_unbox(v___x_2855_);
v_res_2858_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_2857_, v_x_2856_);
lean_dec_ref(v_x_2856_);
v_r_2859_ = lean_box(v_res_2858_);
return v_r_2859_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_2860_, lean_object* v_t_2861_){
_start:
{
lean_object* v_root_2862_; lean_object* v_tail_2863_; uint8_t v___x_2864_; 
v_root_2862_ = lean_ctor_get(v_t_2861_, 0);
v_tail_2863_ = lean_ctor_get(v_t_2861_, 1);
v___x_2864_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_2860_, v_root_2862_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2865_ = lean_unsigned_to_nat(0u);
v___x_2866_ = lean_array_get_size(v_tail_2863_);
v___x_2867_ = lean_nat_dec_lt(v___x_2865_, v___x_2866_);
if (v___x_2867_ == 0)
{
return v___x_2864_;
}
else
{
if (v___x_2867_ == 0)
{
return v___x_2864_;
}
else
{
size_t v___x_2868_; size_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = ((size_t)0ULL);
v___x_2869_ = lean_usize_of_nat(v___x_2866_);
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_2860_, v_tail_2863_, v___x_2868_, v___x_2869_);
return v___x_2870_;
}
}
}
else
{
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_2871_, lean_object* v_t_2872_){
_start:
{
uint8_t v___x_1952__boxed_2873_; uint8_t v_res_2874_; lean_object* v_r_2875_; 
v___x_1952__boxed_2873_ = lean_unbox(v___x_2871_);
v_res_2874_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_2873_, v_t_2872_);
lean_dec_ref(v_t_2872_);
v_r_2875_ = lean_box(v_res_2874_);
return v_r_2875_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_2876_){
_start:
{
lean_object* v_reported_2877_; lean_object* v_unreported_2878_; uint8_t v___x_2879_; 
v_reported_2877_ = lean_ctor_get(v_log_2876_, 0);
v_unreported_2878_ = lean_ctor_get(v_log_2876_, 1);
v___x_2879_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_2877_);
if (v___x_2879_ == 0)
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_2879_, v_unreported_2878_);
return v___x_2880_;
}
else
{
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_Lean_MessageLog_hasErrors(v_log_2881_);
lean_dec_ref(v_log_2881_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_2884_){
_start:
{
lean_object* v_reported_2885_; lean_object* v_unreported_2886_; lean_object* v_loggedKinds_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2898_; 
v_reported_2885_ = lean_ctor_get(v_log_2884_, 0);
v_unreported_2886_ = lean_ctor_get(v_log_2884_, 1);
v_loggedKinds_2887_ = lean_ctor_get(v_log_2884_, 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_log_2884_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2889_ = v_log_2884_;
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_loggedKinds_2887_);
lean_inc(v_unreported_2886_);
lean_inc(v_reported_2885_);
lean_dec(v_log_2884_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2891_ = l_Lean_PersistentArray_append___redArg(v_reported_2885_, v_unreported_2886_);
lean_dec_ref(v_unreported_2886_);
v___x_2892_ = lean_unsigned_to_nat(32u);
v___x_2893_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_dec_ref(v___x_2893_);
v___x_2894_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2894_);
lean_ctor_set(v___x_2889_, 0, v___x_2891_);
v___x_2896_ = v___x_2889_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_loggedKinds_2887_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_2899_, size_t v_i_2900_, lean_object* v_bs_2901_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_usize_dec_lt(v_i_2900_, v_sz_2899_);
if (v___x_2902_ == 0)
{
return v_bs_2901_;
}
else
{
lean_object* v_v_2903_; lean_object* v_fileName_2904_; lean_object* v_pos_2905_; lean_object* v_endPos_2906_; uint8_t v_keepFullRange_2907_; uint8_t v_severity_2908_; uint8_t v_isSilent_2909_; lean_object* v_caption_2910_; lean_object* v_data_2911_; lean_object* v___x_2912_; lean_object* v_bs_x27_2913_; lean_object* v___y_2915_; 
v_v_2903_ = lean_array_uget(v_bs_2901_, v_i_2900_);
v_fileName_2904_ = lean_ctor_get(v_v_2903_, 0);
v_pos_2905_ = lean_ctor_get(v_v_2903_, 1);
v_endPos_2906_ = lean_ctor_get(v_v_2903_, 2);
v_keepFullRange_2907_ = lean_ctor_get_uint8(v_v_2903_, sizeof(void*)*5);
v_severity_2908_ = lean_ctor_get_uint8(v_v_2903_, sizeof(void*)*5 + 1);
v_isSilent_2909_ = lean_ctor_get_uint8(v_v_2903_, sizeof(void*)*5 + 2);
v_caption_2910_ = lean_ctor_get(v_v_2903_, 3);
v_data_2911_ = lean_ctor_get(v_v_2903_, 4);
v___x_2912_ = lean_unsigned_to_nat(0u);
v_bs_x27_2913_ = lean_array_uset(v_bs_2901_, v_i_2900_, v___x_2912_);
if (v_severity_2908_ == 2)
{
lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2927_; 
lean_inc(v_data_2911_);
lean_inc_ref(v_caption_2910_);
lean_inc(v_endPos_2906_);
lean_inc_ref(v_pos_2905_);
lean_inc_ref(v_fileName_2904_);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_v_2903_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; lean_object* v_unused_2929_; lean_object* v_unused_2930_; lean_object* v_unused_2931_; lean_object* v_unused_2932_; 
v_unused_2928_ = lean_ctor_get(v_v_2903_, 4);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_v_2903_, 3);
lean_dec(v_unused_2929_);
v_unused_2930_ = lean_ctor_get(v_v_2903_, 2);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_v_2903_, 1);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_v_2903_, 0);
lean_dec(v_unused_2932_);
v___x_2921_ = v_v_2903_;
v_isShared_2922_ = v_isSharedCheck_2927_;
goto v_resetjp_2920_;
}
else
{
lean_dec(v_v_2903_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2927_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
uint8_t v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = 1;
if (v_isShared_2922_ == 0)
{
v___x_2925_ = v___x_2921_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_fileName_2904_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_pos_2905_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_endPos_2906_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_caption_2910_);
lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_data_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, sizeof(void*)*5, v_keepFullRange_2907_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, sizeof(void*)*5 + 2, v_isSilent_2909_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*5 + 1, v___x_2923_);
v___y_2915_ = v___x_2925_;
goto v___jp_2914_;
}
}
}
else
{
v___y_2915_ = v_v_2903_;
goto v___jp_2914_;
}
v___jp_2914_:
{
size_t v___x_2916_; size_t v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = ((size_t)1ULL);
v___x_2917_ = lean_usize_add(v_i_2900_, v___x_2916_);
v___x_2918_ = lean_array_uset(v_bs_x27_2913_, v_i_2900_, v___y_2915_);
v_i_2900_ = v___x_2917_;
v_bs_2901_ = v___x_2918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_bs_2935_){
_start:
{
size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_2936_, v_i_boxed_2937_, v_bs_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_2939_, size_t v_i_2940_, lean_object* v_bs_2941_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_usize_dec_lt(v_i_2940_, v_sz_2939_);
if (v___x_2942_ == 0)
{
return v_bs_2941_;
}
else
{
lean_object* v_v_2943_; lean_object* v___x_2944_; lean_object* v_bs_x27_2945_; lean_object* v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v_v_2943_ = lean_array_uget(v_bs_2941_, v_i_2940_);
v___x_2944_ = lean_unsigned_to_nat(0u);
v_bs_x27_2945_ = lean_array_uset(v_bs_2941_, v_i_2940_, v___x_2944_);
v___x_2946_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_2943_);
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_add(v_i_2940_, v___x_2947_);
v___x_2949_ = lean_array_uset(v_bs_x27_2945_, v_i_2940_, v___x_2946_);
v_i_2940_ = v___x_2948_;
v_bs_2941_ = v___x_2949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_object* v_cs_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2962_; 
v_cs_2952_ = lean_ctor_get(v_x_2951_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2951_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2954_ = v_x_2951_;
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_cs_2952_);
lean_dec(v_x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
size_t v_sz_2956_; size_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v_sz_2956_ = lean_array_size(v_cs_2952_);
v___x_2957_ = ((size_t)0ULL);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_2956_, v___x_2957_, v_cs_2952_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2958_);
v___x_2960_ = v___x_2954_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
lean_object* v_vs_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2973_; 
v_vs_2963_ = lean_ctor_get(v_x_2951_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_x_2951_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2965_ = v_x_2951_;
v_isShared_2966_ = v_isSharedCheck_2973_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_vs_2963_);
lean_dec(v_x_2951_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2973_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
size_t v_sz_2967_; size_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v_sz_2967_ = lean_array_size(v_vs_2963_);
v___x_2968_ = ((size_t)0ULL);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2967_, v___x_2968_, v_vs_2963_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2969_);
v___x_2971_ = v___x_2965_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2974_, lean_object* v_i_2975_, lean_object* v_bs_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2974_);
lean_dec(v_sz_2974_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_2977_, v_i_boxed_2978_, v_bs_2976_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_2980_){
_start:
{
lean_object* v_root_2981_; lean_object* v_tail_2982_; lean_object* v_size_2983_; size_t v_shift_2984_; lean_object* v_tailOff_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2996_; 
v_root_2981_ = lean_ctor_get(v_t_2980_, 0);
v_tail_2982_ = lean_ctor_get(v_t_2980_, 1);
v_size_2983_ = lean_ctor_get(v_t_2980_, 2);
v_shift_2984_ = lean_ctor_get_usize(v_t_2980_, 4);
v_tailOff_2985_ = lean_ctor_get(v_t_2980_, 3);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_t_2980_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2987_ = v_t_2980_;
v_isShared_2988_ = v_isSharedCheck_2996_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_tailOff_2985_);
lean_inc(v_size_2983_);
lean_inc(v_tail_2982_);
lean_inc(v_root_2981_);
lean_dec(v_t_2980_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2996_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; size_t v_sz_2990_; size_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2989_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_2981_);
v_sz_2990_ = lean_array_size(v_tail_2982_);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_2990_, v___x_2991_, v_tail_2982_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v___x_2992_);
lean_ctor_set(v___x_2987_, 0, v___x_2989_);
v___x_2994_ = v___x_2987_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_size_2983_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v_tailOff_2985_);
lean_ctor_set_usize(v_reuseFailAlloc_2995_, 4, v_shift_2984_);
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
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_unreported_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3010_; 
v___x_2998_ = lean_unsigned_to_nat(32u);
v___x_2999_ = lean_mk_empty_array_with_capacity(v___x_2998_);
lean_dec_ref(v___x_2999_);
v___x_3000_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3001_ = lean_ctor_get(v_log_2997_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_log_2997_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; lean_object* v_unused_3012_; 
v_unused_3011_ = lean_ctor_get(v_log_2997_, 2);
lean_dec(v_unused_3011_);
v_unused_3012_ = lean_ctor_get(v_log_2997_, 0);
lean_dec(v_unused_3012_);
v___x_3003_ = v_log_2997_;
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_unreported_3001_);
lean_dec(v_log_2997_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3005_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3001_);
v___x_3006_ = l_Lean_NameSet_empty;
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 2, v___x_3006_);
lean_ctor_set(v___x_3003_, 1, v___x_3005_);
lean_ctor_set(v___x_3003_, 0, v___x_3000_);
v___x_3008_ = v___x_3003_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3013_, size_t v_i_3014_, lean_object* v_bs_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_lt(v_i_3014_, v_sz_3013_);
if (v___x_3016_ == 0)
{
return v_bs_3015_;
}
else
{
lean_object* v_v_3017_; lean_object* v_fileName_3018_; lean_object* v_pos_3019_; lean_object* v_endPos_3020_; uint8_t v_keepFullRange_3021_; uint8_t v_severity_3022_; uint8_t v_isSilent_3023_; lean_object* v_caption_3024_; lean_object* v_data_3025_; lean_object* v___x_3026_; lean_object* v_bs_x27_3027_; lean_object* v___y_3029_; 
v_v_3017_ = lean_array_uget(v_bs_3015_, v_i_3014_);
v_fileName_3018_ = lean_ctor_get(v_v_3017_, 0);
v_pos_3019_ = lean_ctor_get(v_v_3017_, 1);
v_endPos_3020_ = lean_ctor_get(v_v_3017_, 2);
v_keepFullRange_3021_ = lean_ctor_get_uint8(v_v_3017_, sizeof(void*)*5);
v_severity_3022_ = lean_ctor_get_uint8(v_v_3017_, sizeof(void*)*5 + 1);
v_isSilent_3023_ = lean_ctor_get_uint8(v_v_3017_, sizeof(void*)*5 + 2);
v_caption_3024_ = lean_ctor_get(v_v_3017_, 3);
v_data_3025_ = lean_ctor_get(v_v_3017_, 4);
v___x_3026_ = lean_unsigned_to_nat(0u);
v_bs_x27_3027_ = lean_array_uset(v_bs_3015_, v_i_3014_, v___x_3026_);
if (v_severity_3022_ == 2)
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
lean_inc(v_data_3025_);
lean_inc_ref(v_caption_3024_);
lean_inc(v_endPos_3020_);
lean_inc_ref(v_pos_3019_);
lean_inc_ref(v_fileName_3018_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_v_3017_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; lean_object* v_unused_3043_; lean_object* v_unused_3044_; lean_object* v_unused_3045_; lean_object* v_unused_3046_; 
v_unused_3042_ = lean_ctor_get(v_v_3017_, 4);
lean_dec(v_unused_3042_);
v_unused_3043_ = lean_ctor_get(v_v_3017_, 3);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v_v_3017_, 2);
lean_dec(v_unused_3044_);
v_unused_3045_ = lean_ctor_get(v_v_3017_, 1);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v_v_3017_, 0);
lean_dec(v_unused_3046_);
v___x_3035_ = v_v_3017_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_v_3017_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
uint8_t v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = 0;
if (v_isShared_3036_ == 0)
{
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_fileName_3018_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_pos_3019_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v_endPos_3020_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v_caption_3024_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v_data_3025_);
lean_ctor_set_uint8(v_reuseFailAlloc_3040_, sizeof(void*)*5, v_keepFullRange_3021_);
lean_ctor_set_uint8(v_reuseFailAlloc_3040_, sizeof(void*)*5 + 2, v_isSilent_3023_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*5 + 1, v___x_3037_);
v___y_3029_ = v___x_3039_;
goto v___jp_3028_;
}
}
}
else
{
v___y_3029_ = v_v_3017_;
goto v___jp_3028_;
}
v___jp_3028_:
{
size_t v___x_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((size_t)1ULL);
v___x_3031_ = lean_usize_add(v_i_3014_, v___x_3030_);
v___x_3032_ = lean_array_uset(v_bs_x27_3027_, v_i_3014_, v___y_3029_);
v_i_3014_ = v___x_3031_;
v_bs_3015_ = v___x_3032_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3047_, lean_object* v_i_3048_, lean_object* v_bs_3049_){
_start:
{
size_t v_sz_boxed_3050_; size_t v_i_boxed_3051_; lean_object* v_res_3052_; 
v_sz_boxed_3050_ = lean_unbox_usize(v_sz_3047_);
lean_dec(v_sz_3047_);
v_i_boxed_3051_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3050_, v_i_boxed_3051_, v_bs_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3053_, size_t v_i_3054_, lean_object* v_bs_3055_){
_start:
{
uint8_t v___x_3056_; 
v___x_3056_ = lean_usize_dec_lt(v_i_3054_, v_sz_3053_);
if (v___x_3056_ == 0)
{
return v_bs_3055_;
}
else
{
lean_object* v_v_3057_; lean_object* v___x_3058_; lean_object* v_bs_x27_3059_; lean_object* v___x_3060_; size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v_v_3057_ = lean_array_uget(v_bs_3055_, v_i_3054_);
v___x_3058_ = lean_unsigned_to_nat(0u);
v_bs_x27_3059_ = lean_array_uset(v_bs_3055_, v_i_3054_, v___x_3058_);
v___x_3060_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3057_);
v___x_3061_ = ((size_t)1ULL);
v___x_3062_ = lean_usize_add(v_i_3054_, v___x_3061_);
v___x_3063_ = lean_array_uset(v_bs_x27_3059_, v_i_3054_, v___x_3060_);
v_i_3054_ = v___x_3062_;
v_bs_3055_ = v___x_3063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
lean_object* v_cs_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3076_; 
v_cs_3066_ = lean_ctor_get(v_x_3065_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_x_3065_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3068_ = v_x_3065_;
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_cs_3066_);
lean_dec(v_x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v_sz_3070_ = lean_array_size(v_cs_3066_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3070_, v___x_3071_, v_cs_3066_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3072_);
v___x_3074_ = v___x_3068_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_vs_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3087_; 
v_vs_3077_ = lean_ctor_get(v_x_3065_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_x_3065_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3079_ = v_x_3065_;
v_isShared_3080_ = v_isSharedCheck_3087_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_vs_3077_);
lean_dec(v_x_3065_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3087_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v_sz_3081_ = lean_array_size(v_vs_3077_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3081_, v___x_3082_, v_vs_3077_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 0, v___x_3083_);
v___x_3085_ = v___x_3079_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3088_, lean_object* v_i_3089_, lean_object* v_bs_3090_){
_start:
{
size_t v_sz_boxed_3091_; size_t v_i_boxed_3092_; lean_object* v_res_3093_; 
v_sz_boxed_3091_ = lean_unbox_usize(v_sz_3088_);
lean_dec(v_sz_3088_);
v_i_boxed_3092_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_res_3093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3091_, v_i_boxed_3092_, v_bs_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3094_){
_start:
{
lean_object* v_root_3095_; lean_object* v_tail_3096_; lean_object* v_size_3097_; size_t v_shift_3098_; lean_object* v_tailOff_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3110_; 
v_root_3095_ = lean_ctor_get(v_t_3094_, 0);
v_tail_3096_ = lean_ctor_get(v_t_3094_, 1);
v_size_3097_ = lean_ctor_get(v_t_3094_, 2);
v_shift_3098_ = lean_ctor_get_usize(v_t_3094_, 4);
v_tailOff_3099_ = lean_ctor_get(v_t_3094_, 3);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_t_3094_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3101_ = v_t_3094_;
v_isShared_3102_ = v_isSharedCheck_3110_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_tailOff_3099_);
lean_inc(v_size_3097_);
lean_inc(v_tail_3096_);
lean_inc(v_root_3095_);
lean_dec(v_t_3094_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3110_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3103_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3095_);
v_sz_3104_ = lean_array_size(v_tail_3096_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3104_, v___x_3105_, v_tail_3096_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3106_);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3108_ = v___x_3101_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_size_3097_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_tailOff_3099_);
lean_ctor_set_usize(v_reuseFailAlloc_3109_, 4, v_shift_3098_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3111_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_unreported_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3124_; 
v___x_3112_ = lean_unsigned_to_nat(32u);
v___x_3113_ = lean_mk_empty_array_with_capacity(v___x_3112_);
lean_dec_ref(v___x_3113_);
v___x_3114_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3115_ = lean_ctor_get(v_log_3111_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_log_3111_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3125_ = lean_ctor_get(v_log_3111_, 2);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_log_3111_, 0);
lean_dec(v_unused_3126_);
v___x_3117_ = v_log_3111_;
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_unreported_3115_);
lean_dec(v_log_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3115_);
v___x_3120_ = l_Lean_NameSet_empty;
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 2, v___x_3120_);
lean_ctor_set(v___x_3117_, 1, v___x_3119_);
lean_ctor_set(v___x_3117_, 0, v___x_3114_);
v___x_3122_ = v___x_3117_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3127_, size_t v_i_3128_, size_t v_stop_3129_, lean_object* v_b_3130_){
_start:
{
lean_object* v___y_3132_; uint8_t v___x_3136_; 
v___x_3136_ = lean_usize_dec_eq(v_i_3128_, v_stop_3129_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; uint8_t v_severity_3138_; 
v___x_3137_ = lean_array_uget_borrowed(v_as_3127_, v_i_3128_);
v_severity_3138_ = lean_ctor_get_uint8(v___x_3137_, sizeof(void*)*5 + 1);
if (v_severity_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_inc(v___x_3137_);
v___x_3139_ = l_Lean_PersistentArray_push___redArg(v_b_3130_, v___x_3137_);
v___y_3132_ = v___x_3139_;
goto v___jp_3131_;
}
else
{
v___y_3132_ = v_b_3130_;
goto v___jp_3131_;
}
}
else
{
return v_b_3130_;
}
v___jp_3131_:
{
size_t v___x_3133_; size_t v___x_3134_; 
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_add(v_i_3128_, v___x_3133_);
v_i_3128_ = v___x_3134_;
v_b_3130_ = v___y_3132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3140_, lean_object* v_i_3141_, lean_object* v_stop_3142_, lean_object* v_b_3143_){
_start:
{
size_t v_i_boxed_3144_; size_t v_stop_boxed_3145_; lean_object* v_res_3146_; 
v_i_boxed_3144_ = lean_unbox_usize(v_i_3141_);
lean_dec(v_i_3141_);
v_stop_boxed_3145_ = lean_unbox_usize(v_stop_3142_);
lean_dec(v_stop_3142_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3140_, v_i_boxed_3144_, v_stop_boxed_3145_, v_b_3143_);
lean_dec_ref(v_as_3140_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3147_, lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3147_) == 0)
{
lean_object* v_cs_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_cs_3149_ = lean_ctor_get(v_x_3147_, 0);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_array_get_size(v_cs_3149_);
v___x_3152_ = lean_nat_dec_lt(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
return v_x_3148_;
}
else
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_le(v___x_3151_, v___x_3151_);
if (v___x_3153_ == 0)
{
if (v___x_3152_ == 0)
{
return v_x_3148_;
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = lean_usize_of_nat(v___x_3151_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3149_, v___x_3154_, v___x_3155_, v_x_3148_);
return v___x_3156_;
}
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3151_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3149_, v___x_3157_, v___x_3158_, v_x_3148_);
return v___x_3159_;
}
}
}
else
{
lean_object* v_vs_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_vs_3160_ = lean_ctor_get(v_x_3147_, 0);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_array_get_size(v_vs_3160_);
v___x_3163_ = lean_nat_dec_lt(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
return v_x_3148_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_nat_dec_le(v___x_3162_, v___x_3162_);
if (v___x_3164_ == 0)
{
if (v___x_3163_ == 0)
{
return v_x_3148_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3162_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3160_, v___x_3165_, v___x_3166_, v_x_3148_);
return v___x_3167_;
}
}
else
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = lean_usize_of_nat(v___x_3162_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3160_, v___x_3168_, v___x_3169_, v_x_3148_);
return v___x_3170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3171_, size_t v_i_3172_, size_t v_stop_3173_, lean_object* v_b_3174_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_eq(v_i_3172_, v_stop_3173_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; size_t v___x_3178_; size_t v___x_3179_; 
v___x_3176_ = lean_array_uget_borrowed(v_as_3171_, v_i_3172_);
v___x_3177_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3176_, v_b_3174_);
v___x_3178_ = ((size_t)1ULL);
v___x_3179_ = lean_usize_add(v_i_3172_, v___x_3178_);
v_i_3172_ = v___x_3179_;
v_b_3174_ = v___x_3177_;
goto _start;
}
else
{
return v_b_3174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3181_, lean_object* v_i_3182_, lean_object* v_stop_3183_, lean_object* v_b_3184_){
_start:
{
size_t v_i_boxed_3185_; size_t v_stop_boxed_3186_; lean_object* v_res_3187_; 
v_i_boxed_3185_ = lean_unbox_usize(v_i_3182_);
lean_dec(v_i_3182_);
v_stop_boxed_3186_ = lean_unbox_usize(v_stop_3183_);
lean_dec(v_stop_3183_);
v_res_3187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3181_, v_i_boxed_3185_, v_stop_boxed_3186_, v_b_3184_);
lean_dec_ref(v_as_3181_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3188_, v_x_3189_);
lean_dec_ref(v_x_3188_);
return v_res_3190_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3192_, size_t v_x_3193_, size_t v_x_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 0)
{
lean_object* v_cs_3196_; lean_object* v___x_3197_; size_t v___x_3198_; lean_object* v_j_3199_; lean_object* v___x_3200_; size_t v___x_3201_; size_t v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; size_t v___x_3205_; size_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_cs_3196_ = lean_ctor_get(v_x_3192_, 0);
v___x_3197_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3198_ = lean_usize_shift_right(v_x_3193_, v_x_3194_);
v_j_3199_ = lean_usize_to_nat(v___x_3198_);
v___x_3200_ = lean_array_get_borrowed(v___x_3197_, v_cs_3196_, v_j_3199_);
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_shift_left(v___x_3201_, v_x_3194_);
v___x_3203_ = lean_usize_sub(v___x_3202_, v___x_3201_);
v___x_3204_ = lean_usize_land(v_x_3193_, v___x_3203_);
v___x_3205_ = ((size_t)5ULL);
v___x_3206_ = lean_usize_sub(v_x_3194_, v___x_3205_);
v___x_3207_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3200_, v___x_3204_, v___x_3206_, v_x_3195_);
v___x_3208_ = lean_unsigned_to_nat(1u);
v___x_3209_ = lean_nat_add(v_j_3199_, v___x_3208_);
lean_dec(v_j_3199_);
v___x_3210_ = lean_array_get_size(v_cs_3196_);
v___x_3211_ = lean_nat_dec_lt(v___x_3209_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v___x_3209_);
return v___x_3207_;
}
else
{
uint8_t v___x_3212_; 
v___x_3212_ = lean_nat_dec_le(v___x_3210_, v___x_3210_);
if (v___x_3212_ == 0)
{
if (v___x_3211_ == 0)
{
lean_dec(v___x_3209_);
return v___x_3207_;
}
else
{
size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_usize_of_nat(v___x_3209_);
lean_dec(v___x_3209_);
v___x_3214_ = lean_usize_of_nat(v___x_3210_);
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3196_, v___x_3213_, v___x_3214_, v___x_3207_);
return v___x_3215_;
}
}
else
{
size_t v___x_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_usize_of_nat(v___x_3209_);
lean_dec(v___x_3209_);
v___x_3217_ = lean_usize_of_nat(v___x_3210_);
v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3196_, v___x_3216_, v___x_3217_, v___x_3207_);
return v___x_3218_;
}
}
}
else
{
lean_object* v_vs_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_vs_3219_ = lean_ctor_get(v_x_3192_, 0);
v___x_3220_ = lean_usize_to_nat(v_x_3193_);
v___x_3221_ = lean_array_get_size(v_vs_3219_);
v___x_3222_ = lean_nat_dec_lt(v___x_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_dec(v___x_3220_);
return v_x_3195_;
}
else
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_nat_dec_le(v___x_3221_, v___x_3221_);
if (v___x_3223_ == 0)
{
if (v___x_3222_ == 0)
{
lean_dec(v___x_3220_);
return v_x_3195_;
}
else
{
size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_usize_of_nat(v___x_3220_);
lean_dec(v___x_3220_);
v___x_3225_ = lean_usize_of_nat(v___x_3221_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3219_, v___x_3224_, v___x_3225_, v_x_3195_);
return v___x_3226_;
}
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_usize_of_nat(v___x_3220_);
lean_dec(v___x_3220_);
v___x_3228_ = lean_usize_of_nat(v___x_3221_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3219_, v___x_3227_, v___x_3228_, v_x_3195_);
return v___x_3229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
size_t v_x_1528__boxed_3234_; size_t v_x_1529__boxed_3235_; lean_object* v_res_3236_; 
v_x_1528__boxed_3234_ = lean_unbox_usize(v_x_3231_);
lean_dec(v_x_3231_);
v_x_1529__boxed_3235_ = lean_unbox_usize(v_x_3232_);
lean_dec(v_x_3232_);
v_res_3236_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3230_, v_x_1528__boxed_3234_, v_x_1529__boxed_3235_, v_x_3233_);
lean_dec_ref(v_x_3230_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3237_, lean_object* v_init_3238_, lean_object* v_start_3239_){
_start:
{
lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = lean_unsigned_to_nat(0u);
v___x_3241_ = lean_nat_dec_eq(v_start_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v_root_3242_; lean_object* v_tail_3243_; size_t v_shift_3244_; lean_object* v_tailOff_3245_; uint8_t v___x_3246_; 
v_root_3242_ = lean_ctor_get(v_t_3237_, 0);
v_tail_3243_ = lean_ctor_get(v_t_3237_, 1);
v_shift_3244_ = lean_ctor_get_usize(v_t_3237_, 4);
v_tailOff_3245_ = lean_ctor_get(v_t_3237_, 3);
v___x_3246_ = lean_nat_dec_le(v_tailOff_3245_, v_start_3239_);
if (v___x_3246_ == 0)
{
size_t v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3247_ = lean_usize_of_nat(v_start_3239_);
v___x_3248_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3242_, v___x_3247_, v_shift_3244_, v_init_3238_);
v___x_3249_ = lean_array_get_size(v_tail_3243_);
v___x_3250_ = lean_nat_dec_lt(v___x_3240_, v___x_3249_);
if (v___x_3250_ == 0)
{
return v___x_3248_;
}
else
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_nat_dec_le(v___x_3249_, v___x_3249_);
if (v___x_3251_ == 0)
{
if (v___x_3250_ == 0)
{
return v___x_3248_;
}
else
{
size_t v___x_3252_; size_t v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = ((size_t)0ULL);
v___x_3253_ = lean_usize_of_nat(v___x_3249_);
v___x_3254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3243_, v___x_3252_, v___x_3253_, v___x_3248_);
return v___x_3254_;
}
}
else
{
size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((size_t)0ULL);
v___x_3256_ = lean_usize_of_nat(v___x_3249_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3243_, v___x_3255_, v___x_3256_, v___x_3248_);
return v___x_3257_;
}
}
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = lean_nat_sub(v_start_3239_, v_tailOff_3245_);
v___x_3259_ = lean_array_get_size(v_tail_3243_);
v___x_3260_ = lean_nat_dec_lt(v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_dec(v___x_3258_);
return v_init_3238_;
}
else
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_nat_dec_le(v___x_3259_, v___x_3259_);
if (v___x_3261_ == 0)
{
if (v___x_3260_ == 0)
{
lean_dec(v___x_3258_);
return v_init_3238_;
}
else
{
size_t v___x_3262_; size_t v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = lean_usize_of_nat(v___x_3258_);
lean_dec(v___x_3258_);
v___x_3263_ = lean_usize_of_nat(v___x_3259_);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3243_, v___x_3262_, v___x_3263_, v_init_3238_);
return v___x_3264_;
}
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_usize_of_nat(v___x_3258_);
lean_dec(v___x_3258_);
v___x_3266_ = lean_usize_of_nat(v___x_3259_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3243_, v___x_3265_, v___x_3266_, v_init_3238_);
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_root_3268_; lean_object* v_tail_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_root_3268_ = lean_ctor_get(v_t_3237_, 0);
v_tail_3269_ = lean_ctor_get(v_t_3237_, 1);
v___x_3270_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3268_, v_init_3238_);
v___x_3271_ = lean_array_get_size(v_tail_3269_);
v___x_3272_ = lean_nat_dec_lt(v___x_3240_, v___x_3271_);
if (v___x_3272_ == 0)
{
return v___x_3270_;
}
else
{
uint8_t v___x_3273_; 
v___x_3273_ = lean_nat_dec_le(v___x_3271_, v___x_3271_);
if (v___x_3273_ == 0)
{
if (v___x_3272_ == 0)
{
return v___x_3270_;
}
else
{
size_t v___x_3274_; size_t v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = ((size_t)0ULL);
v___x_3275_ = lean_usize_of_nat(v___x_3271_);
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3269_, v___x_3274_, v___x_3275_, v___x_3270_);
return v___x_3276_;
}
}
else
{
size_t v___x_3277_; size_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = ((size_t)0ULL);
v___x_3278_ = lean_usize_of_nat(v___x_3271_);
v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3269_, v___x_3277_, v___x_3278_, v___x_3270_);
return v___x_3279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3280_, lean_object* v_init_3281_, lean_object* v_start_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3280_, v_init_3281_, v_start_3282_);
lean_dec(v_start_3282_);
lean_dec_ref(v_t_3280_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3284_){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v_unreported_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3298_; 
v___x_3285_ = lean_unsigned_to_nat(32u);
v___x_3286_ = lean_mk_empty_array_with_capacity(v___x_3285_);
lean_dec_ref(v___x_3286_);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3289_ = lean_ctor_get(v_log_3284_, 1);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_log_3284_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; lean_object* v_unused_3300_; 
v_unused_3299_ = lean_ctor_get(v_log_3284_, 2);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_log_3284_, 0);
lean_dec(v_unused_3300_);
v___x_3291_ = v_log_3284_;
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_unreported_3289_);
lean_dec(v_log_3284_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3289_, v___x_3288_, v___x_3287_);
lean_dec_ref(v_unreported_3289_);
v___x_3294_ = l_Lean_NameSet_empty;
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 2, v___x_3294_);
lean_ctor_set(v___x_3291_, 1, v___x_3293_);
lean_ctor_set(v___x_3291_, 0, v___x_3288_);
v___x_3296_ = v___x_3291_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3301_, size_t v_i_3302_, size_t v_stop_3303_, lean_object* v_b_3304_){
_start:
{
lean_object* v___y_3306_; uint8_t v___x_3310_; 
v___x_3310_ = lean_usize_dec_eq(v_i_3302_, v_stop_3303_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; uint8_t v_severity_3312_; 
v___x_3311_ = lean_array_uget_borrowed(v_as_3301_, v_i_3302_);
v_severity_3312_ = lean_ctor_get_uint8(v___x_3311_, sizeof(void*)*5 + 1);
if (v_severity_3312_ == 1)
{
lean_object* v___x_3313_; 
lean_inc(v___x_3311_);
v___x_3313_ = l_Lean_PersistentArray_push___redArg(v_b_3304_, v___x_3311_);
v___y_3306_ = v___x_3313_;
goto v___jp_3305_;
}
else
{
v___y_3306_ = v_b_3304_;
goto v___jp_3305_;
}
}
else
{
return v_b_3304_;
}
v___jp_3305_:
{
size_t v___x_3307_; size_t v___x_3308_; 
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_add(v_i_3302_, v___x_3307_);
v_i_3302_ = v___x_3308_;
v_b_3304_ = v___y_3306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3314_, lean_object* v_i_3315_, lean_object* v_stop_3316_, lean_object* v_b_3317_){
_start:
{
size_t v_i_boxed_3318_; size_t v_stop_boxed_3319_; lean_object* v_res_3320_; 
v_i_boxed_3318_ = lean_unbox_usize(v_i_3315_);
lean_dec(v_i_3315_);
v_stop_boxed_3319_ = lean_unbox_usize(v_stop_3316_);
lean_dec(v_stop_3316_);
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3314_, v_i_boxed_3318_, v_stop_boxed_3319_, v_b_3317_);
lean_dec_ref(v_as_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3321_, lean_object* v_x_3322_){
_start:
{
if (lean_obj_tag(v_x_3321_) == 0)
{
lean_object* v_cs_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v_cs_3323_ = lean_ctor_get(v_x_3321_, 0);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_array_get_size(v_cs_3323_);
v___x_3326_ = lean_nat_dec_lt(v___x_3324_, v___x_3325_);
if (v___x_3326_ == 0)
{
return v_x_3322_;
}
else
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_nat_dec_le(v___x_3325_, v___x_3325_);
if (v___x_3327_ == 0)
{
if (v___x_3326_ == 0)
{
return v_x_3322_;
}
else
{
size_t v___x_3328_; size_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = ((size_t)0ULL);
v___x_3329_ = lean_usize_of_nat(v___x_3325_);
v___x_3330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3323_, v___x_3328_, v___x_3329_, v_x_3322_);
return v___x_3330_;
}
}
else
{
size_t v___x_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = ((size_t)0ULL);
v___x_3332_ = lean_usize_of_nat(v___x_3325_);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3323_, v___x_3331_, v___x_3332_, v_x_3322_);
return v___x_3333_;
}
}
}
else
{
lean_object* v_vs_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_vs_3334_ = lean_ctor_get(v_x_3321_, 0);
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = lean_array_get_size(v_vs_3334_);
v___x_3337_ = lean_nat_dec_lt(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
return v_x_3322_;
}
else
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_le(v___x_3336_, v___x_3336_);
if (v___x_3338_ == 0)
{
if (v___x_3337_ == 0)
{
return v_x_3322_;
}
else
{
size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((size_t)0ULL);
v___x_3340_ = lean_usize_of_nat(v___x_3336_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3334_, v___x_3339_, v___x_3340_, v_x_3322_);
return v___x_3341_;
}
}
else
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = lean_usize_of_nat(v___x_3336_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3334_, v___x_3342_, v___x_3343_, v_x_3322_);
return v___x_3344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3345_, size_t v_i_3346_, size_t v_stop_3347_, lean_object* v_b_3348_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_eq(v_i_3346_, v_stop_3347_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; size_t v___x_3352_; size_t v___x_3353_; 
v___x_3350_ = lean_array_uget_borrowed(v_as_3345_, v_i_3346_);
v___x_3351_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3350_, v_b_3348_);
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_add(v_i_3346_, v___x_3352_);
v_i_3346_ = v___x_3353_;
v_b_3348_ = v___x_3351_;
goto _start;
}
else
{
return v_b_3348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_stop_3357_, lean_object* v_b_3358_){
_start:
{
size_t v_i_boxed_3359_; size_t v_stop_boxed_3360_; lean_object* v_res_3361_; 
v_i_boxed_3359_ = lean_unbox_usize(v_i_3356_);
lean_dec(v_i_3356_);
v_stop_boxed_3360_ = lean_unbox_usize(v_stop_3357_);
lean_dec(v_stop_3357_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3355_, v_i_boxed_3359_, v_stop_boxed_3360_, v_b_3358_);
lean_dec_ref(v_as_3355_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3362_, lean_object* v_x_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3362_, v_x_3363_);
lean_dec_ref(v_x_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3365_, size_t v_x_3366_, size_t v_x_3367_, lean_object* v_x_3368_){
_start:
{
if (lean_obj_tag(v_x_3365_) == 0)
{
lean_object* v_cs_3369_; lean_object* v___x_3370_; size_t v___x_3371_; lean_object* v_j_3372_; lean_object* v___x_3373_; size_t v___x_3374_; size_t v___x_3375_; size_t v___x_3376_; size_t v___x_3377_; size_t v___x_3378_; size_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_cs_3369_ = lean_ctor_get(v_x_3365_, 0);
v___x_3370_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3371_ = lean_usize_shift_right(v_x_3366_, v_x_3367_);
v_j_3372_ = lean_usize_to_nat(v___x_3371_);
v___x_3373_ = lean_array_get_borrowed(v___x_3370_, v_cs_3369_, v_j_3372_);
v___x_3374_ = ((size_t)1ULL);
v___x_3375_ = lean_usize_shift_left(v___x_3374_, v_x_3367_);
v___x_3376_ = lean_usize_sub(v___x_3375_, v___x_3374_);
v___x_3377_ = lean_usize_land(v_x_3366_, v___x_3376_);
v___x_3378_ = ((size_t)5ULL);
v___x_3379_ = lean_usize_sub(v_x_3367_, v___x_3378_);
v___x_3380_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3373_, v___x_3377_, v___x_3379_, v_x_3368_);
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v_j_3372_, v___x_3381_);
lean_dec(v_j_3372_);
v___x_3383_ = lean_array_get_size(v_cs_3369_);
v___x_3384_ = lean_nat_dec_lt(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_dec(v___x_3382_);
return v___x_3380_;
}
else
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_nat_dec_le(v___x_3383_, v___x_3383_);
if (v___x_3385_ == 0)
{
if (v___x_3384_ == 0)
{
lean_dec(v___x_3382_);
return v___x_3380_;
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_usize_of_nat(v___x_3382_);
lean_dec(v___x_3382_);
v___x_3387_ = lean_usize_of_nat(v___x_3383_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3369_, v___x_3386_, v___x_3387_, v___x_3380_);
return v___x_3388_;
}
}
else
{
size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_usize_of_nat(v___x_3382_);
lean_dec(v___x_3382_);
v___x_3390_ = lean_usize_of_nat(v___x_3383_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3369_, v___x_3389_, v___x_3390_, v___x_3380_);
return v___x_3391_;
}
}
}
else
{
lean_object* v_vs_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v_vs_3392_ = lean_ctor_get(v_x_3365_, 0);
v___x_3393_ = lean_usize_to_nat(v_x_3366_);
v___x_3394_ = lean_array_get_size(v_vs_3392_);
v___x_3395_ = lean_nat_dec_lt(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_dec(v___x_3393_);
return v_x_3368_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_nat_dec_le(v___x_3394_, v___x_3394_);
if (v___x_3396_ == 0)
{
if (v___x_3395_ == 0)
{
lean_dec(v___x_3393_);
return v_x_3368_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = lean_usize_of_nat(v___x_3393_);
lean_dec(v___x_3393_);
v___x_3398_ = lean_usize_of_nat(v___x_3394_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3392_, v___x_3397_, v___x_3398_, v_x_3368_);
return v___x_3399_;
}
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_usize_of_nat(v___x_3393_);
lean_dec(v___x_3393_);
v___x_3401_ = lean_usize_of_nat(v___x_3394_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3392_, v___x_3400_, v___x_3401_, v_x_3368_);
return v___x_3402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v_x_3406_){
_start:
{
size_t v_x_1527__boxed_3407_; size_t v_x_1528__boxed_3408_; lean_object* v_res_3409_; 
v_x_1527__boxed_3407_ = lean_unbox_usize(v_x_3404_);
lean_dec(v_x_3404_);
v_x_1528__boxed_3408_ = lean_unbox_usize(v_x_3405_);
lean_dec(v_x_3405_);
v_res_3409_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3403_, v_x_1527__boxed_3407_, v_x_1528__boxed_3408_, v_x_3406_);
lean_dec_ref(v_x_3403_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3410_, lean_object* v_init_3411_, lean_object* v_start_3412_){
_start:
{
lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_nat_dec_eq(v_start_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v_root_3415_; lean_object* v_tail_3416_; size_t v_shift_3417_; lean_object* v_tailOff_3418_; uint8_t v___x_3419_; 
v_root_3415_ = lean_ctor_get(v_t_3410_, 0);
v_tail_3416_ = lean_ctor_get(v_t_3410_, 1);
v_shift_3417_ = lean_ctor_get_usize(v_t_3410_, 4);
v_tailOff_3418_ = lean_ctor_get(v_t_3410_, 3);
v___x_3419_ = lean_nat_dec_le(v_tailOff_3418_, v_start_3412_);
if (v___x_3419_ == 0)
{
size_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3420_ = lean_usize_of_nat(v_start_3412_);
v___x_3421_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3415_, v___x_3420_, v_shift_3417_, v_init_3411_);
v___x_3422_ = lean_array_get_size(v_tail_3416_);
v___x_3423_ = lean_nat_dec_lt(v___x_3413_, v___x_3422_);
if (v___x_3423_ == 0)
{
return v___x_3421_;
}
else
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_nat_dec_le(v___x_3422_, v___x_3422_);
if (v___x_3424_ == 0)
{
if (v___x_3423_ == 0)
{
return v___x_3421_;
}
else
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = lean_usize_of_nat(v___x_3422_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3416_, v___x_3425_, v___x_3426_, v___x_3421_);
return v___x_3427_;
}
}
else
{
size_t v___x_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = ((size_t)0ULL);
v___x_3429_ = lean_usize_of_nat(v___x_3422_);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3416_, v___x_3428_, v___x_3429_, v___x_3421_);
return v___x_3430_;
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_nat_sub(v_start_3412_, v_tailOff_3418_);
v___x_3432_ = lean_array_get_size(v_tail_3416_);
v___x_3433_ = lean_nat_dec_lt(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_dec(v___x_3431_);
return v_init_3411_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_nat_dec_le(v___x_3432_, v___x_3432_);
if (v___x_3434_ == 0)
{
if (v___x_3433_ == 0)
{
lean_dec(v___x_3431_);
return v_init_3411_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_usize_of_nat(v___x_3431_);
lean_dec(v___x_3431_);
v___x_3436_ = lean_usize_of_nat(v___x_3432_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3416_, v___x_3435_, v___x_3436_, v_init_3411_);
return v___x_3437_;
}
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = lean_usize_of_nat(v___x_3431_);
lean_dec(v___x_3431_);
v___x_3439_ = lean_usize_of_nat(v___x_3432_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3416_, v___x_3438_, v___x_3439_, v_init_3411_);
return v___x_3440_;
}
}
}
}
else
{
lean_object* v_root_3441_; lean_object* v_tail_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_root_3441_ = lean_ctor_get(v_t_3410_, 0);
v_tail_3442_ = lean_ctor_get(v_t_3410_, 1);
v___x_3443_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3441_, v_init_3411_);
v___x_3444_ = lean_array_get_size(v_tail_3442_);
v___x_3445_ = lean_nat_dec_lt(v___x_3413_, v___x_3444_);
if (v___x_3445_ == 0)
{
return v___x_3443_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_nat_dec_le(v___x_3444_, v___x_3444_);
if (v___x_3446_ == 0)
{
if (v___x_3445_ == 0)
{
return v___x_3443_;
}
else
{
size_t v___x_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = ((size_t)0ULL);
v___x_3448_ = lean_usize_of_nat(v___x_3444_);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3442_, v___x_3447_, v___x_3448_, v___x_3443_);
return v___x_3449_;
}
}
else
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___x_3444_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3442_, v___x_3450_, v___x_3451_, v___x_3443_);
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3453_, lean_object* v_init_3454_, lean_object* v_start_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3453_, v_init_3454_, v_start_3455_);
lean_dec(v_start_3455_);
lean_dec_ref(v_t_3453_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3457_){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v_unreported_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3471_; 
v___x_3458_ = lean_unsigned_to_nat(32u);
v___x_3459_ = lean_mk_empty_array_with_capacity(v___x_3458_);
lean_dec_ref(v___x_3459_);
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_obj_once(&l_Lean_MessageLog_empty___closed__1, &l_Lean_MessageLog_empty___closed__1_once, _init_l_Lean_MessageLog_empty___closed__1);
v_unreported_3462_ = lean_ctor_get(v_log_3457_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_log_3457_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; 
v_unused_3472_ = lean_ctor_get(v_log_3457_, 2);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_log_3457_, 0);
lean_dec(v_unused_3473_);
v___x_3464_ = v_log_3457_;
v_isShared_3465_ = v_isSharedCheck_3471_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_unreported_3462_);
lean_dec(v_log_3457_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3471_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3466_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3462_, v___x_3461_, v___x_3460_);
lean_dec_ref(v_unreported_3462_);
v___x_3467_ = l_Lean_NameSet_empty;
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 2, v___x_3467_);
lean_ctor_set(v___x_3464_, 1, v___x_3466_);
lean_ctor_set(v___x_3464_, 0, v___x_3461_);
v___x_3469_ = v___x_3464_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3474_, lean_object* v_log_3475_, lean_object* v_f_3476_){
_start:
{
lean_object* v_unreported_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v_unreported_3477_ = lean_ctor_get(v_log_3475_, 1);
lean_inc_ref(v_unreported_3477_);
lean_dec_ref(v_log_3475_);
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = l_Lean_PersistentArray_forM___redArg(v_inst_3474_, v_unreported_3477_, v_f_3476_, v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3480_, lean_object* v_inst_3481_, lean_object* v_log_3482_, lean_object* v_f_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_MessageLog_forM___redArg(v_inst_3481_, v_log_3482_, v_f_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3485_){
_start:
{
lean_object* v_unreported_3486_; lean_object* v___x_3487_; 
v_unreported_3486_ = lean_ctor_get(v_log_3485_, 1);
v___x_3487_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_MessageLog_toList(v_log_3488_);
lean_dec_ref(v_log_3488_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3490_){
_start:
{
lean_object* v_unreported_3491_; lean_object* v___x_3492_; 
v_unreported_3491_ = lean_ctor_get(v_log_3490_, 1);
v___x_3492_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_MessageLog_toArray(v_log_3493_);
lean_dec_ref(v_log_3493_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3495_){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_unsigned_to_nat(2u);
v___x_3497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v_msg_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3498_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v_msg_3498_);
v___x_3501_ = l_Lean_MessageData_nestD(v___x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = l_Lean_MessageData_ofExpr(v_e_3502_);
v___x_3504_ = l_Lean_indentD(v___x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3505_, lean_object* v_msg_3506_){
_start:
{
lean_object* v_env_3508_; lean_object* v_mctx_3509_; lean_object* v_lctx_3510_; lean_object* v_opts_3511_; lean_object* v_currNamespace_3512_; lean_object* v_openDecls_3513_; lean_object* v___x_3514_; lean_object* v_msg_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_env_3508_ = lean_ctor_get(v_ctx_3505_, 0);
v_mctx_3509_ = lean_ctor_get(v_ctx_3505_, 1);
v_lctx_3510_ = lean_ctor_get(v_ctx_3505_, 2);
v_opts_3511_ = lean_ctor_get(v_ctx_3505_, 3);
v_currNamespace_3512_ = lean_ctor_get(v_ctx_3505_, 4);
v_openDecls_3513_ = lean_ctor_get(v_ctx_3505_, 5);
lean_inc(v_openDecls_3513_);
lean_inc(v_currNamespace_3512_);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v_currNamespace_3512_);
lean_ctor_set(v___x_3514_, 1, v_openDecls_3513_);
v_msg_3515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3515_, 0, v___x_3514_);
lean_ctor_set(v_msg_3515_, 1, v_msg_3506_);
lean_inc_ref(v_opts_3511_);
lean_inc_ref(v_lctx_3510_);
lean_inc_ref(v_mctx_3509_);
lean_inc_ref(v_env_3508_);
v___x_3516_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3516_, 0, v_env_3508_);
lean_ctor_set(v___x_3516_, 1, v_mctx_3509_);
lean_ctor_set(v___x_3516_, 2, v_lctx_3510_);
lean_ctor_set(v___x_3516_, 3, v_opts_3511_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
v___x_3518_ = l_Lean_MessageData_format(v_msg_3515_, v___x_3517_);
v___x_3519_ = l_Std_Format_defWidth;
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = l_Std_Format_pretty(v___x_3518_, v___x_3519_, v___x_3520_, v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3522_, lean_object* v_msg_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3522_, v_msg_3523_);
lean_dec_ref(v_ctx_3522_);
return v_res_3525_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(lean_object* v_s_3526_, lean_object* v_a_3527_, uint8_t v_b_3528_){
_start:
{
lean_object* v_str_3529_; lean_object* v_startInclusive_3530_; lean_object* v_endExclusive_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_str_3529_ = lean_ctor_get(v_s_3526_, 0);
v_startInclusive_3530_ = lean_ctor_get(v_s_3526_, 1);
v_endExclusive_3531_ = lean_ctor_get(v_s_3526_, 2);
v___x_3532_ = lean_nat_sub(v_endExclusive_3531_, v_startInclusive_3530_);
v___x_3533_ = lean_nat_dec_eq(v_a_3527_, v___x_3532_);
lean_dec(v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; uint32_t v___x_3535_; uint32_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3534_ = lean_nat_add(v_startInclusive_3530_, v_a_3527_);
lean_dec(v_a_3527_);
v___x_3535_ = lean_string_utf8_get_fast(v_str_3529_, v___x_3534_);
v___x_3536_ = 10;
v___x_3537_ = lean_uint32_dec_eq(v___x_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_string_utf8_next_fast(v_str_3529_, v___x_3534_);
lean_dec(v___x_3534_);
v___x_3539_ = lean_nat_sub(v___x_3538_, v_startInclusive_3530_);
v_a_3527_ = v___x_3539_;
v_b_3528_ = v___x_3537_;
goto _start;
}
else
{
lean_dec(v___x_3534_);
return v___x_3537_;
}
}
else
{
lean_dec(v_a_3527_);
return v_b_3528_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg___boxed(lean_object* v_s_3541_, lean_object* v_a_3542_, lean_object* v_b_3543_){
_start:
{
uint8_t v_b_boxed_3544_; uint8_t v_res_3545_; lean_object* v_r_3546_; 
v_b_boxed_3544_ = lean_unbox(v_b_3543_);
v_res_3545_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3541_, v_a_3542_, v_b_boxed_3544_);
lean_dec_ref(v_s_3541_);
v_r_3546_ = lean_box(v_res_3545_);
return v_r_3546_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(lean_object* v_s_3547_){
_start:
{
lean_object* v_searcher_3548_; uint8_t v___x_3549_; uint8_t v___x_3550_; 
v_searcher_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = 0;
v___x_3550_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3547_, v_searcher_3548_, v___x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v_s_3551_){
_start:
{
uint8_t v_res_3552_; lean_object* v_r_3553_; 
v_res_3552_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v_s_3551_);
lean_dec_ref(v_s_3551_);
v_r_3553_ = lean_box(v_res_3552_);
return v_r_3553_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_3558_ = l_Lean_MessageData_ofFormat(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_3563_ = l_Lean_MessageData_ofFormat(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3565_ = l_Lean_MessageData_ofFormat(v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3566_, lean_object* v_maxInlineLength_3567_, lean_object* v_ctx_3568_){
_start:
{
lean_object* v_msg_3570_; lean_object* v___x_3571_; uint8_t v___y_3573_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v_msg_3570_ = l_Lean_MessageData_ofExpr(v_e_3566_);
lean_inc_ref(v_msg_3570_);
v___x_3571_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3568_, v_msg_3570_);
v___x_3581_ = lean_string_length(v___x_3571_);
v___x_3582_ = lean_nat_dec_lt(v_maxInlineLength_3567_, v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_string_utf8_byte_size(v___x_3571_);
v___x_3585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3571_);
lean_ctor_set(v___x_3585_, 1, v___x_3583_);
lean_ctor_set(v___x_3585_, 2, v___x_3584_);
v___x_3586_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3585_);
lean_dec_ref(v___x_3585_);
v___y_3573_ = v___x_3586_;
goto v___jp_3572_;
}
else
{
lean_dec_ref(v___x_3571_);
v___y_3573_ = v___x_3582_;
goto v___jp_3572_;
}
v___jp_3572_:
{
if (v___y_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3574_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v_msg_3570_);
v___x_3576_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = l_Lean_indentD(v_msg_3570_);
v___x_3579_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3587_, lean_object* v_maxInlineLength_3588_, lean_object* v_ctx_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_inlineExpr___lam__0(v_e_3587_, v_maxInlineLength_3588_, v_ctx_3589_);
lean_dec_ref(v_ctx_3589_);
lean_dec(v_maxInlineLength_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3595_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3596_ = l_Lean_MessageData_ofExpr(v_e_3592_);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3600_, lean_object* v_x_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_inlineExpr___lam__2(v_e_3600_, v_x_3601_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3604_, lean_object* v_maxInlineLength_3605_){
_start:
{
lean_object* v___f_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; 
lean_inc_ref(v_e_3604_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3606_, 0, v_e_3604_);
lean_closure_set(v___f_3606_, 1, v_maxInlineLength_3605_);
lean_inc_ref(v_e_3604_);
v___f_3607_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3607_, 0, v_e_3604_);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3608_, 0, v_e_3604_);
v___x_3609_ = l_Lean_MessageData_lazy(v___f_3606_, v___f_3607_, v___f_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(lean_object* v_s_3610_, lean_object* v_inst_3611_, lean_object* v_R_3612_, lean_object* v_a_3613_, uint8_t v_b_3614_, lean_object* v_c_3615_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___redArg(v_s_3610_, v_a_3613_, v_b_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0___boxed(lean_object* v_s_3617_, lean_object* v_inst_3618_, lean_object* v_R_3619_, lean_object* v_a_3620_, lean_object* v_b_3621_, lean_object* v_c_3622_){
_start:
{
uint8_t v_b_boxed_3623_; uint8_t v_res_3624_; lean_object* v_r_3625_; 
v_b_boxed_3623_ = lean_unbox(v_b_3621_);
v_res_3624_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__0_spec__0(v_s_3617_, v_inst_3618_, v_R_3619_, v_a_3620_, v_b_boxed_3623_, v_c_3622_);
lean_dec_ref(v_s_3617_);
v_r_3625_ = lean_box(v_res_3624_);
return v_r_3625_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_3630_ = l_Lean_MessageData_ofFormat(v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_3631_, lean_object* v_maxInlineLength_3632_, lean_object* v_ctx_3633_){
_start:
{
lean_object* v_msg_3635_; lean_object* v___x_3636_; uint8_t v___y_3638_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_msg_3635_ = l_Lean_MessageData_ofExpr(v_e_3631_);
lean_inc_ref(v_msg_3635_);
v___x_3636_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3633_, v_msg_3635_);
v___x_3644_ = lean_string_length(v___x_3636_);
v___x_3645_ = lean_nat_dec_lt(v_maxInlineLength_3632_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3647_ = lean_string_utf8_byte_size(v___x_3636_);
v___x_3648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3636_);
lean_ctor_set(v___x_3648_, 1, v___x_3646_);
lean_ctor_set(v___x_3648_, 2, v___x_3647_);
v___x_3649_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__0(v___x_3648_);
lean_dec_ref(v___x_3648_);
v___y_3638_ = v___x_3649_;
goto v___jp_3637_;
}
else
{
lean_dec_ref(v___x_3636_);
v___y_3638_ = v___x_3645_;
goto v___jp_3637_;
}
v___jp_3637_:
{
if (v___y_3638_ == 0)
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
lean_ctor_set(v___x_3640_, 1, v_msg_3635_);
v___x_3641_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_indentD(v_msg_3635_);
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_3650_, lean_object* v_maxInlineLength_3651_, lean_object* v_ctx_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_inlineExprTrailing___lam__0(v_e_3650_, v_maxInlineLength_3651_, v_ctx_3652_);
lean_dec_ref(v_ctx_3652_);
lean_dec(v_maxInlineLength_3651_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3658_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_3659_ = l_Lean_MessageData_ofExpr(v_e_3655_);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_3663_, lean_object* v_x_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_inlineExprTrailing___lam__2(v_e_3663_, v_x_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_3667_, lean_object* v_maxInlineLength_3668_){
_start:
{
lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___f_3671_; lean_object* v___x_3672_; 
lean_inc_ref(v_e_3667_);
v___f_3669_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3669_, 0, v_e_3667_);
lean_closure_set(v___f_3669_, 1, v_maxInlineLength_3668_);
lean_inc_ref(v_e_3667_);
v___f_3670_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3670_, 0, v_e_3667_);
v___f_3671_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3671_, 0, v_e_3667_);
v___x_3672_ = l_Lean_MessageData_lazy(v___f_3669_, v___f_3670_, v___f_3671_);
return v___x_3672_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_3677_ = l_Lean_MessageData_ofFormat(v___x_3676_);
return v___x_3677_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_3682_ = l_Lean_MessageData_ofFormat(v___x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_3683_){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3684_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_msg_3683_);
v___x_3686_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3685_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_msg_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_apply_1(v_inst_3688_, v_msg_3690_);
v___x_3692_ = lean_apply_2(v_inst_3689_, lean_box(0), v___x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_3693_, lean_object* v_inst_3694_){
_start:
{
lean_object* v___f_3695_; 
v___f_3695_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3695_, 0, v_inst_3694_);
lean_closure_set(v___f_3695_, 1, v_inst_3693_);
return v___f_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_3696_, lean_object* v_n_3697_, lean_object* v_inst_3698_, lean_object* v_inst_3699_){
_start:
{
lean_object* v___f_3700_; 
v___f_3700_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3700_, 0, v_inst_3699_);
lean_closure_set(v___f_3700_, 1, v_inst_3698_);
return v___f_3700_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_unsigned_to_nat(32u);
v___x_3702_ = lean_mk_empty_array_with_capacity(v___x_3701_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3704_ = ((size_t)5ULL);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_unsigned_to_nat(32u);
v___x_3707_ = lean_mk_empty_array_with_capacity(v___x_3706_);
v___x_3708_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_3709_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
lean_ctor_set(v___x_3709_, 1, v___x_3707_);
lean_ctor_set(v___x_3709_, 2, v___x_3705_);
lean_ctor_set(v___x_3709_, 3, v___x_3705_);
lean_ctor_set_usize(v___x_3709_, 4, v___x_3704_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3710_ = lean_box(1);
v___x_3711_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_3712_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_3713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v___x_3711_);
lean_ctor_set(v___x_3713_, 2, v___x_3710_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_3714_, lean_object* v_msgData_3715_, lean_object* v_toPure_3716_, lean_object* v_opts_3717_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3718_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_3719_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_3720_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3720_, 0, v_env_3714_);
lean_ctor_set(v___x_3720_, 1, v___x_3718_);
lean_ctor_set(v___x_3720_, 2, v___x_3719_);
lean_ctor_set(v___x_3720_, 3, v_opts_3717_);
v___x_3721_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v_msgData_3715_);
v___x_3722_ = lean_apply_2(v_toPure_3716_, lean_box(0), v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_3723_, lean_object* v_toPure_3724_, lean_object* v_toBind_3725_, lean_object* v_inst_3726_, lean_object* v_env_3727_){
_start:
{
lean_object* v___f_3728_; lean_object* v___x_3729_; 
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3728_, 0, v_env_3727_);
lean_closure_set(v___f_3728_, 1, v_msgData_3723_);
lean_closure_set(v___f_3728_, 2, v_toPure_3724_);
v___x_3729_ = lean_apply_4(v_toBind_3725_, lean_box(0), lean_box(0), v_inst_3726_, v___f_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_3730_, lean_object* v_inst_3731_, lean_object* v_inst_3732_, lean_object* v_msgData_3733_){
_start:
{
lean_object* v_toApplicative_3734_; lean_object* v_toBind_3735_; lean_object* v_getEnv_3736_; lean_object* v_toPure_3737_; lean_object* v___f_3738_; lean_object* v___x_3739_; 
v_toApplicative_3734_ = lean_ctor_get(v_inst_3730_, 0);
lean_inc_ref(v_toApplicative_3734_);
v_toBind_3735_ = lean_ctor_get(v_inst_3730_, 1);
lean_inc(v_toBind_3735_);
lean_dec_ref(v_inst_3730_);
v_getEnv_3736_ = lean_ctor_get(v_inst_3731_, 0);
lean_inc(v_getEnv_3736_);
lean_dec_ref(v_inst_3731_);
v_toPure_3737_ = lean_ctor_get(v_toApplicative_3734_, 1);
lean_inc(v_toPure_3737_);
lean_dec_ref(v_toApplicative_3734_);
lean_inc(v_toBind_3735_);
v___f_3738_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3738_, 0, v_msgData_3733_);
lean_closure_set(v___f_3738_, 1, v_toPure_3737_);
lean_closure_set(v___f_3738_, 2, v_toBind_3735_);
lean_closure_set(v___f_3738_, 3, v_inst_3732_);
v___x_3739_ = lean_apply_4(v_toBind_3735_, lean_box(0), lean_box(0), v_getEnv_3736_, v___f_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_3740_, lean_object* v_inst_3741_, lean_object* v_inst_3742_, lean_object* v_inst_3743_, lean_object* v_msgData_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_addMessageContextPartial___redArg(v_inst_3741_, v_inst_3742_, v_inst_3743_, v_msgData_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_3746_, lean_object* v_mctx_3747_, lean_object* v_lctx_3748_, lean_object* v_msgData_3749_, lean_object* v_toPure_3750_, lean_object* v_opts_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3752_, 0, v_env_3746_);
lean_ctor_set(v___x_3752_, 1, v_mctx_3747_);
lean_ctor_set(v___x_3752_, 2, v_lctx_3748_);
lean_ctor_set(v___x_3752_, 3, v_opts_3751_);
v___x_3753_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v_msgData_3749_);
v___x_3754_ = lean_apply_2(v_toPure_3750_, lean_box(0), v___x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_3755_, lean_object* v_mctx_3756_, lean_object* v_msgData_3757_, lean_object* v_toPure_3758_, lean_object* v_toBind_3759_, lean_object* v_inst_3760_, lean_object* v_lctx_3761_){
_start:
{
lean_object* v___f_3762_; lean_object* v___x_3763_; 
v___f_3762_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3762_, 0, v_env_3755_);
lean_closure_set(v___f_3762_, 1, v_mctx_3756_);
lean_closure_set(v___f_3762_, 2, v_lctx_3761_);
lean_closure_set(v___f_3762_, 3, v_msgData_3757_);
lean_closure_set(v___f_3762_, 4, v_toPure_3758_);
v___x_3763_ = lean_apply_4(v_toBind_3759_, lean_box(0), lean_box(0), v_inst_3760_, v___f_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_3764_, lean_object* v_msgData_3765_, lean_object* v_toPure_3766_, lean_object* v_toBind_3767_, lean_object* v_inst_3768_, lean_object* v_inst_3769_, lean_object* v_mctx_3770_){
_start:
{
lean_object* v___f_3771_; lean_object* v___x_3772_; 
lean_inc(v_toBind_3767_);
v___f_3771_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3771_, 0, v_env_3764_);
lean_closure_set(v___f_3771_, 1, v_mctx_3770_);
lean_closure_set(v___f_3771_, 2, v_msgData_3765_);
lean_closure_set(v___f_3771_, 3, v_toPure_3766_);
lean_closure_set(v___f_3771_, 4, v_toBind_3767_);
lean_closure_set(v___f_3771_, 5, v_inst_3768_);
v___x_3772_ = lean_apply_4(v_toBind_3767_, lean_box(0), lean_box(0), v_inst_3769_, v___f_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_3773_, lean_object* v_msgData_3774_, lean_object* v_toPure_3775_, lean_object* v_toBind_3776_, lean_object* v_inst_3777_, lean_object* v_inst_3778_, lean_object* v_env_3779_){
_start:
{
lean_object* v_getMCtx_3780_; lean_object* v___f_3781_; lean_object* v___x_3782_; 
v_getMCtx_3780_ = lean_ctor_get(v_inst_3773_, 0);
lean_inc(v_getMCtx_3780_);
lean_dec_ref(v_inst_3773_);
lean_inc(v_toBind_3776_);
v___f_3781_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3781_, 0, v_env_3779_);
lean_closure_set(v___f_3781_, 1, v_msgData_3774_);
lean_closure_set(v___f_3781_, 2, v_toPure_3775_);
lean_closure_set(v___f_3781_, 3, v_toBind_3776_);
lean_closure_set(v___f_3781_, 4, v_inst_3777_);
lean_closure_set(v___f_3781_, 5, v_inst_3778_);
v___x_3782_ = lean_apply_4(v_toBind_3776_, lean_box(0), lean_box(0), v_getMCtx_3780_, v___f_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_3783_, lean_object* v_inst_3784_, lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_inst_3787_, lean_object* v_msgData_3788_){
_start:
{
lean_object* v_toApplicative_3789_; lean_object* v_toBind_3790_; lean_object* v_getEnv_3791_; lean_object* v_toPure_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; 
v_toApplicative_3789_ = lean_ctor_get(v_inst_3783_, 0);
lean_inc_ref(v_toApplicative_3789_);
v_toBind_3790_ = lean_ctor_get(v_inst_3783_, 1);
lean_inc(v_toBind_3790_);
lean_dec_ref(v_inst_3783_);
v_getEnv_3791_ = lean_ctor_get(v_inst_3784_, 0);
lean_inc(v_getEnv_3791_);
lean_dec_ref(v_inst_3784_);
v_toPure_3792_ = lean_ctor_get(v_toApplicative_3789_, 1);
lean_inc(v_toPure_3792_);
lean_dec_ref(v_toApplicative_3789_);
lean_inc(v_toBind_3790_);
v___f_3793_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_3793_, 0, v_inst_3785_);
lean_closure_set(v___f_3793_, 1, v_msgData_3788_);
lean_closure_set(v___f_3793_, 2, v_toPure_3792_);
lean_closure_set(v___f_3793_, 3, v_toBind_3790_);
lean_closure_set(v___f_3793_, 4, v_inst_3787_);
lean_closure_set(v___f_3793_, 5, v_inst_3786_);
v___x_3794_ = lean_apply_4(v_toBind_3790_, lean_box(0), lean_box(0), v_getEnv_3791_, v___f_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_3795_, lean_object* v_inst_3796_, lean_object* v_inst_3797_, lean_object* v_inst_3798_, lean_object* v_inst_3799_, lean_object* v_inst_3800_, lean_object* v_msgData_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_addMessageContextFull___redArg(v_inst_3796_, v_inst_3797_, v_inst_3798_, v_inst_3799_, v_inst_3800_, v_msgData_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_3807_);
lean_dec_ref(v_s_3807_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_3809_, lean_object* v___x_3810_, lean_object* v___x_3811_, lean_object* v_a_3812_, lean_object* v_b_3813_){
_start:
{
lean_object* v_it_3815_; lean_object* v_startInclusive_3816_; lean_object* v_endExclusive_3817_; 
if (lean_obj_tag(v_a_3812_) == 0)
{
lean_object* v_currPos_3823_; lean_object* v_searcher_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3850_; 
v_currPos_3823_ = lean_ctor_get(v_a_3812_, 0);
v_searcher_3824_ = lean_ctor_get(v_a_3812_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_a_3812_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3826_ = v_a_3812_;
v_isShared_3827_ = v_isSharedCheck_3850_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_searcher_3824_);
lean_inc(v_currPos_3823_);
lean_dec(v_a_3812_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3850_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v_startInclusive_3828_; lean_object* v_endExclusive_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_startInclusive_3828_ = lean_ctor_get(v___x_3810_, 1);
v_endExclusive_3829_ = lean_ctor_get(v___x_3810_, 2);
v___x_3830_ = lean_nat_sub(v_endExclusive_3829_, v_startInclusive_3828_);
v___x_3831_ = lean_nat_dec_eq(v_searcher_3824_, v___x_3830_);
lean_dec(v___x_3830_);
if (v___x_3831_ == 0)
{
uint32_t v___x_3832_; uint32_t v___x_3833_; uint8_t v___x_3834_; 
v___x_3832_ = 10;
v___x_3833_ = lean_string_utf8_get_fast(v_str_3809_, v_searcher_3824_);
v___x_3834_ = lean_uint32_dec_eq(v___x_3833_, v___x_3832_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = lean_string_utf8_next_fast(v_str_3809_, v_searcher_3824_);
lean_dec(v_searcher_3824_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 1, v___x_3835_);
v___x_3837_ = v___x_3826_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_currPos_3823_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
v_a_3812_ = v___x_3837_;
goto _start;
}
}
else
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v_slice_3843_; lean_object* v_nextIt_3845_; 
v___x_3840_ = lean_string_utf8_next_fast(v_str_3809_, v_searcher_3824_);
v___x_3841_ = lean_nat_sub(v___x_3840_, v_searcher_3824_);
v___x_3842_ = lean_nat_add(v_searcher_3824_, v___x_3841_);
lean_dec(v___x_3841_);
v_slice_3843_ = l_String_Slice_subslice_x21(v___x_3810_, v_currPos_3823_, v_searcher_3824_);
lean_inc(v___x_3842_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 1, v___x_3842_);
lean_ctor_set(v___x_3826_, 0, v___x_3842_);
v_nextIt_3845_ = v___x_3826_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3842_);
v_nextIt_3845_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v_startInclusive_3846_; lean_object* v_endExclusive_3847_; 
v_startInclusive_3846_ = lean_ctor_get(v_slice_3843_, 0);
lean_inc(v_startInclusive_3846_);
v_endExclusive_3847_ = lean_ctor_get(v_slice_3843_, 1);
lean_inc(v_endExclusive_3847_);
lean_dec_ref(v_slice_3843_);
v_it_3815_ = v_nextIt_3845_;
v_startInclusive_3816_ = v_startInclusive_3846_;
v_endExclusive_3817_ = v_endExclusive_3847_;
goto v___jp_3814_;
}
}
}
else
{
lean_object* v___x_3849_; 
lean_del_object(v___x_3826_);
lean_dec(v_searcher_3824_);
v___x_3849_ = lean_box(1);
lean_inc(v___x_3811_);
v_it_3815_ = v___x_3849_;
v_startInclusive_3816_ = v_currPos_3823_;
v_endExclusive_3817_ = v___x_3811_;
goto v___jp_3814_;
}
}
}
else
{
lean_dec(v___x_3811_);
return v_b_3813_;
}
v___jp_3814_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3818_ = lean_string_utf8_extract(v_str_3809_, v_startInclusive_3816_, v_endExclusive_3817_);
lean_dec(v_endExclusive_3817_);
lean_dec(v_startInclusive_3816_);
v___x_3819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
v___x_3820_ = l_Lean_MessageData_ofFormat(v___x_3819_);
v___x_3821_ = lean_array_push(v_b_3813_, v___x_3820_);
v_a_3812_ = v_it_3815_;
v_b_3813_ = v___x_3821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_3851_, lean_object* v___x_3852_, lean_object* v___x_3853_, lean_object* v_a_3854_, lean_object* v_b_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3851_, v___x_3852_, v___x_3853_, v_a_3854_, v_b_3855_);
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_str_3851_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_3859_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v_lines_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3860_ = lean_unsigned_to_nat(0u);
v___x_3861_ = lean_string_utf8_byte_size(v_str_3859_);
lean_inc_ref(v_str_3859_);
v___x_3862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3862_, 0, v_str_3859_);
lean_ctor_set(v___x_3862_, 1, v___x_3860_);
lean_ctor_set(v___x_3862_, 2, v___x_3861_);
v_lines_3863_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_3862_);
v___x_3864_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_3865_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3859_, v___x_3862_, v___x_3861_, v_lines_3863_, v___x_3864_);
lean_dec_ref(v___x_3862_);
lean_dec_ref(v_str_3859_);
v___x_3866_ = lean_array_to_list(v___x_3865_);
v___x_3867_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3868_ = l_Lean_MessageData_joinSep(v___x_3866_, v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_3869_, lean_object* v___x_3870_, lean_object* v___x_3871_, lean_object* v_inst_3872_, lean_object* v_R_3873_, lean_object* v_a_3874_, lean_object* v_b_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_3869_, v___x_3870_, v___x_3871_, v_a_3874_, v_b_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_3877_, lean_object* v___x_3878_, lean_object* v___x_3879_, lean_object* v_inst_3880_, lean_object* v_R_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_3877_, v___x_3878_, v___x_3879_, v_inst_3880_, v_R_3881_, v_a_3882_, v_b_3883_);
lean_dec_ref(v___x_3878_);
lean_dec_ref(v_str_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_3885_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_3887_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_3887_, 0, lean_box(0));
lean_closure_set(v___x_3887_, 1, lean_box(0));
lean_closure_set(v___x_3887_, 2, lean_box(0));
lean_closure_set(v___x_3887_, 3, v___x_3886_);
lean_closure_set(v___x_3887_, 4, v_inst_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_3888_, lean_object* v_inst_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_3897_){
_start:
{
lean_object* v___f_3898_; 
v___f_3898_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_instToMessageDataTSyntax(v_k_3899_);
lean_dec(v_k_3899_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_3905_, lean_object* v_as_3906_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_box(0);
v___x_3908_ = l_List_mapTR_loop___redArg(v_inst_3905_, v_as_3906_, v___x_3907_);
v___x_3909_ = l_Lean_MessageData_ofList(v___x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_3910_){
_start:
{
lean_object* v___f_3911_; 
v___f_3911_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3911_, 0, v_inst_3910_);
return v___f_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_3912_, lean_object* v_inst_3913_){
_start:
{
lean_object* v___f_3914_; 
v___f_3914_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3914_, 0, v_inst_3913_);
return v___f_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_3915_, lean_object* v_as_3916_){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3917_ = lean_array_to_list(v_as_3916_);
v___x_3918_ = lean_box(0);
v___x_3919_ = l_List_mapTR_loop___redArg(v_inst_3915_, v___x_3917_, v___x_3918_);
v___x_3920_ = l_Lean_MessageData_ofList(v___x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_3921_){
_start:
{
lean_object* v___f_3922_; 
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3922_, 0, v_inst_3921_);
return v___f_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_3923_, lean_object* v_inst_3924_){
_start:
{
lean_object* v___f_3925_; 
v___f_3925_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3925_, 0, v_inst_3924_);
return v___f_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_3926_, lean_object* v_acc_3927_, lean_object* v_recur_3928_){
_start:
{
lean_object* v_array_3929_; lean_object* v_start_3930_; lean_object* v_stop_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3944_; 
v_array_3929_ = lean_ctor_get(v_it_3926_, 0);
v_start_3930_ = lean_ctor_get(v_it_3926_, 1);
v_stop_3931_ = lean_ctor_get(v_it_3926_, 2);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_it_3926_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3933_ = v_it_3926_;
v_isShared_3934_ = v_isSharedCheck_3944_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_stop_3931_);
lean_inc(v_start_3930_);
lean_inc(v_array_3929_);
lean_dec(v_it_3926_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3944_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
uint8_t v___x_3935_; 
v___x_3935_ = lean_nat_dec_lt(v_start_3930_, v_stop_3931_);
if (v___x_3935_ == 0)
{
lean_del_object(v___x_3933_);
lean_dec(v_stop_3931_);
lean_dec(v_start_3930_);
lean_dec_ref(v_array_3929_);
lean_dec_ref(v_recur_3928_);
return v_acc_3927_;
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = lean_nat_add(v_start_3930_, v___x_3936_);
lean_inc_ref(v_array_3929_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v___x_3937_);
v___x_3939_ = v___x_3933_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_array_3929_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_stop_3931_);
v___x_3939_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_array_fget(v_array_3929_, v_start_3930_);
lean_dec(v_start_3930_);
lean_dec_ref(v_array_3929_);
v___x_3941_ = lean_array_push(v_acc_3927_, v___x_3940_);
v___x_3942_ = lean_apply_3(v_recur_3928_, v___x_3939_, v___x_3941_, lean_box(0));
return v___x_3942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_3947_, lean_object* v_inst_3948_, lean_object* v_as_3949_){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3950_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_3951_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_3947_, v_as_3949_, v___x_3950_);
v___x_3952_ = lean_array_to_list(v___x_3951_);
v___x_3953_ = lean_box(0);
v___x_3954_ = l_List_mapTR_loop___redArg(v_inst_3948_, v___x_3952_, v___x_3953_);
v___x_3955_ = l_Lean_MessageData_ofList(v___x_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_3957_){
_start:
{
lean_object* v___f_3958_; lean_object* v___f_3959_; 
v___f_3958_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_3959_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3959_, 0, v___f_3958_);
lean_closure_set(v___f_3959_, 1, v_inst_3957_);
return v___f_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_3960_, lean_object* v_inst_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_3967_ = l_Lean_MessageData_ofFormat(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_3971_ = l_Lean_MessageData_ofFormat(v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_3972_, lean_object* v_x_3973_){
_start:
{
if (lean_obj_tag(v_x_3973_) == 0)
{
lean_object* v___x_3974_; 
lean_dec_ref(v_inst_3972_);
v___x_3974_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_3974_;
}
else
{
lean_object* v_val_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_val_3975_ = lean_ctor_get(v_x_3973_, 0);
lean_inc(v_val_3975_);
lean_dec_ref(v_x_3973_);
v___x_3976_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_3977_ = lean_apply_1(v_inst_3972_, v_val_3975_);
v___x_3978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_3980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_3981_){
_start:
{
lean_object* v___f_3982_; 
v___f_3982_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3982_, 0, v_inst_3981_);
return v___f_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_3983_, lean_object* v_inst_3984_){
_start:
{
lean_object* v___f_3985_; 
v___f_3985_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3985_, 0, v_inst_3984_);
return v___f_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_3986_, lean_object* v_inst_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v_fst_3989_; lean_object* v_snd_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4004_; 
v_fst_3989_ = lean_ctor_get(v_x_3988_, 0);
v_snd_3990_ = lean_ctor_get(v_x_3988_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_x_3988_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3992_ = v_x_3988_;
v_isShared_3993_ = v_isSharedCheck_4004_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_snd_3990_);
lean_inc(v_fst_3989_);
lean_dec(v_x_3988_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4004_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3994_ = lean_apply_1(v_inst_3986_, v_fst_3989_);
v___x_3995_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 7);
lean_ctor_set(v___x_3992_, 1, v___x_3995_);
lean_ctor_set(v___x_3992_, 0, v___x_3994_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3998_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_apply_1(v_inst_3987_, v_snd_3990_);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Lean_MessageData_paren(v___x_4001_);
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4005_, lean_object* v_inst_4006_){
_start:
{
lean_object* v___f_4007_; 
v___f_4007_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4007_, 0, v_inst_4005_);
lean_closure_set(v___f_4007_, 1, v_inst_4006_);
return v___f_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4008_, lean_object* v_00_u03b2_4009_, lean_object* v_inst_4010_, lean_object* v_inst_4011_){
_start:
{
lean_object* v___f_4012_; 
v___f_4012_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4012_, 0, v_inst_4010_);
lean_closure_set(v___f_4012_, 1, v_inst_4011_);
return v___f_4012_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4017_ = l_Lean_MessageData_ofFormat(v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4018_){
_start:
{
if (lean_obj_tag(v_x_4018_) == 0)
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4019_;
}
else
{
lean_object* v_val_4020_; lean_object* v___x_4021_; 
v_val_4020_ = lean_ctor_get(v_x_4018_, 0);
lean_inc(v_val_4020_);
lean_dec_ref(v_x_4018_);
v___x_4021_ = l_Lean_MessageData_ofExpr(v_val_4020_);
return v___x_4021_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_136_));
v___x_4056_ = l_String_toRawSubstring_x27(v___x_4055_);
return v___x_4056_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4072_ = l_String_toRawSubstring_x27(v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4089_; uint8_t v___x_4090_; 
v___x_4089_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4086_);
v___x_4090_ = l_Lean_Syntax_isOfKind(v_x_4086_, v___x_4089_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_dec_ref(v_a_4087_);
lean_dec(v_x_4086_);
v___x_4091_ = lean_box(1);
v___x_4092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
lean_ctor_set(v___x_4092_, 1, v_a_4088_);
return v___x_4092_;
}
else
{
lean_object* v_quotContext_4093_; lean_object* v_currMacroScope_4094_; lean_object* v_ref_4095_; lean_object* v___x_4096_; lean_object* v_interpStr_4097_; uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v_quotContext_4093_ = lean_ctor_get(v_a_4087_, 1);
v_currMacroScope_4094_ = lean_ctor_get(v_a_4087_, 2);
v_ref_4095_ = lean_ctor_get(v_a_4087_, 5);
v___x_4096_ = lean_unsigned_to_nat(1u);
v_interpStr_4097_ = l_Lean_Syntax_getArg(v_x_4086_, v___x_4096_);
lean_dec(v_x_4086_);
v___x_4098_ = 0;
v___x_4099_ = l_Lean_SourceInfo_fromRef(v_ref_4095_, v___x_4098_);
v___x_4100_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4101_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc(v_currMacroScope_4094_);
lean_inc(v_quotContext_4093_);
v___x_4102_ = l_Lean_addMacroScope(v_quotContext_4093_, v___x_4101_, v_currMacroScope_4094_);
v___x_4103_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4099_);
v___x_4104_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4099_);
lean_ctor_set(v___x_4104_, 1, v___x_4100_);
lean_ctor_set(v___x_4104_, 2, v___x_4102_);
lean_ctor_set(v___x_4104_, 3, v___x_4103_);
v___x_4105_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4106_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
lean_inc(v_currMacroScope_4094_);
lean_inc(v_quotContext_4093_);
v___x_4107_ = l_Lean_addMacroScope(v_quotContext_4093_, v___x_4106_, v_currMacroScope_4094_);
v___x_4108_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4099_);
lean_ctor_set(v___x_4109_, 1, v___x_4105_);
lean_ctor_set(v___x_4109_, 2, v___x_4107_);
lean_ctor_set(v___x_4109_, 3, v___x_4108_);
lean_inc_ref(v___x_4109_);
v___x_4110_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4097_, v___x_4104_, v___x_4109_, v___x_4109_, v_a_4087_, v_a_4088_);
lean_dec(v_interpStr_4097_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_a_4112_ = lean_ctor_get(v___x_4110_, 1);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4110_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4111_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
v_a_4120_ = lean_ctor_get(v___x_4110_, 0);
v_a_4121_ = lean_ctor_get(v___x_4110_, 1);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4110_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_inc(v_a_4120_);
lean_dec(v___x_4110_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4120_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4131_ = l_Lean_stringToMessageData(v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4132_){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4133_ = lean_array_to_list(v_msgs_4132_);
v___x_4134_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4135_ = l_Lean_MessageData_joinSep(v___x_4133_, v___x_4134_);
v___x_4136_ = l_Lean_indentD(v___x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4137_, lean_object* v_lctx_4138_, lean_object* v_opts_4139_, lean_object* v_msg_4140_){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4141_ = lean_elab_environment_of_kernel_env(v_env_4137_);
v___x_4142_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
lean_ctor_set(v___x_4143_, 2, v_lctx_4138_);
lean_ctor_set(v___x_4143_, 3, v_opts_4139_);
v___x_4144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
lean_ctor_set(v___x_4144_, 1, v_msg_4140_);
return v___x_4144_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4147_ = l_Lean_stringToMessageData(v___x_4146_);
return v___x_4147_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4150_ = l_Lean_stringToMessageData(v___x_4149_);
return v___x_4150_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4153_ = l_Lean_stringToMessageData(v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4154_, lean_object* v_n_4155_, lean_object* v_expectedType_4156_){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4157_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4158_ = l_Lean_MessageData_ofName(v_n_4155_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_indentExpr(v_givenType_4154_);
v___x_4163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4161_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Lean_indentExpr(v_expectedType_4156_);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
return v___x_4167_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4168_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4171_ = lean_box(1);
v___x_4172_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4173_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v___x_4172_);
lean_ctor_set(v___x_4174_, 2, v___x_4171_);
return v___x_4174_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4177_ = l_Lean_stringToMessageData(v___x_4176_);
return v___x_4177_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4180_ = l_Lean_stringToMessageData(v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4183_ = l_Lean_stringToMessageData(v___x_4182_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4188_ = l_Lean_MessageData_ofFormat(v___x_4187_);
return v___x_4188_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4194_ = l_Lean_stringToMessageData(v___x_4193_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4197_ = l_Lean_stringToMessageData(v___x_4196_);
return v___x_4197_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4200_ = l_Lean_stringToMessageData(v___x_4199_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4206_ = l_Lean_stringToMessageData(v___x_4205_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4209_ = l_Lean_stringToMessageData(v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4212_ = l_Lean_stringToMessageData(v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4215_ = l_Lean_stringToMessageData(v___x_4214_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4218_ = l_Lean_stringToMessageData(v___x_4217_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4221_ = l_Lean_stringToMessageData(v___x_4220_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4224_ = l_Lean_stringToMessageData(v___x_4223_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4235_ = l_Lean_MessageData_ofFormat(v___x_4234_);
return v___x_4235_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4240_ = l_Lean_MessageData_ofFormat(v___x_4239_);
return v___x_4240_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4245_ = l_Lean_MessageData_ofFormat(v___x_4244_);
return v___x_4245_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4251_, lean_object* v_opts_4252_){
_start:
{
switch(lean_obj_tag(v_e_4251_))
{
case 0:
{
lean_object* v_env_4253_; lean_object* v_name_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4267_; 
v_env_4253_ = lean_ctor_get(v_e_4251_, 0);
v_name_4254_ = lean_ctor_get(v_e_4251_, 1);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_e_4251_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4256_ = v_e_4251_;
v_isShared_4257_ = v_isSharedCheck_4267_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_name_4254_);
lean_inc(v_env_4253_);
lean_dec(v_e_4251_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4267_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4258_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4259_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4260_ = l_Lean_MessageData_ofName(v_name_4254_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set_tag(v___x_4256_, 7);
lean_ctor_set(v___x_4256_, 1, v___x_4260_);
lean_ctor_set(v___x_4256_, 0, v___x_4259_);
v___x_4262_ = v___x_4256_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4253_, v___x_4258_, v_opts_4252_, v___x_4264_);
return v___x_4265_;
}
}
}
case 1:
{
lean_object* v_env_4268_; lean_object* v_name_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4283_; 
v_env_4268_ = lean_ctor_get(v_e_4251_, 0);
v_name_4269_ = lean_ctor_get(v_e_4251_, 1);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_e_4251_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4271_ = v_e_4251_;
v_isShared_4272_ = v_isSharedCheck_4283_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_name_4269_);
lean_inc(v_env_4268_);
lean_dec(v_e_4251_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4283_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4273_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4274_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4275_ = 1;
v___x_4276_ = l_Lean_MessageData_ofConstName(v_name_4269_, v___x_4275_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set_tag(v___x_4271_, 7);
lean_ctor_set(v___x_4271_, 1, v___x_4276_);
lean_ctor_set(v___x_4271_, 0, v___x_4274_);
v___x_4278_ = v___x_4271_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4268_, v___x_4273_, v_opts_4252_, v___x_4280_);
return v___x_4281_;
}
}
}
case 2:
{
lean_object* v_env_4284_; lean_object* v_decl_4285_; lean_object* v_givenType_4286_; lean_object* v___x_4287_; 
v_env_4284_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4284_);
v_decl_4285_ = lean_ctor_get(v_e_4251_, 1);
lean_inc(v_decl_4285_);
v_givenType_4286_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_givenType_4286_);
lean_dec_ref(v_e_4251_);
v___x_4287_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4285_))
{
case 1:
{
lean_object* v_val_4288_; lean_object* v_toConstantVal_4289_; lean_object* v_name_4290_; lean_object* v_type_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v_val_4288_ = lean_ctor_get(v_decl_4285_, 0);
lean_inc_ref(v_val_4288_);
lean_dec_ref(v_decl_4285_);
v_toConstantVal_4289_ = lean_ctor_get(v_val_4288_, 0);
lean_inc_ref(v_toConstantVal_4289_);
lean_dec_ref(v_val_4288_);
v_name_4290_ = lean_ctor_get(v_toConstantVal_4289_, 0);
lean_inc(v_name_4290_);
v_type_4291_ = lean_ctor_get(v_toConstantVal_4289_, 2);
lean_inc_ref(v_type_4291_);
lean_dec_ref(v_toConstantVal_4289_);
v___x_4292_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4286_, v_name_4290_, v_type_4291_);
v___x_4293_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4284_, v___x_4287_, v_opts_4252_, v___x_4292_);
return v___x_4293_;
}
case 2:
{
lean_object* v_val_4294_; lean_object* v_toConstantVal_4295_; lean_object* v_name_4296_; lean_object* v_type_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_val_4294_ = lean_ctor_get(v_decl_4285_, 0);
lean_inc_ref(v_val_4294_);
lean_dec_ref(v_decl_4285_);
v_toConstantVal_4295_ = lean_ctor_get(v_val_4294_, 0);
lean_inc_ref(v_toConstantVal_4295_);
lean_dec_ref(v_val_4294_);
v_name_4296_ = lean_ctor_get(v_toConstantVal_4295_, 0);
lean_inc(v_name_4296_);
v_type_4297_ = lean_ctor_get(v_toConstantVal_4295_, 2);
lean_inc_ref(v_type_4297_);
lean_dec_ref(v_toConstantVal_4295_);
v___x_4298_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4286_, v_name_4296_, v_type_4297_);
v___x_4299_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4284_, v___x_4287_, v_opts_4252_, v___x_4298_);
return v___x_4299_;
}
default: 
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
lean_dec_ref(v_givenType_4286_);
lean_dec(v_decl_4285_);
v___x_4300_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4301_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4284_, v___x_4287_, v_opts_4252_, v___x_4300_);
return v___x_4301_;
}
}
}
case 3:
{
lean_object* v_env_4302_; lean_object* v_name_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_env_4302_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4302_);
v_name_4303_ = lean_ctor_get(v_e_4251_, 1);
lean_inc(v_name_4303_);
lean_dec_ref(v_e_4251_);
v___x_4304_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4305_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4306_ = 1;
v___x_4307_ = l_Lean_MessageData_ofConstName(v_name_4303_, v___x_4306_);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4305_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4308_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4302_, v___x_4304_, v_opts_4252_, v___x_4310_);
return v___x_4311_;
}
case 4:
{
lean_object* v_env_4312_; lean_object* v_name_4313_; lean_object* v_expr_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_env_4312_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4312_);
v_name_4313_ = lean_ctor_get(v_e_4251_, 1);
lean_inc(v_name_4313_);
v_expr_4314_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_expr_4314_);
lean_dec_ref(v_e_4251_);
v___x_4315_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4316_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4317_ = 1;
v___x_4318_ = l_Lean_MessageData_ofConstName(v_name_4313_, v___x_4317_);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4316_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = l_Lean_indentExpr(v_expr_4314_);
v___x_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4321_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4312_, v___x_4315_, v_opts_4252_, v___x_4323_);
return v___x_4324_;
}
case 5:
{
lean_object* v_env_4325_; lean_object* v_lctx_4326_; lean_object* v_expr_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v_env_4325_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4325_);
v_lctx_4326_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4326_);
v_expr_4327_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_expr_4327_);
lean_dec_ref(v_e_4251_);
v___x_4328_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4329_ = l_Lean_indentExpr(v_expr_4327_);
v___x_4330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4328_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4325_, v_lctx_4326_, v_opts_4252_, v___x_4330_);
return v___x_4331_;
}
case 6:
{
lean_object* v_env_4332_; lean_object* v_lctx_4333_; lean_object* v_expr_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_env_4332_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4332_);
v_lctx_4333_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4333_);
v_expr_4334_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_expr_4334_);
lean_dec_ref(v_e_4251_);
v___x_4335_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4336_ = l_Lean_indentExpr(v_expr_4334_);
v___x_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4332_, v_lctx_4333_, v_opts_4252_, v___x_4337_);
return v___x_4338_;
}
case 7:
{
lean_object* v_env_4339_; lean_object* v_lctx_4340_; lean_object* v_name_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_env_4339_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4339_);
v_lctx_4340_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4340_);
v_name_4341_ = lean_ctor_get(v_e_4251_, 2);
lean_inc(v_name_4341_);
lean_dec_ref(v_e_4251_);
v___x_4342_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4343_ = l_Lean_MessageData_ofName(v_name_4341_);
v___x_4344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v___x_4347_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4339_, v_lctx_4340_, v_opts_4252_, v___x_4346_);
return v___x_4347_;
}
case 8:
{
lean_object* v_env_4348_; lean_object* v_lctx_4349_; lean_object* v_expr_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v_env_4348_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4348_);
v_lctx_4349_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4349_);
v_expr_4350_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_expr_4350_);
lean_dec_ref(v_e_4251_);
v___x_4351_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4352_ = l_Lean_indentExpr(v_expr_4350_);
v___x_4353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
v___x_4354_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4348_, v_lctx_4349_, v_opts_4252_, v___x_4353_);
return v___x_4354_;
}
case 9:
{
lean_object* v_env_4355_; lean_object* v_lctx_4356_; lean_object* v_app_4357_; lean_object* v_funType_4358_; lean_object* v_argType_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_env_4355_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4355_);
v_lctx_4356_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4356_);
v_app_4357_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_app_4357_);
v_funType_4358_ = lean_ctor_get(v_e_4251_, 3);
lean_inc_ref(v_funType_4358_);
v_argType_4359_ = lean_ctor_get(v_e_4251_, 4);
lean_inc_ref(v_argType_4359_);
lean_dec_ref(v_e_4251_);
v___x_4360_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4361_ = l_Lean_indentExpr(v_app_4357_);
v___x_4362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v___x_4363_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = l_Lean_indentExpr(v_argType_4359_);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_indentExpr(v_funType_4358_);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4355_, v_lctx_4356_, v_opts_4252_, v___x_4370_);
return v___x_4371_;
}
case 10:
{
lean_object* v_env_4372_; lean_object* v_lctx_4373_; lean_object* v_proj_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_env_4372_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4372_);
v_lctx_4373_ = lean_ctor_get(v_e_4251_, 1);
lean_inc_ref(v_lctx_4373_);
v_proj_4374_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_proj_4374_);
lean_dec_ref(v_e_4251_);
v___x_4375_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4376_ = l_Lean_indentExpr(v_proj_4374_);
v___x_4377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4375_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
v___x_4378_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4372_, v_lctx_4373_, v_opts_4252_, v___x_4377_);
return v___x_4378_;
}
case 11:
{
lean_object* v_env_4379_; lean_object* v_name_4380_; lean_object* v_type_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_env_4379_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_env_4379_);
v_name_4380_ = lean_ctor_get(v_e_4251_, 1);
lean_inc(v_name_4380_);
v_type_4381_ = lean_ctor_get(v_e_4251_, 2);
lean_inc_ref(v_type_4381_);
lean_dec_ref(v_e_4251_);
v___x_4382_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4383_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4384_ = 1;
v___x_4385_ = l_Lean_MessageData_ofConstName(v_name_4380_, v___x_4384_);
v___x_4386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4383_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
v___x_4387_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_indentExpr(v_type_4381_);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4379_, v___x_4382_, v_opts_4252_, v___x_4390_);
return v___x_4391_;
}
case 12:
{
lean_object* v_msg_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec_ref(v_opts_4252_);
v_msg_4392_ = lean_ctor_get(v_e_4251_, 0);
lean_inc_ref(v_msg_4392_);
lean_dec_ref(v_e_4251_);
v___x_4393_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4394_ = l_Lean_stringToMessageData(v_msg_4392_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
return v___x_4395_;
}
case 13:
{
lean_object* v___x_4396_; 
lean_dec_ref(v_opts_4252_);
v___x_4396_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4396_;
}
case 14:
{
lean_object* v___x_4397_; 
lean_dec_ref(v_opts_4252_);
v___x_4397_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4397_;
}
case 15:
{
lean_object* v___x_4398_; 
lean_dec_ref(v_opts_4252_);
v___x_4398_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4398_;
}
default: 
{
lean_object* v___x_4399_; 
lean_dec_ref(v_opts_4252_);
v___x_4399_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4400_, lean_object* v_e_4401_, lean_object* v_cls_4402_){
_start:
{
lean_object* v___x_4403_; double v___x_4404_; uint8_t v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4403_ = lean_box(0);
v___x_4404_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4405_ = 1;
v___x_4406_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4407_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4407_, 0, v_cls_4402_);
lean_ctor_set(v___x_4407_, 1, v___x_4403_);
lean_ctor_set(v___x_4407_, 2, v___x_4406_);
lean_ctor_set_float(v___x_4407_, sizeof(void*)*3, v___x_4404_);
lean_ctor_set_float(v___x_4407_, sizeof(void*)*3 + 8, v___x_4404_);
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*3 + 16, v___x_4405_);
v___x_4408_ = lean_apply_1(v_inst_4400_, v_e_4401_);
v___x_4409_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4410_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4407_);
lean_ctor_set(v___x_4410_, 1, v___x_4408_);
lean_ctor_set(v___x_4410_, 2, v___x_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4411_, lean_object* v_inst_4412_, lean_object* v_e_4413_, lean_object* v_cls_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Lean_toTraceElem___redArg(v_inst_4412_, v_e_4413_, v_cls_4414_);
return v___x_4415_;
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
