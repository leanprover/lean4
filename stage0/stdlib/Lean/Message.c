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
lean_object* lean_simp_macro_scopes(lean_object*);
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
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value;
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
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
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
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_138__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_367_){
_start:
{
switch(v_x_367_)
{
case 0:
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_368_;
}
case 1:
{
lean_object* v___x_369_; 
v___x_369_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_369_;
}
default: 
{
lean_object* v___x_370_; 
v___x_370_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_371_){
_start:
{
uint8_t v_x_31__boxed_372_; lean_object* v_res_373_; 
v_x_31__boxed_372_ = lean_unbox(v_x_371_);
v_res_373_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx(lean_object* v_x_374_){
_start:
{
switch(lean_obj_tag(v_x_374_))
{
case 0:
{
lean_object* v___x_375_; 
v___x_375_ = lean_unsigned_to_nat(0u);
return v___x_375_;
}
case 1:
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(1u);
return v___x_376_;
}
case 2:
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(2u);
return v___x_377_;
}
case 3:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(3u);
return v___x_378_;
}
case 4:
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(4u);
return v___x_379_;
}
case 5:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(5u);
return v___x_380_;
}
case 6:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(6u);
return v___x_381_;
}
case 7:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(7u);
return v___x_382_;
}
case 8:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(8u);
return v___x_383_;
}
case 9:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(9u);
return v___x_384_;
}
case 10:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(10u);
return v___x_385_;
}
default: 
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(11u);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_MessageData_ctorIdx(v_x_387_);
lean_dec_ref(v_x_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_389_, lean_object* v_k_390_){
_start:
{
switch(lean_obj_tag(v_t_389_))
{
case 0:
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v_t_389_, 0);
lean_inc_ref(v_a_391_);
lean_dec_ref_known(v_t_389_, 1);
v___x_392_ = lean_apply_1(v_k_390_, v_a_391_);
return v___x_392_;
}
case 1:
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_t_389_, 1);
v___x_394_ = lean_apply_1(v_k_390_, v_a_393_);
return v___x_394_;
}
case 5:
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_395_);
v_a_396_ = lean_ctor_get(v_t_389_, 1);
lean_inc_ref(v_a_396_);
lean_dec_ref_known(v_t_389_, 2);
v___x_397_ = lean_apply_2(v_k_390_, v_a_395_, v_a_396_);
return v___x_397_;
}
case 6:
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v_t_389_, 0);
lean_inc_ref(v_a_398_);
lean_dec_ref_known(v_t_389_, 1);
v___x_399_ = lean_apply_1(v_k_390_, v_a_398_);
return v___x_399_;
}
case 8:
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_400_);
v_a_401_ = lean_ctor_get(v_t_389_, 1);
lean_inc_ref(v_a_401_);
lean_dec_ref_known(v_t_389_, 2);
v___x_402_ = lean_apply_2(v_k_390_, v_a_400_, v_a_401_);
return v___x_402_;
}
case 9:
{
lean_object* v_data_403_; lean_object* v_msg_404_; lean_object* v_children_405_; lean_object* v___x_406_; 
v_data_403_ = lean_ctor_get(v_t_389_, 0);
lean_inc_ref(v_data_403_);
v_msg_404_ = lean_ctor_get(v_t_389_, 1);
lean_inc_ref(v_msg_404_);
v_children_405_ = lean_ctor_get(v_t_389_, 2);
lean_inc_ref(v_children_405_);
lean_dec_ref_known(v_t_389_, 3);
v___x_406_ = lean_apply_3(v_k_390_, v_data_403_, v_msg_404_, v_children_405_);
return v___x_406_;
}
case 11:
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_407_ = lean_ctor_get(v_t_389_, 0);
lean_inc(v_a_407_);
v_a_408_ = lean_ctor_get(v_t_389_, 1);
lean_inc_ref(v_a_408_);
lean_dec_ref_known(v_t_389_, 2);
v___x_409_ = lean_apply_2(v_k_390_, v_a_407_, v_a_408_);
return v___x_409_;
}
default: 
{
lean_object* v_a_410_; lean_object* v_a_411_; lean_object* v___x_412_; 
v_a_410_ = lean_ctor_get(v_t_389_, 0);
lean_inc_ref(v_a_410_);
v_a_411_ = lean_ctor_get(v_t_389_, 1);
lean_inc_ref(v_a_411_);
lean_dec_ref(v_t_389_);
v___x_412_ = lean_apply_2(v_k_390_, v_a_410_, v_a_411_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_413_, lean_object* v_ctorIdx_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_k_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MessageData_ctorElim___redArg(v_t_415_, v_k_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_419_, lean_object* v_ctorIdx_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_k_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_MessageData_ctorElim(v_motive__1_419_, v_ctorIdx_420_, v_t_421_, v_h_422_, v_k_423_);
lean_dec(v_ctorIdx_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_425_, lean_object* v_ofFormatWithInfos_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_MessageData_ctorElim___redArg(v_t_425_, v_ofFormatWithInfos_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_ofFormatWithInfos_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_MessageData_ctorElim___redArg(v_t_429_, v_ofFormatWithInfos_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_433_, lean_object* v_ofGoal_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_MessageData_ctorElim___redArg(v_t_433_, v_ofGoal_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_ofGoal_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_MessageData_ctorElim___redArg(v_t_437_, v_ofGoal_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_441_, lean_object* v_ofWidget_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_MessageData_ctorElim___redArg(v_t_441_, v_ofWidget_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_ofWidget_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_MessageData_ctorElim___redArg(v_t_445_, v_ofWidget_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_449_, lean_object* v_withContext_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_MessageData_ctorElim___redArg(v_t_449_, v_withContext_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_withContext_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_MessageData_ctorElim___redArg(v_t_453_, v_withContext_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_457_, lean_object* v_withNamingContext_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_MessageData_ctorElim___redArg(v_t_457_, v_withNamingContext_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_460_, lean_object* v_t_461_, lean_object* v_h_462_, lean_object* v_withNamingContext_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_MessageData_ctorElim___redArg(v_t_461_, v_withNamingContext_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_465_, lean_object* v_nest_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_MessageData_ctorElim___redArg(v_t_465_, v_nest_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_nest_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_MessageData_ctorElim___redArg(v_t_469_, v_nest_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_473_, lean_object* v_group_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_MessageData_ctorElim___redArg(v_t_473_, v_group_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_476_, lean_object* v_t_477_, lean_object* v_h_478_, lean_object* v_group_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_MessageData_ctorElim___redArg(v_t_477_, v_group_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_481_, lean_object* v_compose_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_MessageData_ctorElim___redArg(v_t_481_, v_compose_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_compose_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_MessageData_ctorElim___redArg(v_t_485_, v_compose_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_489_, lean_object* v_tagged_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_MessageData_ctorElim___redArg(v_t_489_, v_tagged_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_tagged_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_MessageData_ctorElim___redArg(v_t_493_, v_tagged_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_497_, lean_object* v_trace_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_MessageData_ctorElim___redArg(v_t_497_, v_trace_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_trace_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MessageData_ctorElim___redArg(v_t_501_, v_trace_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_505_, lean_object* v_ofLazy_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_MessageData_ctorElim___redArg(v_t_505_, v_ofLazy_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_ofLazy_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_MessageData_ctorElim___redArg(v_t_509_, v_ofLazy_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_513_, lean_object* v_ofOriginatingSyntax_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_MessageData_ctorElim___redArg(v_t_513_, v_ofOriginatingSyntax_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_ofOriginatingSyntax_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_MessageData_ctorElim___redArg(v_t_517_, v_ofOriginatingSyntax_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_box(1);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_fmt_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_536_, lean_object* v_onMissingContext_537_, lean_object* v_f_538_, lean_object* v_ctx_x3f_539_){
_start:
{
lean_object* v_msg_542_; 
if (lean_obj_tag(v_ctx_x3f_539_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_f_538_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_2(v_onMissingContext_537_, v___x_544_, lean_box(0));
v_msg_542_ = v___x_545_;
goto v___jp_541_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; 
lean_dec_ref(v_onMissingContext_537_);
v_val_546_ = lean_ctor_get(v_ctx_x3f_539_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v_ctx_x3f_539_, 1);
v___x_547_ = lean_apply_2(v_f_538_, v_val_546_, lean_box(0));
v_msg_542_ = v___x_547_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_536_);
lean_ctor_set(v___x_543_, 1, v_msg_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_548_, lean_object* v_onMissingContext_549_, lean_object* v_f_550_, lean_object* v_ctx_x3f_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_MessageData_lazy___lam__0(v___x_548_, v_onMissingContext_549_, v_f_550_, v_ctx_x3f_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_554_, lean_object* v_hasSyntheticSorry_555_, lean_object* v_onMissingContext_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v___x_557_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___f_558_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_558_, 0, v___x_557_);
lean_closure_set(v___f_558_, 1, v_onMissingContext_556_);
lean_closure_set(v___f_558_, 2, v_f_554_);
v___x_559_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_559_, 0, v___f_558_);
lean_ctor_set(v___x_559_, 1, v_hasSyntheticSorry_555_);
return v___x_559_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_560_, lean_object* v_x_561_){
_start:
{
switch(lean_obj_tag(v_x_561_))
{
case 3:
{
lean_object* v_a_562_; 
v_a_562_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_562_);
lean_dec_ref_known(v_x_561_, 2);
v_x_561_ = v_a_562_;
goto _start;
}
case 4:
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_564_);
lean_dec_ref_known(v_x_561_, 2);
v_x_561_ = v_a_564_;
goto _start;
}
case 5:
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_566_);
lean_dec_ref_known(v_x_561_, 2);
v_x_561_ = v_a_566_;
goto _start;
}
case 6:
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v_x_561_, 0);
lean_inc_ref(v_a_568_);
lean_dec_ref_known(v_x_561_, 1);
v_x_561_ = v_a_568_;
goto _start;
}
case 7:
{
lean_object* v_a_570_; lean_object* v_a_571_; uint8_t v___x_572_; 
v_a_570_ = lean_ctor_get(v_x_561_, 0);
lean_inc_ref(v_a_570_);
v_a_571_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_571_);
lean_dec_ref_known(v_x_561_, 2);
lean_inc_ref(v_p_560_);
v___x_572_ = l_Lean_MessageData_hasTag(v_p_560_, v_a_570_);
if (v___x_572_ == 0)
{
v_x_561_ = v_a_571_;
goto _start;
}
else
{
lean_dec_ref(v_a_571_);
lean_dec_ref(v_p_560_);
return v___x_572_;
}
}
case 8:
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_a_574_);
v_a_575_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_575_);
lean_dec_ref_known(v_x_561_, 2);
lean_inc_ref(v_p_560_);
v___x_576_ = lean_apply_1(v_p_560_, v_a_574_);
v___x_577_ = lean_unbox(v___x_576_);
if (v___x_577_ == 0)
{
v_x_561_ = v_a_575_;
goto _start;
}
else
{
uint8_t v___x_579_; 
lean_dec_ref(v_a_575_);
lean_dec_ref(v_p_560_);
v___x_579_ = lean_unbox(v___x_576_);
return v___x_579_;
}
}
case 9:
{
lean_object* v_data_580_; lean_object* v_msg_581_; lean_object* v_children_582_; lean_object* v_cls_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_data_580_ = lean_ctor_get(v_x_561_, 0);
lean_inc_ref(v_data_580_);
v_msg_581_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_msg_581_);
v_children_582_ = lean_ctor_get(v_x_561_, 2);
lean_inc_ref(v_children_582_);
lean_dec_ref_known(v_x_561_, 3);
v_cls_583_ = lean_ctor_get(v_data_580_, 0);
lean_inc(v_cls_583_);
lean_dec_ref(v_data_580_);
lean_inc_ref(v_p_560_);
v___x_584_ = lean_apply_1(v_p_560_, v_cls_583_);
v___x_585_ = lean_unbox(v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
lean_inc_ref(v_p_560_);
v___x_586_ = l_Lean_MessageData_hasTag(v_p_560_, v_msg_581_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_children_582_);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec_ref(v_children_582_);
lean_dec_ref(v_p_560_);
return v___x_586_;
}
else
{
if (v___x_589_ == 0)
{
lean_dec_ref(v_children_582_);
lean_dec_ref(v_p_560_);
return v___x_586_;
}
else
{
size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = ((size_t)0ULL);
v___x_591_ = lean_usize_of_nat(v___x_588_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_560_, v_children_582_, v___x_590_, v___x_591_);
lean_dec_ref(v_children_582_);
return v___x_592_;
}
}
}
else
{
lean_dec_ref(v_children_582_);
lean_dec_ref(v_p_560_);
return v___x_586_;
}
}
else
{
uint8_t v___x_593_; 
lean_dec_ref(v_children_582_);
lean_dec_ref(v_msg_581_);
lean_dec_ref(v_p_560_);
v___x_593_ = lean_unbox(v___x_584_);
return v___x_593_;
}
}
case 11:
{
lean_object* v_a_594_; 
v_a_594_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_a_594_);
lean_dec_ref_known(v_x_561_, 2);
v_x_561_ = v_a_594_;
goto _start;
}
default: 
{
uint8_t v___x_596_; 
lean_dec_ref(v_x_561_);
lean_dec_ref(v_p_560_);
v___x_596_ = 0;
return v___x_596_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_597_, lean_object* v_as_598_, size_t v_i_599_, size_t v_stop_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_eq(v_i_599_, v_stop_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_uget_borrowed(v_as_598_, v_i_599_);
lean_inc(v___x_602_);
lean_inc_ref(v_p_597_);
v___x_603_ = l_Lean_MessageData_hasTag(v_p_597_, v___x_602_);
if (v___x_603_ == 0)
{
size_t v___x_604_; size_t v___x_605_; 
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_599_, v___x_604_);
v_i_599_ = v___x_605_;
goto _start;
}
else
{
lean_dec_ref(v_p_597_);
return v___x_603_;
}
}
else
{
uint8_t v___x_607_; 
lean_dec_ref(v_p_597_);
v___x_607_ = 0;
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_608_, lean_object* v_as_609_, lean_object* v_i_610_, lean_object* v_stop_611_){
_start:
{
size_t v_i_boxed_612_; size_t v_stop_boxed_613_; uint8_t v_res_614_; lean_object* v_r_615_; 
v_i_boxed_612_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_stop_boxed_613_ = lean_unbox_usize(v_stop_611_);
lean_dec(v_stop_611_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_608_, v_as_609_, v_i_boxed_612_, v_stop_boxed_613_);
lean_dec_ref(v_as_609_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_616_, lean_object* v_x_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_MessageData_hasTag(v_p_616_, v_x_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_620_){
_start:
{
switch(lean_obj_tag(v_x_620_))
{
case 3:
{
lean_object* v_a_621_; 
v_a_621_ = lean_ctor_get(v_x_620_, 1);
v_x_620_ = v_a_621_;
goto _start;
}
case 4:
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v_x_620_, 1);
v_x_620_ = v_a_623_;
goto _start;
}
case 8:
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v_x_620_, 0);
lean_inc(v_a_625_);
return v_a_625_;
}
case 9:
{
lean_object* v_data_626_; lean_object* v_cls_627_; 
v_data_626_ = lean_ctor_get(v_x_620_, 0);
v_cls_627_ = lean_ctor_get(v_data_626_, 0);
lean_inc(v_cls_627_);
return v_cls_627_;
}
case 11:
{
lean_object* v_a_628_; 
v_a_628_ = lean_ctor_get(v_x_620_, 1);
v_x_620_ = v_a_628_;
goto _start;
}
default: 
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_MessageData_kind(v_x_631_);
lean_dec_ref(v_x_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 11)
{
lean_object* v_a_634_; lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_a_634_ = lean_ctor_get(v_x_633_, 0);
v_a_635_ = lean_ctor_get(v_x_633_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v_x_633_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_inc(v_a_634_);
lean_dec(v_x_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v_a_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_a_635_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_x_633_);
return v___x_645_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_646_){
_start:
{
switch(lean_obj_tag(v_x_646_))
{
case 3:
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v_x_646_, 1);
v_x_646_ = v_a_647_;
goto _start;
}
case 4:
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v_x_646_, 1);
v_x_646_ = v_a_649_;
goto _start;
}
case 8:
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v_x_646_, 1);
v_x_646_ = v_a_651_;
goto _start;
}
case 9:
{
uint8_t v___x_653_; 
v___x_653_ = 1;
return v___x_653_;
}
case 11:
{
lean_object* v_a_654_; 
v_a_654_ = lean_ctor_get(v_x_646_, 1);
v_x_646_ = v_a_654_;
goto _start;
}
default: 
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_MessageData_isTrace(v_x_657_);
lean_dec_ref(v_x_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
switch(lean_obj_tag(v_x_660_))
{
case 3:
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_a_662_ = lean_ctor_get(v_x_660_, 0);
v_a_663_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v_x_660_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_inc(v_a_662_);
lean_dec(v_x_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_MessageData_composePreservingKind(v_a_663_, v_x_661_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(3, 2, 0);
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
case 4:
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_a_672_ = lean_ctor_get(v_x_660_, 0);
v_a_673_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v_x_660_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_inc(v_a_672_);
lean_dec(v_x_660_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_MessageData_composePreservingKind(v_a_673_, v_x_661_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_672_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
case 8:
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
v_a_682_ = lean_ctor_get(v_x_660_, 0);
v_a_683_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_691_ == 0)
{
v___x_685_ = v_x_660_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_inc(v_a_682_);
lean_dec(v_x_660_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 7);
lean_ctor_set(v___x_685_, 1, v_x_661_);
lean_ctor_set(v___x_685_, 0, v_a_683_);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_x_661_);
v___x_688_ = v_reuseFailAlloc_690_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_689_, 0, v_a_682_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
return v___x_689_;
}
}
}
case 11:
{
lean_object* v_a_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_a_692_ = lean_ctor_get(v_x_660_, 0);
v_a_693_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_x_660_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_inc(v_a_692_);
lean_dec(v_x_660_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_MessageData_composePreservingKind(v_a_693_, v_x_661_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v_x_660_);
lean_ctor_set(v___x_702_, 1, v_x_661_);
return v___x_702_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_box(0);
v___x_704_ = l_Lean_MessageData_ofFormat(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_706_, lean_object* v_ctx_707_){
_start:
{
lean_object* v_env_708_; lean_object* v_mctx_709_; lean_object* v_lctx_710_; lean_object* v_opts_711_; lean_object* v_currNamespace_712_; lean_object* v_openDecls_713_; lean_object* v___x_714_; 
v_env_708_ = lean_ctor_get(v_ctx_707_, 0);
v_mctx_709_ = lean_ctor_get(v_ctx_707_, 1);
v_lctx_710_ = lean_ctor_get(v_ctx_707_, 2);
v_opts_711_ = lean_ctor_get(v_ctx_707_, 3);
v_currNamespace_712_ = lean_ctor_get(v_nCtx_706_, 0);
v_openDecls_713_ = lean_ctor_get(v_nCtx_706_, 1);
lean_inc(v_openDecls_713_);
lean_inc(v_currNamespace_712_);
lean_inc_ref(v_opts_711_);
lean_inc_ref(v_lctx_710_);
lean_inc_ref(v_mctx_709_);
lean_inc_ref(v_env_708_);
v___x_714_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_714_, 0, v_env_708_);
lean_ctor_set(v___x_714_, 1, v_mctx_709_);
lean_ctor_set(v___x_714_, 2, v_lctx_710_);
lean_ctor_set(v___x_714_, 3, v_opts_711_);
lean_ctor_set(v___x_714_, 4, v_currNamespace_712_);
lean_ctor_set(v___x_714_, 5, v_openDecls_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_715_, lean_object* v_ctx_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_MessageData_mkPPContext(v_nCtx_715_, v_ctx_716_);
lean_dec_ref(v_ctx_716_);
lean_dec_ref(v_nCtx_715_);
return v_res_717_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = 0;
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_720_);
lean_dec_ref(v_x_720_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_723_, lean_object* v_stx_724_, lean_object* v_ctx_x3f_725_){
_start:
{
lean_object* v_val_728_; 
if (lean_obj_tag(v_ctx_x3f_725_) == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = 0;
v___x_733_ = l_Lean_Syntax_formatStx(v_stx_724_, v___x_731_, v___x_732_);
v_val_728_ = v___x_733_;
goto v___jp_727_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_735_; 
v_val_734_ = lean_ctor_get(v_ctx_x3f_725_, 0);
lean_inc(v_val_734_);
lean_dec_ref_known(v_ctx_x3f_725_, 1);
v___x_735_ = l_Lean_ppTerm(v_val_734_, v_stx_724_);
v_val_728_ = v___x_735_;
goto v___jp_727_;
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = l_Lean_MessageData_ofFormat(v_val_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_723_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_736_, lean_object* v_stx_737_, lean_object* v_ctx_x3f_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_736_, v_stx_737_, v_ctx_x3f_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_stx_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v___f_743_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_744_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___x_745_ = lean_box(0);
v_stx_746_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_742_, v___x_745_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_747_, 0, v___x_744_);
lean_closure_set(v___f_747_, 1, v_stx_746_);
v___x_748_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_748_, 0, v___f_747_);
lean_ctor_set(v___x_748_, 1, v___f_743_);
return v___x_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_749_, lean_object* v_mctx_750_){
_start:
{
lean_object* v___x_751_; lean_object* v_fst_752_; uint8_t v___x_753_; 
v___x_751_ = l_Lean_instantiateMVarsCore(v_mctx_750_, v_e_749_);
v_fst_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_fst_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = l_Lean_Expr_hasSyntheticSorry(v_fst_752_);
lean_dec(v_fst_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_754_, lean_object* v_mctx_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lean_MessageData_ofExpr___lam__0(v_e_754_, v_mctx_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_758_, lean_object* v_e_759_, lean_object* v_ctx_x3f_760_){
_start:
{
lean_object* v_val_763_; 
if (lean_obj_tag(v_ctx_x3f_760_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_expr_dbg_to_string(v_e_759_);
lean_dec_ref(v_e_759_);
v___x_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = lean_box(1);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v_val_763_ = v___x_769_;
goto v___jp_762_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; 
v_val_770_ = lean_ctor_get(v_ctx_x3f_760_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_ctx_x3f_760_, 1);
v___x_771_ = l_Lean_ppExprWithInfos(v_val_770_, v_e_759_);
v_val_763_ = v___x_771_;
goto v___jp_762_;
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v_val_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_758_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_772_, lean_object* v_e_773_, lean_object* v_ctx_x3f_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_MessageData_ofExpr___lam__1(v___x_772_, v_e_773_, v_ctx_x3f_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_777_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
lean_inc_ref(v_e_777_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_778_, 0, v_e_777_);
v___x_779_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___f_780_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_780_, 0, v___x_779_);
lean_closure_set(v___f_780_, 1, v_e_777_);
v___x_781_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_781_, 0, v___f_780_);
lean_ctor_set(v___x_781_, 1, v___f_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_box(0);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_MessageData_ofLevel___lam__0(v_x_784_);
lean_dec(v_x_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_786_, lean_object* v_l_787_, lean_object* v___f_788_, lean_object* v_ctx_x3f_789_){
_start:
{
lean_object* v_val_792_; 
if (lean_obj_tag(v_ctx_x3f_789_) == 0)
{
uint8_t v___x_795_; lean_object* v___x_796_; 
v___x_795_ = 1;
v___x_796_ = l_Lean_Level_format(v_l_787_, v___x_795_, v___f_788_);
v_val_792_ = v___x_796_;
goto v___jp_791_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_798_; 
lean_dec_ref(v___f_788_);
v_val_797_ = lean_ctor_get(v_ctx_x3f_789_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_ctx_x3f_789_, 1);
v___x_798_ = l_Lean_ppLevel(v_val_797_, v_l_787_);
v_val_792_ = v___x_798_;
goto v___jp_791_;
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = l_Lean_MessageData_ofFormat(v_val_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_786_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_799_, lean_object* v_l_800_, lean_object* v___f_801_, lean_object* v_ctx_x3f_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_MessageData_ofLevel___lam__2(v___x_799_, v_l_800_, v___f_801_, v_ctx_x3f_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; 
v___f_807_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_808_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_809_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___f_810_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_810_, 0, v___x_809_);
lean_closure_set(v___f_810_, 1, v_l_806_);
lean_closure_set(v___f_810_, 2, v___f_807_);
v___x_811_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_811_, 0, v___f_810_);
lean_ctor_set(v___x_811_, 1, v___f_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_812_){
_start:
{
uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = 1;
v___x_814_ = l_Lean_Name_toString(v_n_812_, v___x_813_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofFormat(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_820_, lean_object* v_k_821_, uint8_t v_v_822_){
_start:
{
lean_object* v_map_823_; uint8_t v_hasTrace_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_838_; 
v_map_823_ = lean_ctor_get(v_o_820_, 0);
v_hasTrace_824_ = lean_ctor_get_uint8(v_o_820_, sizeof(void*)*1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_o_820_);
if (v_isSharedCheck_838_ == 0)
{
v___x_826_ = v_o_820_;
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_map_823_);
lean_dec(v_o_820_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_828_, 0, v_v_822_);
lean_inc(v_k_821_);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_821_, v___x_828_, v_map_823_);
if (v_hasTrace_824_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_833_; 
v___x_830_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_831_ = l_Lean_Name_isPrefixOf(v___x_830_, v_k_821_);
lean_dec(v_k_821_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_833_ = v___x_826_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_829_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v___x_831_);
return v___x_833_;
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v_k_821_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_836_ = v___x_826_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*1, v_hasTrace_824_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_839_, lean_object* v_k_840_, lean_object* v_v_841_){
_start:
{
uint8_t v_v_boxed_842_; lean_object* v_res_843_; 
v_v_boxed_842_ = lean_unbox(v_v_841_);
v_res_843_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_839_, v_k_840_, v_v_boxed_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_849_, lean_object* v_constName_850_, uint8_t v_fullNames_851_, lean_object* v_ctx_x3f_852_){
_start:
{
lean_object* v_val_855_; lean_object* v___y_859_; 
if (lean_obj_tag(v_ctx_x3f_852_) == 0)
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = 1;
v___x_861_ = l_Lean_Name_toString(v_constName_850_, v___x_860_);
v___x_862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
v___x_863_ = lean_box(1);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v_val_855_ = v___x_864_;
goto v___jp_854_;
}
else
{
if (v_fullNames_851_ == 0)
{
lean_object* v_val_865_; lean_object* v___x_866_; 
v_val_865_ = lean_ctor_get(v_ctx_x3f_852_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_ctx_x3f_852_, 1);
v___x_866_ = l_Lean_ppConstNameWithInfos(v_val_865_, v_constName_850_);
v___y_859_ = v___x_866_;
goto v___jp_858_;
}
else
{
lean_object* v_val_867_; lean_object* v_env_868_; lean_object* v_mctx_869_; lean_object* v_lctx_870_; lean_object* v_opts_871_; lean_object* v_currNamespace_872_; lean_object* v_openDecls_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_val_867_ = lean_ctor_get(v_ctx_x3f_852_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v_ctx_x3f_852_, 1);
v_env_868_ = lean_ctor_get(v_val_867_, 0);
v_mctx_869_ = lean_ctor_get(v_val_867_, 1);
v_lctx_870_ = lean_ctor_get(v_val_867_, 2);
v_opts_871_ = lean_ctor_get(v_val_867_, 3);
v_currNamespace_872_ = lean_ctor_get(v_val_867_, 4);
v_openDecls_873_ = lean_ctor_get(v_val_867_, 5);
v_isSharedCheck_883_ = !lean_is_exclusive(v_val_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_875_ = v_val_867_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_openDecls_873_);
lean_inc(v_currNamespace_872_);
lean_inc(v_opts_871_);
lean_inc(v_lctx_870_);
lean_inc(v_mctx_869_);
lean_inc(v_env_868_);
lean_dec(v_val_867_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_878_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_871_, v___x_877_, v_fullNames_851_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 3, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_env_868_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_mctx_869_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_lctx_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_currNamespace_872_);
lean_ctor_set(v_reuseFailAlloc_882_, 5, v_openDecls_873_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_ppConstNameWithInfos(v___x_880_, v_constName_850_);
v___y_859_ = v___x_881_;
goto v___jp_858_;
}
}
}
}
v___jp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_val_855_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_849_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
return v___x_857_;
}
v___jp_858_:
{
v_val_855_ = v___y_859_;
goto v___jp_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_884_, lean_object* v_constName_885_, lean_object* v_fullNames_886_, lean_object* v_ctx_x3f_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_fullNames_boxed_889_; lean_object* v_res_890_; 
v_fullNames_boxed_889_ = lean_unbox(v_fullNames_886_);
v_res_890_ = l_Lean_MessageData_ofConstName___lam__1(v___x_884_, v_constName_885_, v_fullNames_boxed_889_, v_ctx_x3f_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_891_, uint8_t v_fullNames_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; 
v___f_893_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_894_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___x_895_ = lean_box(v_fullNames_892_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_896_, 0, v___x_894_);
lean_closure_set(v___f_896_, 1, v_constName_891_);
lean_closure_set(v___f_896_, 2, v___x_895_);
v___x_897_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_897_, 0, v___f_896_);
lean_ctor_set(v___x_897_, 1, v___f_893_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_898_, lean_object* v_fullNames_899_){
_start:
{
uint8_t v_fullNames_boxed_900_; lean_object* v_res_901_; 
v_fullNames_boxed_900_ = lean_unbox(v_fullNames_899_);
v_res_901_ = l_Lean_MessageData_ofConstName(v_constName_898_, v_fullNames_boxed_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v_val_902_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_MessageData_withExprHover___lam__0(v_val_906_, v___y_907_);
lean_dec_ref(v___y_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_910_, lean_object* v_v_911_, lean_object* v_t_912_){
_start:
{
if (lean_obj_tag(v_t_912_) == 0)
{
lean_object* v_size_913_; lean_object* v_k_914_; lean_object* v_v_915_; lean_object* v_l_916_; lean_object* v_r_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_1198_; 
v_size_913_ = lean_ctor_get(v_t_912_, 0);
v_k_914_ = lean_ctor_get(v_t_912_, 1);
v_v_915_ = lean_ctor_get(v_t_912_, 2);
v_l_916_ = lean_ctor_get(v_t_912_, 3);
v_r_917_ = lean_ctor_get(v_t_912_, 4);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_t_912_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_919_ = v_t_912_;
v_isShared_920_ = v_isSharedCheck_1198_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_r_917_);
lean_inc(v_l_916_);
lean_inc(v_v_915_);
lean_inc(v_k_914_);
lean_inc(v_size_913_);
lean_dec(v_t_912_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_1198_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_lt(v_k_910_, v_k_914_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = lean_nat_dec_eq(v_k_910_, v_k_914_);
if (v___x_922_ == 0)
{
lean_object* v_impl_923_; lean_object* v___x_924_; 
lean_dec(v_size_913_);
v_impl_923_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_910_, v_v_911_, v_r_917_);
v___x_924_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_916_) == 0)
{
lean_object* v_size_925_; lean_object* v_size_926_; lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v_l_929_; lean_object* v_r_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_size_925_ = lean_ctor_get(v_l_916_, 0);
v_size_926_ = lean_ctor_get(v_impl_923_, 0);
lean_inc(v_size_926_);
v_k_927_ = lean_ctor_get(v_impl_923_, 1);
lean_inc(v_k_927_);
v_v_928_ = lean_ctor_get(v_impl_923_, 2);
lean_inc(v_v_928_);
v_l_929_ = lean_ctor_get(v_impl_923_, 3);
lean_inc(v_l_929_);
v_r_930_ = lean_ctor_get(v_impl_923_, 4);
lean_inc(v_r_930_);
v___x_931_ = lean_unsigned_to_nat(3u);
v___x_932_ = lean_nat_mul(v___x_931_, v_size_925_);
v___x_933_ = lean_nat_dec_lt(v___x_932_, v_size_926_);
lean_dec(v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_r_930_);
lean_dec(v_l_929_);
lean_dec(v_v_928_);
lean_dec(v_k_927_);
v___x_934_ = lean_nat_add(v___x_924_, v_size_925_);
v___x_935_ = lean_nat_add(v___x_934_, v_size_926_);
lean_dec(v_size_926_);
lean_dec(v___x_934_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_impl_923_);
lean_ctor_set(v___x_919_, 0, v___x_935_);
v___x_937_ = v___x_919_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_l_916_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_impl_923_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v_impl_923_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; 
v_unused_1003_ = lean_ctor_get(v_impl_923_, 4);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_impl_923_, 3);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_impl_923_, 2);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_impl_923_, 1);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_impl_923_, 0);
lean_dec(v_unused_1007_);
v___x_940_ = v_impl_923_;
v_isShared_941_ = v_isSharedCheck_1002_;
goto v_resetjp_939_;
}
else
{
lean_dec(v_impl_923_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1002_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_size_942_; lean_object* v_k_943_; lean_object* v_v_944_; lean_object* v_l_945_; lean_object* v_r_946_; lean_object* v_size_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_size_942_ = lean_ctor_get(v_l_929_, 0);
v_k_943_ = lean_ctor_get(v_l_929_, 1);
v_v_944_ = lean_ctor_get(v_l_929_, 2);
v_l_945_ = lean_ctor_get(v_l_929_, 3);
v_r_946_ = lean_ctor_get(v_l_929_, 4);
v_size_947_ = lean_ctor_get(v_r_930_, 0);
v___x_948_ = lean_unsigned_to_nat(2u);
v___x_949_ = lean_nat_mul(v___x_948_, v_size_947_);
v___x_950_ = lean_nat_dec_lt(v_size_942_, v___x_949_);
lean_dec(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_978_; 
lean_inc(v_r_946_);
lean_inc(v_l_945_);
lean_inc(v_v_944_);
lean_inc(v_k_943_);
v_isSharedCheck_978_ = !lean_is_exclusive(v_l_929_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_979_ = lean_ctor_get(v_l_929_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_929_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_929_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_929_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_929_, 0);
lean_dec(v_unused_983_);
v___x_952_ = v_l_929_;
v_isShared_953_ = v_isSharedCheck_978_;
goto v_resetjp_951_;
}
else
{
lean_dec(v_l_929_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_978_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_968_; 
v___x_954_ = lean_nat_add(v___x_924_, v_size_925_);
v___x_955_ = lean_nat_add(v___x_954_, v_size_926_);
lean_dec(v_size_926_);
if (lean_obj_tag(v_l_945_) == 0)
{
lean_object* v_size_976_; 
v_size_976_ = lean_ctor_get(v_l_945_, 0);
lean_inc(v_size_976_);
v___y_968_ = v_size_976_;
goto v___jp_967_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___y_968_ = v___x_977_;
goto v___jp_967_;
}
v___jp_956_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_nat_add(v___y_957_, v___y_959_);
lean_dec(v___y_959_);
lean_dec(v___y_957_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 4, v_r_930_);
lean_ctor_set(v___x_952_, 3, v_r_946_);
lean_ctor_set(v___x_952_, 2, v_v_928_);
lean_ctor_set(v___x_952_, 1, v_k_927_);
lean_ctor_set(v___x_952_, 0, v___x_960_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_r_946_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_r_930_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___x_962_);
lean_ctor_set(v___x_940_, 3, v___y_958_);
lean_ctor_set(v___x_940_, 2, v_v_944_);
lean_ctor_set(v___x_940_, 1, v_k_943_);
lean_ctor_set(v___x_940_, 0, v___x_955_);
v___x_964_ = v___x_940_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v___y_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_nat_add(v___x_954_, v___y_968_);
lean_dec(v___y_968_);
lean_dec(v___x_954_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_l_945_);
lean_ctor_set(v___x_919_, 0, v___x_969_);
v___x_971_ = v___x_919_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_l_916_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_l_945_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; 
v___x_972_ = lean_nat_add(v___x_924_, v_size_947_);
if (lean_obj_tag(v_r_946_) == 0)
{
lean_object* v_size_973_; 
v_size_973_ = lean_ctor_get(v_r_946_, 0);
lean_inc(v_size_973_);
v___y_957_ = v___x_972_;
v___y_958_ = v___x_971_;
v___y_959_ = v_size_973_;
goto v___jp_956_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___y_957_ = v___x_972_;
v___y_958_ = v___x_971_;
v___y_959_ = v___x_974_;
goto v___jp_956_;
}
}
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
lean_del_object(v___x_919_);
v___x_984_ = lean_nat_add(v___x_924_, v_size_925_);
v___x_985_ = lean_nat_add(v___x_984_, v_size_926_);
lean_dec(v_size_926_);
v___x_986_ = lean_nat_add(v___x_984_, v_size_942_);
lean_dec(v___x_984_);
lean_inc_ref(v_l_916_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_l_929_);
lean_ctor_set(v___x_940_, 3, v_l_916_);
lean_ctor_set(v___x_940_, 2, v_v_915_);
lean_ctor_set(v___x_940_, 1, v_k_914_);
lean_ctor_set(v___x_940_, 0, v___x_986_);
v___x_988_ = v___x_940_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_l_916_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_l_929_);
v___x_988_ = v_reuseFailAlloc_1001_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v_l_916_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_996_ = lean_ctor_get(v_l_916_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_l_916_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_l_916_, 2);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_l_916_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_l_916_, 0);
lean_dec(v_unused_1000_);
v___x_990_ = v_l_916_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_dec(v_l_916_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 4, v_r_930_);
lean_ctor_set(v___x_990_, 3, v___x_988_);
lean_ctor_set(v___x_990_, 2, v_v_928_);
lean_ctor_set(v___x_990_, 1, v_k_927_);
lean_ctor_set(v___x_990_, 0, v___x_985_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_r_930_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1008_; 
v_l_1008_ = lean_ctor_get(v_impl_923_, 3);
lean_inc(v_l_1008_);
if (lean_obj_tag(v_l_1008_) == 0)
{
lean_object* v_r_1009_; lean_object* v_k_1010_; lean_object* v_v_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1034_; 
v_r_1009_ = lean_ctor_get(v_impl_923_, 4);
v_k_1010_ = lean_ctor_get(v_impl_923_, 1);
v_v_1011_ = lean_ctor_get(v_impl_923_, 2);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_impl_923_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1035_ = lean_ctor_get(v_impl_923_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_923_, 0);
lean_dec(v_unused_1036_);
v___x_1013_ = v_impl_923_;
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_r_1009_);
lean_inc(v_v_1011_);
lean_inc(v_k_1010_);
lean_dec(v_impl_923_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_k_1015_; lean_object* v_v_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1030_; 
v_k_1015_ = lean_ctor_get(v_l_1008_, 1);
v_v_1016_ = lean_ctor_get(v_l_1008_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_l_1008_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1031_ = lean_ctor_get(v_l_1008_, 4);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_l_1008_, 3);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_l_1008_, 0);
lean_dec(v_unused_1033_);
v___x_1018_ = v_l_1008_;
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_v_1016_);
lean_inc(v_k_1015_);
lean_dec(v_l_1008_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1009_, 2);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 4, v_r_1009_);
lean_ctor_set(v___x_1018_, 3, v_r_1009_);
lean_ctor_set(v___x_1018_, 2, v_v_915_);
lean_ctor_set(v___x_1018_, 1, v_k_914_);
lean_ctor_set(v___x_1018_, 0, v___x_924_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_r_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_r_1009_);
v___x_1022_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
lean_inc(v_r_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 3, v_r_1009_);
lean_ctor_set(v___x_1013_, 0, v___x_924_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_k_1010_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_v_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_r_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_r_1009_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v___x_1024_);
lean_ctor_set(v___x_919_, 3, v___x_1022_);
lean_ctor_set(v___x_919_, 2, v_v_1016_);
lean_ctor_set(v___x_919_, 1, v_k_1015_);
lean_ctor_set(v___x_919_, 0, v___x_1020_);
v___x_1026_ = v___x_919_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_1015_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_v_1016_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
lean_object* v_r_1037_; 
v_r_1037_ = lean_ctor_get(v_impl_923_, 4);
lean_inc(v_r_1037_);
if (lean_obj_tag(v_r_1037_) == 0)
{
lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1050_; 
v_k_1038_ = lean_ctor_get(v_impl_923_, 1);
v_v_1039_ = lean_ctor_get(v_impl_923_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_impl_923_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; 
v_unused_1051_ = lean_ctor_get(v_impl_923_, 4);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_impl_923_, 3);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_impl_923_, 0);
lean_dec(v_unused_1053_);
v___x_1041_ = v_impl_923_;
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_v_1039_);
lean_inc(v_k_1038_);
lean_dec(v_impl_923_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_unsigned_to_nat(3u);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v_l_1008_);
lean_ctor_set(v___x_1041_, 2, v_v_915_);
lean_ctor_set(v___x_1041_, 1, v_k_914_);
lean_ctor_set(v___x_1041_, 0, v___x_924_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_1008_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_l_1008_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_r_1037_);
lean_ctor_set(v___x_919_, 3, v___x_1045_);
lean_ctor_set(v___x_919_, 2, v_v_1039_);
lean_ctor_set(v___x_919_, 1, v_k_1038_);
lean_ctor_set(v___x_919_, 0, v___x_1043_);
v___x_1047_ = v___x_919_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_r_1037_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = lean_unsigned_to_nat(2u);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_impl_923_);
lean_ctor_set(v___x_919_, 3, v_r_1037_);
lean_ctor_set(v___x_919_, 0, v___x_1054_);
v___x_1056_ = v___x_919_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_r_1037_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_impl_923_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_v_915_);
lean_dec(v_k_914_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 2, v_v_911_);
lean_ctor_set(v___x_919_, 1, v_k_910_);
v___x_1059_ = v___x_919_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_size_913_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_l_916_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_r_917_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_impl_1061_; lean_object* v___x_1062_; 
lean_dec(v_size_913_);
v_impl_1061_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_910_, v_v_911_, v_l_916_);
v___x_1062_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_917_) == 0)
{
lean_object* v_size_1063_; lean_object* v_size_1064_; lean_object* v_k_1065_; lean_object* v_v_1066_; lean_object* v_l_1067_; lean_object* v_r_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_size_1063_ = lean_ctor_get(v_r_917_, 0);
v_size_1064_ = lean_ctor_get(v_impl_1061_, 0);
lean_inc(v_size_1064_);
v_k_1065_ = lean_ctor_get(v_impl_1061_, 1);
lean_inc(v_k_1065_);
v_v_1066_ = lean_ctor_get(v_impl_1061_, 2);
lean_inc(v_v_1066_);
v_l_1067_ = lean_ctor_get(v_impl_1061_, 3);
lean_inc(v_l_1067_);
v_r_1068_ = lean_ctor_get(v_impl_1061_, 4);
lean_inc(v_r_1068_);
v___x_1069_ = lean_unsigned_to_nat(3u);
v___x_1070_ = lean_nat_mul(v___x_1069_, v_size_1063_);
v___x_1071_ = lean_nat_dec_lt(v___x_1070_, v_size_1064_);
lean_dec(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec(v_r_1068_);
lean_dec(v_l_1067_);
lean_dec(v_v_1066_);
lean_dec(v_k_1065_);
v___x_1072_ = lean_nat_add(v___x_1062_, v_size_1064_);
lean_dec(v_size_1064_);
v___x_1073_ = lean_nat_add(v___x_1072_, v_size_1063_);
lean_dec(v___x_1072_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 3, v_impl_1061_);
lean_ctor_set(v___x_919_, 0, v___x_1073_);
v___x_1075_ = v___x_919_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_impl_1061_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_r_917_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
else
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1142_; 
v_isSharedCheck_1142_ = !lean_is_exclusive(v_impl_1061_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1143_ = lean_ctor_get(v_impl_1061_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_impl_1061_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_impl_1061_, 2);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_impl_1061_, 1);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1061_, 0);
lean_dec(v_unused_1147_);
v___x_1078_ = v_impl_1061_;
v_isShared_1079_ = v_isSharedCheck_1142_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v_impl_1061_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1142_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_size_1080_; lean_object* v_size_1081_; lean_object* v_k_1082_; lean_object* v_v_1083_; lean_object* v_l_1084_; lean_object* v_r_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_size_1080_ = lean_ctor_get(v_l_1067_, 0);
v_size_1081_ = lean_ctor_get(v_r_1068_, 0);
v_k_1082_ = lean_ctor_get(v_r_1068_, 1);
v_v_1083_ = lean_ctor_get(v_r_1068_, 2);
v_l_1084_ = lean_ctor_get(v_r_1068_, 3);
v_r_1085_ = lean_ctor_get(v_r_1068_, 4);
v___x_1086_ = lean_unsigned_to_nat(2u);
v___x_1087_ = lean_nat_mul(v___x_1086_, v_size_1080_);
v___x_1088_ = lean_nat_dec_lt(v_size_1081_, v___x_1087_);
lean_dec(v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1117_; 
lean_inc(v_r_1085_);
lean_inc(v_l_1084_);
lean_inc(v_v_1083_);
lean_inc(v_k_1082_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_r_1068_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; 
v_unused_1118_ = lean_ctor_get(v_r_1068_, 4);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_r_1068_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_1068_, 2);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_r_1068_, 1);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_r_1068_, 0);
lean_dec(v_unused_1122_);
v___x_1090_ = v_r_1068_;
v_isShared_1091_ = v_isSharedCheck_1117_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_r_1068_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1117_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___x_1105_; lean_object* v___y_1107_; 
v___x_1092_ = lean_nat_add(v___x_1062_, v_size_1064_);
lean_dec(v_size_1064_);
v___x_1093_ = lean_nat_add(v___x_1092_, v_size_1063_);
lean_dec(v___x_1092_);
v___x_1105_ = lean_nat_add(v___x_1062_, v_size_1080_);
if (lean_obj_tag(v_l_1084_) == 0)
{
lean_object* v_size_1115_; 
v_size_1115_ = lean_ctor_get(v_l_1084_, 0);
lean_inc(v_size_1115_);
v___y_1107_ = v_size_1115_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
v___y_1107_ = v___x_1116_;
goto v___jp_1106_;
}
v___jp_1094_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_nat_add(v___y_1095_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec(v___y_1095_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v_r_917_);
lean_ctor_set(v___x_1090_, 3, v_r_1085_);
lean_ctor_set(v___x_1090_, 2, v_v_915_);
lean_ctor_set(v___x_1090_, 1, v_k_914_);
lean_ctor_set(v___x_1090_, 0, v___x_1098_);
v___x_1100_ = v___x_1090_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_r_1085_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_r_917_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1100_);
lean_ctor_set(v___x_1078_, 3, v___y_1096_);
lean_ctor_set(v___x_1078_, 2, v_v_1083_);
lean_ctor_set(v___x_1078_, 1, v_k_1082_);
lean_ctor_set(v___x_1078_, 0, v___x_1093_);
v___x_1102_ = v___x_1078_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_k_1082_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_v_1083_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v___y_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
v___jp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_nat_add(v___x_1105_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec(v___x_1105_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_l_1084_);
lean_ctor_set(v___x_919_, 3, v_l_1067_);
lean_ctor_set(v___x_919_, 2, v_v_1066_);
lean_ctor_set(v___x_919_, 1, v_k_1065_);
lean_ctor_set(v___x_919_, 0, v___x_1108_);
v___x_1110_ = v___x_919_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1065_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1066_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1067_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_l_1084_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_nat_add(v___x_1062_, v_size_1063_);
if (lean_obj_tag(v_r_1085_) == 0)
{
lean_object* v_size_1112_; 
v_size_1112_ = lean_ctor_get(v_r_1085_, 0);
lean_inc(v_size_1112_);
v___y_1095_ = v___x_1111_;
v___y_1096_ = v___x_1110_;
v___y_1097_ = v_size_1112_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___y_1095_ = v___x_1111_;
v___y_1096_ = v___x_1110_;
v___y_1097_ = v___x_1113_;
goto v___jp_1094_;
}
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_del_object(v___x_919_);
v___x_1123_ = lean_nat_add(v___x_1062_, v_size_1064_);
lean_dec(v_size_1064_);
v___x_1124_ = lean_nat_add(v___x_1123_, v_size_1063_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_nat_add(v___x_1062_, v_size_1063_);
v___x_1126_ = lean_nat_add(v___x_1125_, v_size_1081_);
lean_dec(v___x_1125_);
lean_inc_ref(v_r_917_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_r_917_);
lean_ctor_set(v___x_1078_, 3, v_r_1068_);
lean_ctor_set(v___x_1078_, 2, v_v_915_);
lean_ctor_set(v___x_1078_, 1, v_k_914_);
lean_ctor_set(v___x_1078_, 0, v___x_1126_);
v___x_1128_ = v___x_1078_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_r_1068_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_917_);
v___x_1128_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_isSharedCheck_1135_ = !lean_is_exclusive(v_r_917_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1136_ = lean_ctor_get(v_r_917_, 4);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_r_917_, 3);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_r_917_, 2);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_r_917_, 1);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_r_917_, 0);
lean_dec(v_unused_1140_);
v___x_1130_ = v_r_917_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v_r_917_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v___x_1128_);
lean_ctor_set(v___x_1130_, 3, v_l_1067_);
lean_ctor_set(v___x_1130_, 2, v_v_1066_);
lean_ctor_set(v___x_1130_, 1, v_k_1065_);
lean_ctor_set(v___x_1130_, 0, v___x_1124_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1065_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1066_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_l_1067_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1148_; 
v_l_1148_ = lean_ctor_get(v_impl_1061_, 3);
lean_inc(v_l_1148_);
if (lean_obj_tag(v_l_1148_) == 0)
{
lean_object* v_r_1149_; lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1162_; 
v_r_1149_ = lean_ctor_get(v_impl_1061_, 4);
v_k_1150_ = lean_ctor_get(v_impl_1061_, 1);
v_v_1151_ = lean_ctor_get(v_impl_1061_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_impl_1061_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1163_ = lean_ctor_get(v_impl_1061_, 3);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_impl_1061_, 0);
lean_dec(v_unused_1164_);
v___x_1153_ = v_impl_1061_;
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_r_1149_);
lean_inc(v_v_1151_);
lean_inc(v_k_1150_);
lean_dec(v_impl_1061_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1149_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 3, v_r_1149_);
lean_ctor_set(v___x_1153_, 2, v_v_915_);
lean_ctor_set(v___x_1153_, 1, v_k_914_);
lean_ctor_set(v___x_1153_, 0, v___x_1062_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_r_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_r_1149_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v___x_1157_);
lean_ctor_set(v___x_919_, 3, v_l_1148_);
lean_ctor_set(v___x_919_, 2, v_v_1151_);
lean_ctor_set(v___x_919_, 1, v_k_1150_);
lean_ctor_set(v___x_919_, 0, v___x_1155_);
v___x_1159_ = v___x_919_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1151_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_1148_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_r_1165_; 
v_r_1165_ = lean_ctor_get(v_impl_1061_, 4);
lean_inc(v_r_1165_);
if (lean_obj_tag(v_r_1165_) == 0)
{
lean_object* v_k_1166_; lean_object* v_v_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1190_; 
v_k_1166_ = lean_ctor_get(v_impl_1061_, 1);
v_v_1167_ = lean_ctor_get(v_impl_1061_, 2);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_impl_1061_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; 
v_unused_1191_ = lean_ctor_get(v_impl_1061_, 4);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_impl_1061_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1061_, 0);
lean_dec(v_unused_1193_);
v___x_1169_ = v_impl_1061_;
v_isShared_1170_ = v_isSharedCheck_1190_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_v_1167_);
lean_inc(v_k_1166_);
lean_dec(v_impl_1061_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1190_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_k_1171_; lean_object* v_v_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1186_; 
v_k_1171_ = lean_ctor_get(v_r_1165_, 1);
v_v_1172_ = lean_ctor_get(v_r_1165_, 2);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_r_1165_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; 
v_unused_1187_ = lean_ctor_get(v_r_1165_, 4);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_r_1165_, 3);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_r_1165_, 0);
lean_dec(v_unused_1189_);
v___x_1174_ = v_r_1165_;
v_isShared_1175_ = v_isSharedCheck_1186_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_v_1172_);
lean_inc(v_k_1171_);
lean_dec(v_r_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1186_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(3u);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v_l_1148_);
lean_ctor_set(v___x_1174_, 3, v_l_1148_);
lean_ctor_set(v___x_1174_, 2, v_v_1167_);
lean_ctor_set(v___x_1174_, 1, v_k_1166_);
lean_ctor_set(v___x_1174_, 0, v___x_1062_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_1166_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_1167_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_l_1148_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_l_1148_);
v___x_1178_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 4, v_l_1148_);
lean_ctor_set(v___x_1169_, 2, v_v_915_);
lean_ctor_set(v___x_1169_, 1, v_k_914_);
lean_ctor_set(v___x_1169_, 0, v___x_1062_);
v___x_1180_ = v___x_1169_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_l_1148_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_l_1148_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v___x_1180_);
lean_ctor_set(v___x_919_, 3, v___x_1178_);
lean_ctor_set(v___x_919_, 2, v_v_1172_);
lean_ctor_set(v___x_919_, 1, v_k_1171_);
lean_ctor_set(v___x_919_, 0, v___x_1176_);
v___x_1182_ = v___x_919_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_unsigned_to_nat(2u);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_r_1165_);
lean_ctor_set(v___x_919_, 3, v_impl_1061_);
lean_ctor_set(v___x_919_, 0, v___x_1194_);
v___x_1196_ = v___x_919_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_impl_1061_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_r_1165_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_k_910_);
lean_ctor_set(v___x_1200_, 2, v_v_911_);
lean_ctor_set(v___x_1200_, 3, v_t_912_);
lean_ctor_set(v___x_1200_, 4, v_t_912_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1201_, lean_object* v_b_1202_){
_start:
{
if (lean_obj_tag(v_as_x27_1201_) == 0)
{
return v_b_1202_;
}
else
{
lean_object* v_head_1203_; lean_object* v_tail_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v_r_1207_; 
v_head_1203_ = lean_ctor_get(v_as_x27_1201_, 0);
v_tail_1204_ = lean_ctor_get(v_as_x27_1201_, 1);
v_fst_1205_ = lean_ctor_get(v_head_1203_, 0);
v_snd_1206_ = lean_ctor_get(v_head_1203_, 1);
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
v_r_1207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1205_, v_snd_1206_, v_b_1202_);
v_as_x27_1201_ = v_tail_1204_;
v_b_1202_ = v_r_1207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1209_, lean_object* v_b_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1209_, v_b_1210_);
lean_dec(v_as_x27_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1220_, lean_object* v_expr_1221_, lean_object* v_lctx_1222_, lean_object* v_location_x3f_1223_, lean_object* v_docString_x3f_1224_, lean_object* v_mkDocString_x3f_1225_, uint8_t v_explicit_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___y_1234_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_fmt_1220_);
v___x_1229_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1230_ = lean_box(0);
v___x_1231_ = 0;
v___x_1232_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1232_, 0, v___x_1229_);
lean_ctor_set(v___x_1232_, 1, v_lctx_1222_);
lean_ctor_set(v___x_1232_, 2, v___x_1230_);
lean_ctor_set(v___x_1232_, 3, v_expr_1221_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*4, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*4 + 1, v___x_1231_);
if (lean_obj_tag(v_mkDocString_x3f_1225_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1224_) == 0)
{
v___y_1234_ = v_mkDocString_x3f_1225_;
goto v___jp_1233_;
}
else
{
lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_val_1244_ = lean_ctor_get(v_docString_x3f_1224_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_docString_x3f_1224_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v_docString_x3f_1224_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_dec(v_docString_x3f_1224_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___f_1248_; lean_object* v___x_1250_; 
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1248_, 0, v_val_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___f_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___f_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
v___y_1234_ = v___x_1250_;
goto v___jp_1233_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1224_);
v___y_1234_ = v_mkDocString_x3f_1225_;
goto v___jp_1233_;
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_r_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1235_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1235_, 0, v___x_1232_);
lean_ctor_set(v___x_1235_, 1, v_location_x3f_1223_);
lean_ctor_set(v___x_1235_, 2, v___y_1234_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*3, v_explicit_1226_);
v___x_1236_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1227_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v_r_1240_ = lean_box(1);
v___x_1241_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1239_, v_r_1240_);
lean_dec_ref_known(v___x_1239_, 2);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1228_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1253_, lean_object* v_expr_1254_, lean_object* v_lctx_1255_, lean_object* v_location_x3f_1256_, lean_object* v_docString_x3f_1257_, lean_object* v_mkDocString_x3f_1258_, lean_object* v_explicit_1259_){
_start:
{
uint8_t v_explicit_boxed_1260_; lean_object* v_res_1261_; 
v_explicit_boxed_1260_ = lean_unbox(v_explicit_1259_);
v_res_1261_ = l_Lean_MessageData_withExprHover(v_fmt_1253_, v_expr_1254_, v_lctx_1255_, v_location_x3f_1256_, v_docString_x3f_1257_, v_mkDocString_x3f_1258_, v_explicit_boxed_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1262_, lean_object* v_k_1263_, lean_object* v_v_1264_, lean_object* v_t_1265_, lean_object* v_hl_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1263_, v_v_1264_, v_t_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1268_, lean_object* v_as_x27_1269_, lean_object* v_b_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1269_, v_b_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1273_, lean_object* v_as_x27_1274_, lean_object* v_b_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1273_, v_as_x27_1274_, v_b_1275_, v_a_1276_);
lean_dec(v_as_x27_1274_);
lean_dec(v_as_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1278_, lean_object* v_expr_1279_, lean_object* v_location_x3f_1280_, lean_object* v_docString_x3f_1281_, lean_object* v_mkDocString_x3f_1282_, uint8_t v_explicit_1283_, lean_object* v_toPure_1284_, lean_object* v_lctx_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = l_Lean_MessageData_withExprHover(v_fmt_1278_, v_expr_1279_, v_lctx_1285_, v_location_x3f_1280_, v_docString_x3f_1281_, v_mkDocString_x3f_1282_, v_explicit_1283_);
v___x_1287_ = lean_apply_2(v_toPure_1284_, lean_box(0), v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1288_, lean_object* v_expr_1289_, lean_object* v_location_x3f_1290_, lean_object* v_docString_x3f_1291_, lean_object* v_mkDocString_x3f_1292_, lean_object* v_explicit_1293_, lean_object* v_toPure_1294_, lean_object* v_lctx_1295_){
_start:
{
uint8_t v_explicit_boxed_1296_; lean_object* v_res_1297_; 
v_explicit_boxed_1296_ = lean_unbox(v_explicit_1293_);
v_res_1297_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1288_, v_expr_1289_, v_location_x3f_1290_, v_docString_x3f_1291_, v_mkDocString_x3f_1292_, v_explicit_boxed_1296_, v_toPure_1294_, v_lctx_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_fmt_1300_, lean_object* v_expr_1301_, lean_object* v_lctx_x3f_1302_, lean_object* v_location_x3f_1303_, lean_object* v_docString_x3f_1304_, lean_object* v_mkDocString_x3f_1305_, uint8_t v_explicit_1306_){
_start:
{
lean_object* v_toApplicative_1307_; lean_object* v_toBind_1308_; lean_object* v_toPure_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; 
v_toApplicative_1307_ = lean_ctor_get(v_inst_1298_, 0);
lean_inc_ref(v_toApplicative_1307_);
v_toBind_1308_ = lean_ctor_get(v_inst_1298_, 1);
lean_inc(v_toBind_1308_);
lean_dec_ref(v_inst_1298_);
v_toPure_1309_ = lean_ctor_get(v_toApplicative_1307_, 1);
lean_inc_n(v_toPure_1309_, 2);
lean_dec_ref(v_toApplicative_1307_);
v___x_1310_ = lean_box(v_explicit_1306_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1311_, 0, v_fmt_1300_);
lean_closure_set(v___f_1311_, 1, v_expr_1301_);
lean_closure_set(v___f_1311_, 2, v_location_x3f_1303_);
lean_closure_set(v___f_1311_, 3, v_docString_x3f_1304_);
lean_closure_set(v___f_1311_, 4, v_mkDocString_x3f_1305_);
lean_closure_set(v___f_1311_, 5, v___x_1310_);
lean_closure_set(v___f_1311_, 6, v_toPure_1309_);
if (lean_obj_tag(v_lctx_x3f_1302_) == 0)
{
lean_object* v___x_1312_; 
lean_dec(v_toPure_1309_);
v___x_1312_ = lean_apply_4(v_toBind_1308_, lean_box(0), lean_box(0), v_inst_1299_, v___f_1311_);
return v___x_1312_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_inst_1299_);
v_val_1313_ = lean_ctor_get(v_lctx_x3f_1302_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v_lctx_x3f_1302_, 1);
v___x_1314_ = lean_apply_2(v_toPure_1309_, lean_box(0), v_val_1313_);
v___x_1315_ = lean_apply_4(v_toBind_1308_, lean_box(0), lean_box(0), v___x_1314_, v___f_1311_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_fmt_1318_, lean_object* v_expr_1319_, lean_object* v_lctx_x3f_1320_, lean_object* v_location_x3f_1321_, lean_object* v_docString_x3f_1322_, lean_object* v_mkDocString_x3f_1323_, lean_object* v_explicit_1324_){
_start:
{
uint8_t v_explicit_boxed_1325_; lean_object* v_res_1326_; 
v_explicit_boxed_1325_ = lean_unbox(v_explicit_1324_);
v_res_1326_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1316_, v_inst_1317_, v_fmt_1318_, v_expr_1319_, v_lctx_x3f_1320_, v_location_x3f_1321_, v_docString_x3f_1322_, v_mkDocString_x3f_1323_, v_explicit_boxed_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_fmt_1330_, lean_object* v_expr_1331_, lean_object* v_lctx_x3f_1332_, lean_object* v_location_x3f_1333_, lean_object* v_docString_x3f_1334_, lean_object* v_mkDocString_x3f_1335_, uint8_t v_explicit_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1328_, v_inst_1329_, v_fmt_1330_, v_expr_1331_, v_lctx_x3f_1332_, v_location_x3f_1333_, v_docString_x3f_1334_, v_mkDocString_x3f_1335_, v_explicit_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_fmt_1341_, lean_object* v_expr_1342_, lean_object* v_lctx_x3f_1343_, lean_object* v_location_x3f_1344_, lean_object* v_docString_x3f_1345_, lean_object* v_mkDocString_x3f_1346_, lean_object* v_explicit_1347_){
_start:
{
uint8_t v_explicit_boxed_1348_; lean_object* v_res_1349_; 
v_explicit_boxed_1348_ = lean_unbox(v_explicit_1347_);
v_res_1349_ = l_Lean_MessageData_withExprHoverM(v_m_1338_, v_inst_1339_, v_inst_1340_, v_fmt_1341_, v_expr_1342_, v_lctx_x3f_1343_, v_location_x3f_1344_, v_docString_x3f_1345_, v_mkDocString_x3f_1346_, v_explicit_boxed_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1350_, lean_object* v_display_1351_, lean_object* v_toPure_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_____do__lift_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1355_, v_userName_1350_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_inst_1354_);
lean_dec_ref(v_inst_1353_);
v___x_1357_ = l_Lean_MessageData_ofName(v_display_1351_);
v___x_1358_ = lean_apply_2(v_toPure_1352_, lean_box(0), v___x_1357_);
return v___x_1358_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_toPure_1352_);
v_val_1359_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1361_ = v___x_1356_;
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_val_1359_);
lean_dec(v___x_1356_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1363_ = 1;
v___x_1364_ = l_Lean_Name_toString(v_display_1351_, v___x_1363_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 3);
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1367_ = l_Lean_LocalDecl_fvarId(v_val_1359_);
lean_dec(v_val_1359_);
v___x_1368_ = l_Lean_Expr_fvar___override(v___x_1367_);
v___x_1369_ = lean_box(0);
v___x_1370_ = 0;
v___x_1371_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1353_, v_inst_1354_, v___x_1366_, v___x_1368_, v___x_1369_, v___x_1369_, v___x_1369_, v___x_1369_, v___x_1370_);
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1374_, lean_object* v_display_1375_, lean_object* v_toPure_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_____do__lift_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1374_, v_display_1375_, v_toPure_1376_, v_inst_1377_, v_inst_1378_, v_____do__lift_1379_);
lean_dec_ref(v_____do__lift_1379_);
lean_dec(v_userName_1374_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_userName_1383_){
_start:
{
lean_object* v_toApplicative_1384_; lean_object* v_toBind_1385_; lean_object* v_toPure_1386_; lean_object* v_display_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; 
v_toApplicative_1384_ = lean_ctor_get(v_inst_1381_, 0);
v_toBind_1385_ = lean_ctor_get(v_inst_1381_, 1);
lean_inc(v_toBind_1385_);
v_toPure_1386_ = lean_ctor_get(v_toApplicative_1384_, 1);
lean_inc(v_toPure_1386_);
lean_inc(v_userName_1383_);
v_display_1387_ = lean_simp_macro_scopes(v_userName_1383_);
lean_inc(v_inst_1382_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1388_, 0, v_userName_1383_);
lean_closure_set(v___f_1388_, 1, v_display_1387_);
lean_closure_set(v___f_1388_, 2, v_toPure_1386_);
lean_closure_set(v___f_1388_, 3, v_inst_1381_);
lean_closure_set(v___f_1388_, 4, v_inst_1382_);
v___x_1389_ = lean_apply_4(v_toBind_1385_, lean_box(0), lean_box(0), v_inst_1382_, v___f_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_userName_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1391_, v_inst_1392_, v_userName_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1395_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_ctor_set(v___x_1400_, 2, v___x_1399_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
lean_ctor_set(v___x_1400_, 4, v___x_1398_);
lean_ctor_set(v___x_1400_, 5, v___x_1398_);
lean_ctor_set(v___x_1400_, 6, v___x_1398_);
lean_ctor_set(v___x_1400_, 7, v___x_1398_);
lean_ctor_set(v___x_1400_, 8, v___x_1398_);
lean_ctor_set(v___x_1400_, 9, v___x_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1401_, lean_object* v_a_1402_){
_start:
{
switch(lean_obj_tag(v_a_1402_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1401_) == 0)
{
lean_object* v_hasSyntheticSorry_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_hasSyntheticSorry_1403_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_hasSyntheticSorry_1403_);
lean_dec_ref_known(v_a_1402_, 2);
v___x_1404_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1405_ = lean_apply_1(v_hasSyntheticSorry_1403_, v___x_1404_);
v___x_1406_ = lean_unbox(v___x_1405_);
return v___x_1406_;
}
else
{
lean_object* v_hasSyntheticSorry_1407_; lean_object* v_val_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_hasSyntheticSorry_1407_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_hasSyntheticSorry_1407_);
lean_dec_ref_known(v_a_1402_, 2);
v_val_1408_ = lean_ctor_get(v_mctx_x3f_1401_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_mctx_x3f_1401_, 1);
v___x_1409_ = lean_apply_1(v_hasSyntheticSorry_1407_, v_val_1408_);
v___x_1410_ = lean_unbox(v___x_1409_);
return v___x_1410_;
}
}
case 3:
{
lean_object* v_a_1411_; lean_object* v_a_1412_; lean_object* v_mctx_1413_; lean_object* v___x_1414_; 
lean_dec(v_mctx_x3f_1401_);
v_a_1411_ = lean_ctor_get(v_a_1402_, 0);
lean_inc_ref(v_a_1411_);
v_a_1412_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1412_);
lean_dec_ref_known(v_a_1402_, 2);
v_mctx_1413_ = lean_ctor_get(v_a_1411_, 1);
lean_inc_ref(v_mctx_1413_);
lean_dec_ref(v_a_1411_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_mctx_1413_);
v_mctx_x3f_1401_ = v___x_1414_;
v_a_1402_ = v_a_1412_;
goto _start;
}
case 4:
{
lean_object* v_a_1416_; 
v_a_1416_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1416_);
lean_dec_ref_known(v_a_1402_, 2);
v_a_1402_ = v_a_1416_;
goto _start;
}
case 5:
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1418_);
lean_dec_ref_known(v_a_1402_, 2);
v_a_1402_ = v_a_1418_;
goto _start;
}
case 6:
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v_a_1402_, 0);
lean_inc_ref(v_a_1420_);
lean_dec_ref_known(v_a_1402_, 1);
v_a_1402_ = v_a_1420_;
goto _start;
}
case 7:
{
lean_object* v_a_1422_; lean_object* v_a_1423_; uint8_t v___x_1424_; 
v_a_1422_ = lean_ctor_get(v_a_1402_, 0);
lean_inc_ref(v_a_1422_);
v_a_1423_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1423_);
lean_dec_ref_known(v_a_1402_, 2);
lean_inc(v_mctx_x3f_1401_);
v___x_1424_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1401_, v_a_1422_);
if (v___x_1424_ == 0)
{
v_a_1402_ = v_a_1423_;
goto _start;
}
else
{
lean_dec_ref(v_a_1423_);
lean_dec(v_mctx_x3f_1401_);
return v___x_1424_;
}
}
case 8:
{
lean_object* v_a_1426_; 
v_a_1426_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1426_);
lean_dec_ref_known(v_a_1402_, 2);
v_a_1402_ = v_a_1426_;
goto _start;
}
case 11:
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_a_1428_);
lean_dec_ref_known(v_a_1402_, 2);
v_a_1402_ = v_a_1428_;
goto _start;
}
case 9:
{
lean_object* v_msg_1430_; lean_object* v_children_1431_; uint8_t v___x_1432_; 
v_msg_1430_ = lean_ctor_get(v_a_1402_, 1);
lean_inc_ref(v_msg_1430_);
v_children_1431_ = lean_ctor_get(v_a_1402_, 2);
lean_inc_ref(v_children_1431_);
lean_dec_ref_known(v_a_1402_, 3);
lean_inc(v_mctx_x3f_1401_);
v___x_1432_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1401_, v_msg_1430_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_array_get_size(v_children_1431_);
v___x_1435_ = lean_nat_dec_lt(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec_ref(v_children_1431_);
lean_dec(v_mctx_x3f_1401_);
return v___x_1432_;
}
else
{
if (v___x_1435_ == 0)
{
lean_dec_ref(v_children_1431_);
lean_dec(v_mctx_x3f_1401_);
return v___x_1432_;
}
else
{
size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_of_nat(v___x_1434_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1401_, v_children_1431_, v___x_1436_, v___x_1437_);
lean_dec_ref(v_children_1431_);
return v___x_1438_;
}
}
}
else
{
lean_dec_ref(v_children_1431_);
lean_dec(v_mctx_x3f_1401_);
return v___x_1432_;
}
}
default: 
{
uint8_t v___x_1439_; 
lean_dec_ref(v_a_1402_);
lean_dec(v_mctx_x3f_1401_);
v___x_1439_ = 0;
return v___x_1439_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1440_, lean_object* v_as_1441_, size_t v_i_1442_, size_t v_stop_1443_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_eq(v_i_1442_, v_stop_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = lean_array_uget_borrowed(v_as_1441_, v_i_1442_);
lean_inc(v___x_1445_);
lean_inc(v_mctx_x3f_1440_);
v___x_1446_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1440_, v___x_1445_);
if (v___x_1446_ == 0)
{
size_t v___x_1447_; size_t v___x_1448_; 
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_add(v_i_1442_, v___x_1447_);
v_i_1442_ = v___x_1448_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1440_);
return v___x_1446_;
}
}
else
{
uint8_t v___x_1450_; 
lean_dec(v_mctx_x3f_1440_);
v___x_1450_ = 0;
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1451_, lean_object* v_as_1452_, lean_object* v_i_1453_, lean_object* v_stop_1454_){
_start:
{
size_t v_i_boxed_1455_; size_t v_stop_boxed_1456_; uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_i_boxed_1455_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_stop_boxed_1456_ = lean_unbox_usize(v_stop_1454_);
lean_dec(v_stop_1454_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1451_, v_as_1452_, v_i_boxed_1455_, v_stop_boxed_1456_);
lean_dec_ref(v_as_1452_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1459_, lean_object* v_a_1460_){
_start:
{
uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_res_1461_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1459_, v_a_1460_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1464_, v_msg_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1466_){
_start:
{
uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1466_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_1469_, lean_object* v_decl_1470_, lean_object* v_ref_1471_){
_start:
{
lean_object* v_defValue_1473_; lean_object* v_descr_1474_; lean_object* v_deprecation_x3f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_defValue_1473_ = lean_ctor_get(v_decl_1470_, 0);
v_descr_1474_ = lean_ctor_get(v_decl_1470_, 1);
v_deprecation_x3f_1475_ = lean_ctor_get(v_decl_1470_, 2);
lean_inc(v_defValue_1473_);
v___x_1476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_defValue_1473_);
lean_inc(v_deprecation_x3f_1475_);
lean_inc_ref(v_descr_1474_);
lean_inc_n(v_name_1469_, 2);
v___x_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1477_, 0, v_name_1469_);
lean_ctor_set(v___x_1477_, 1, v_ref_1471_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_ctor_set(v___x_1477_, 3, v_descr_1474_);
lean_ctor_set(v___x_1477_, 4, v_deprecation_x3f_1475_);
v___x_1478_ = lean_register_option(v_name_1469_, v___x_1477_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1487_);
v___x_1480_ = v___x_1478_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1478_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_inc(v_defValue_1473_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_name_1469_);
lean_ctor_set(v___x_1482_, 1, v_defValue_1473_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_name_1469_);
v_a_1488_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1478_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1478_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1496_, lean_object* v_decl_1497_, lean_object* v_ref_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_1496_, v_decl_1497_, v_ref_1498_);
lean_dec_ref(v_decl_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1515_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1516_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1517_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_1514_, v___x_1515_, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_nat_to_int(v_a_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = l_instMonadBaseIO;
v___x_1524_ = l_instInhabitedOfMonad___redArg(v___x_1523_, v___x_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_2214__overap_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2214__overap_1528_ = lean_panic_fn_borrowed(v___x_1527_, v_msg_1525_);
v___x_1529_ = lean_apply_1(v___x_2214__overap_1528_, lean_box(0));
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_dec(v_x_1533_);
return v_x_1534_;
}
else
{
lean_object* v_head_1536_; lean_object* v_tail_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
v_head_1536_ = lean_ctor_get(v_x_1535_, 0);
v_tail_1537_ = lean_ctor_get(v_x_1535_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1539_ = v_x_1535_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_tail_1537_);
lean_inc(v_head_1536_);
lean_dec(v_x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
lean_inc(v_x_1533_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 5);
lean_ctor_set(v___x_1539_, 1, v_x_1533_);
lean_ctor_set(v___x_1539_, 0, v_x_1534_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_x_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_x_1533_);
v___x_1542_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v_head_1536_);
v_x_1534_ = v___x_1543_;
v_x_1535_ = v_tail_1537_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1547_) == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_x_1548_);
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
else
{
lean_object* v_tail_1550_; 
v_tail_1550_ = lean_ctor_get(v_x_1547_, 1);
if (lean_obj_tag(v_tail_1550_) == 0)
{
lean_object* v_head_1551_; 
lean_dec(v_x_1548_);
v_head_1551_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_head_1551_);
lean_dec_ref_known(v_x_1547_, 2);
return v_head_1551_;
}
else
{
lean_object* v_head_1552_; lean_object* v___x_1553_; 
lean_inc(v_tail_1550_);
v_head_1552_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_head_1552_);
lean_dec_ref_known(v_x_1547_, 2);
v___x_1553_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1548_, v_head_1552_, v_tail_1550_);
return v___x_1553_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1568_; double v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = lean_float_of_nat(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
switch(lean_obj_tag(v_x_1575_))
{
case 0:
{
lean_object* v_a_1577_; lean_object* v_fmt_1578_; 
lean_dec(v_x_1574_);
lean_dec_ref(v_x_1573_);
v_a_1577_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_a_1577_);
lean_dec_ref_known(v_x_1575_, 1);
v_fmt_1578_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_fmt_1578_);
lean_dec_ref(v_a_1577_);
return v_fmt_1578_;
}
case 1:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_x_1573_);
v_a_1579_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1580_ = l_Lean_formatRawGoal(v_a_1579_);
return v___x_1580_;
}
else
{
lean_object* v_a_1581_; lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1581_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v_x_1575_, 1);
v_val_1582_ = lean_ctor_get(v_x_1574_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_x_1574_, 1);
v___x_1583_ = l_Lean_MessageData_mkPPContext(v_x_1573_, v_val_1582_);
lean_dec(v_val_1582_);
lean_dec_ref(v_x_1573_);
v___x_1584_ = l_Lean_ppGoal(v___x_1583_, v_a_1581_);
return v___x_1584_;
}
}
case 3:
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1587_; 
lean_dec(v_x_1574_);
v_a_1585_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_a_1585_);
v_a_1586_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_ref(v_a_1586_);
lean_dec_ref_known(v_x_1575_, 2);
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1585_);
v_x_1574_ = v___x_1587_;
v_x_1575_ = v_a_1586_;
goto _start;
}
case 4:
{
lean_object* v_a_1589_; lean_object* v_a_1590_; 
lean_dec_ref(v_x_1573_);
v_a_1589_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_a_1589_);
v_a_1590_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_ref(v_a_1590_);
lean_dec_ref_known(v_x_1575_, 2);
v_x_1573_ = v_a_1589_;
v_x_1575_ = v_a_1590_;
goto _start;
}
case 5:
{
lean_object* v_a_1592_; lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1602_; 
v_a_1592_ = lean_ctor_get(v_x_1575_, 0);
v_a_1593_ = lean_ctor_get(v_x_1575_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1595_ = v_x_1575_;
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_inc(v_a_1592_);
lean_dec(v_x_1575_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1597_ = l_Lean_MessageData_formatAux(v_x_1573_, v_x_1574_, v_a_1593_);
v___x_1598_ = lean_nat_to_int(v_a_1592_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 4);
lean_ctor_set(v___x_1595_, 1, v___x_1597_);
lean_ctor_set(v___x_1595_, 0, v___x_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1597_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
case 6:
{
lean_object* v_a_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; 
v_a_1603_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_a_1603_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1604_ = l_Lean_MessageData_formatAux(v_x_1573_, v_x_1574_, v_a_1603_);
v___x_1605_ = 0;
v___x_1606_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*1, v___x_1605_);
return v___x_1606_;
}
case 7:
{
lean_object* v_a_1607_; lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
v_a_1607_ = lean_ctor_get(v_x_1575_, 0);
v_a_1608_ = lean_ctor_get(v_x_1575_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1610_ = v_x_1575_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_inc(v_a_1607_);
lean_dec(v_x_1575_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_inc(v_x_1574_);
lean_inc_ref(v_x_1573_);
v___x_1612_ = l_Lean_MessageData_formatAux(v_x_1573_, v_x_1574_, v_a_1607_);
v___x_1613_ = l_Lean_MessageData_formatAux(v_x_1573_, v_x_1574_, v_a_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 5);
lean_ctor_set(v___x_1610_, 1, v___x_1613_);
lean_ctor_set(v___x_1610_, 0, v___x_1612_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
case 9:
{
lean_object* v_data_1618_; lean_object* v_msg_1619_; lean_object* v_children_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v_cls_1637_; lean_object* v_result_x3f_1638_; double v_startTime_1639_; double v_stopTime_1640_; lean_object* v_msg_1642_; uint8_t v___x_1657_; 
v_data_1618_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_data_1618_);
v_msg_1619_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_ref(v_msg_1619_);
v_children_1620_ = lean_ctor_get(v_x_1575_, 2);
lean_inc_ref(v_children_1620_);
lean_dec_ref_known(v_x_1575_, 3);
v_sz_1621_ = lean_array_size(v_children_1620_);
v___x_1622_ = ((size_t)0ULL);
lean_inc(v_x_1574_);
lean_inc_ref(v_x_1573_);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1573_, v_x_1574_, v_sz_1621_, v___x_1622_, v_children_1620_);
v_cls_1637_ = lean_ctor_get(v_data_1618_, 0);
lean_inc(v_cls_1637_);
v_result_x3f_1638_ = lean_ctor_get(v_data_1618_, 1);
lean_inc(v_result_x3f_1638_);
v_startTime_1639_ = lean_ctor_get_float(v_data_1618_, sizeof(void*)*3);
v_stopTime_1640_ = lean_ctor_get_float(v_data_1618_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1618_);
v___x_1657_ = l_Lean_Name_isAnonymous(v_cls_1637_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; double v___x_1673_; uint8_t v___x_1674_; 
v___x_1658_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1659_ = 1;
v___x_1660_ = l_Lean_Name_toString(v_cls_1637_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1658_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1673_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1674_ = lean_float_beq(v_startTime_1639_, v___x_1673_);
if (v___x_1674_ == 0)
{
goto v___jp_1665_;
}
else
{
if (v___x_1657_ == 0)
{
v_msg_1642_ = v___x_1664_;
goto v___jp_1641_;
}
else
{
goto v___jp_1665_;
}
}
v___jp_1665_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; double v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1666_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_float_sub(v_stopTime_1640_, v_startTime_1639_);
v___x_1669_ = lean_float_to_string(v___x_1668_);
v___x_1670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1667_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1663_);
v_msg_1642_ = v___x_1672_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v_result_x3f_1638_);
lean_dec(v_cls_1637_);
lean_dec_ref(v_msg_1619_);
lean_dec(v_x_1574_);
lean_dec_ref(v_x_1573_);
v___x_1675_ = lean_array_to_list(v___x_1623_);
v___x_1676_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1677_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
v___jp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1627_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___y_1626_);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_array_to_list(v___x_1623_);
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1635_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1633_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1629_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
return v___x_1636_;
}
v___jp_1641_:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_MessageData_formatAux(v_x_1573_, v_x_1574_, v_msg_1619_);
if (lean_obj_tag(v_result_x3f_1638_) == 0)
{
v___y_1625_ = v_msg_1642_;
v___y_1626_ = v___x_1643_;
goto v___jp_1624_;
}
else
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1656_; 
v_val_1644_ = lean_ctor_get(v_result_x3f_1638_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_result_x3f_1638_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1646_ = v_result_x3f_1638_;
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v_result_x3f_1638_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = lean_unbox(v_val_1644_);
lean_dec(v_val_1644_);
v___x_1649_ = l_Lean_TraceResult_toEmoji(v___x_1648_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 3);
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1643_);
v___y_1625_ = v_msg_1642_;
v___y_1626_ = v___x_1654_;
goto v___jp_1624_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1678_; lean_object* v___x_1679_; lean_object* v___y_1681_; 
v_f_1678_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_f_1678_);
lean_dec_ref_known(v_x_1575_, 2);
v___x_1679_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_box(0);
v___y_1681_ = v___x_1697_;
goto v___jp_1680_;
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1698_ = lean_ctor_get(v_x_1574_, 0);
v___x_1699_ = l_Lean_MessageData_mkPPContext(v_x_1573_, v_val_1698_);
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
v___y_1681_ = v___x_1700_;
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_apply_2(v_f_1678_, v___y_1681_, lean_box(0));
v___x_1683_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1682_, v___x_1679_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; 
lean_dec(v___x_1682_);
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_x_1575_ = v_val_1684_;
goto _start;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v___x_1683_);
lean_dec(v_x_1574_);
lean_dec_ref(v_x_1573_);
v___x_1686_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1687_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1688_ = lean_unsigned_to_nat(409u);
v___x_1689_ = lean_unsigned_to_nat(8u);
v___x_1690_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1691_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1682_);
lean_dec(v___x_1682_);
v___x_1692_ = 1;
v___x_1693_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_string_append(v___x_1690_, v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = l_mkPanicMessageWithDecl(v___x_1686_, v___x_1687_, v___x_1688_, v___x_1689_, v___x_1694_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1695_);
return v___x_1696_;
}
}
}
default: 
{
lean_object* v_a_1701_; 
v_a_1701_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_ref(v_a_1701_);
lean_dec_ref(v_x_1575_);
v_x_1575_ = v_a_1701_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1703_, lean_object* v_x_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_bs_1707_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1709_ == 0)
{
lean_dec(v_x_1704_);
lean_dec_ref(v_x_1703_);
return v_bs_1707_;
}
else
{
lean_object* v_v_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v_bs_x27_1713_; size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v_v_1710_ = lean_array_uget_borrowed(v_bs_1707_, v_i_1706_);
lean_inc(v_v_1710_);
lean_inc(v_x_1704_);
lean_inc_ref(v_x_1703_);
v___x_1711_ = l_Lean_MessageData_formatAux(v_x_1703_, v_x_1704_, v_v_1710_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v_bs_x27_1713_ = lean_array_uset(v_bs_1707_, v_i_1706_, v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1706_, v___x_1714_);
v___x_1716_ = lean_array_uset(v_bs_x27_1713_, v_i_1706_, v___x_1711_);
v_i_1706_ = v___x_1715_;
v_bs_1707_ = v___x_1716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_bs_1722_, lean_object* v___y_1723_){
_start:
{
size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1718_, v_x_1719_, v_sz_boxed_1724_, v_i_boxed_1725_, v_bs_1722_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_MessageData_formatAux(v_x_1727_, v_x_1728_, v_x_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1735_, lean_object* v_ctx_x3f_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1739_ = l_Lean_MessageData_formatAux(v___x_1738_, v_ctx_x3f_1736_, v_msgData_1735_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1740_, lean_object* v_ctx_x3f_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_MessageData_format(v_msgData_1740_, v_ctx_x3f_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1746_ = lean_box(0);
v___x_1747_ = l_Lean_MessageData_format(v_msgData_1744_, v___x_1746_);
v___x_1748_ = l_Std_Format_defWidth;
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = l_Std_Format_pretty(v___x_1747_, v___x_1748_, v___x_1749_, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_MessageData_toString(v_msgData_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_a_1754_);
lean_ctor_set(v___x_1756_, 1, v_a_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_s_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_a_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1785_){
_start:
{
if (lean_obj_tag(v_o_1785_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1786_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; 
v_val_1787_ = lean_ctor_get(v_o_1785_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_o_1785_, 1);
v___x_1788_ = l_Lean_MessageData_ofExpr(v_val_1787_);
return v___x_1788_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1792_ = l_Lean_MessageData_ofFormat(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1797_ = l_Lean_MessageData_ofFormat(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1798_, lean_object* v_i_1799_, lean_object* v_acc_1800_){
_start:
{
lean_object* v___y_1802_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_size(v_es_1798_);
v___x_1807_ = lean_nat_dec_lt(v_i_1799_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_i_1799_);
v___x_1808_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_acc_1800_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
return v___x_1809_;
}
else
{
lean_object* v_e_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_e_1810_ = lean_array_fget_borrowed(v_es_1798_, v_i_1799_);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_nat_dec_eq(v_i_1799_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_acc_1800_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
lean_inc(v_e_1810_);
v___x_1815_ = l_Lean_MessageData_ofExpr(v_e_1810_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___y_1802_ = v___x_1816_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc(v_e_1810_);
v___x_1817_ = l_Lean_MessageData_ofExpr(v_e_1810_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_acc_1800_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___y_1802_ = v___x_1818_;
goto v___jp_1801_;
}
}
v___jp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_add(v_i_1799_, v___x_1803_);
lean_dec(v_i_1799_);
v_i_1799_ = v___x_1804_;
v_acc_1800_ = v___y_1802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1819_, lean_object* v_i_1820_, lean_object* v_acc_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1819_, v_i_1820_, v_acc_1821_);
lean_dec_ref(v_es_1819_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1827_ = l_Lean_MessageData_ofFormat(v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1831_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1828_, v___x_1829_, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1832_);
lean_dec_ref(v_es_1832_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1836_, lean_object* v_f_1837_, lean_object* v_r_1838_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1839_ = lean_string_length(v_l_1836_);
v___x_1840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_l_1836_);
v___x_1841_ = l_Lean_MessageData_ofFormat(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_f_1837_);
v___x_1843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_r_1838_);
v___x_1844_ = l_Lean_MessageData_ofFormat(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1842_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1839_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1848_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1850_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1851_ = l_Lean_MessageData_bracket(v___x_1849_, v_f_1848_, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1854_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1855_ = l_Lean_MessageData_bracket(v___x_1853_, v_f_1852_, v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1856_) == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_x_1857_);
v___x_1858_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1858_;
}
else
{
lean_object* v_tail_1859_; 
v_tail_1859_ = lean_ctor_get(v_x_1856_, 1);
if (lean_obj_tag(v_tail_1859_) == 0)
{
lean_object* v_head_1860_; 
lean_dec_ref(v_x_1857_);
v_head_1860_ = lean_ctor_get(v_x_1856_, 0);
lean_inc(v_head_1860_);
lean_dec_ref_known(v_x_1856_, 2);
return v_head_1860_;
}
else
{
lean_object* v_head_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1870_; 
lean_inc(v_tail_1859_);
v_head_1861_ = lean_ctor_get(v_x_1856_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v_x_1856_, 1);
lean_dec(v_unused_1871_);
v___x_1863_ = v_x_1856_;
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_head_1861_);
lean_dec(v_x_1856_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
lean_inc_ref(v_x_1857_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 7);
lean_ctor_set(v___x_1863_, 1, v_x_1857_);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_head_1861_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_x_1857_);
v___x_1866_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = l_Lean_MessageData_joinSep(v_tail_1859_, v_x_1857_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
return v___x_1868_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1876_ = l_Lean_MessageData_ofFormat(v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1881_ = l_Lean_MessageData_ofFormat(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_box(1);
v___x_1883_ = l_Lean_MessageData_ofFormat(v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1885_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1890_ = l_Lean_MessageData_joinSep(v_x_1887_, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_sbracket(v___x_1890_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_array_to_list(v_msgs_1892_);
v___x_1894_ = l_Lean_MessageData_ofList(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1899_ = l_Lean_MessageData_ofFormat(v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1904_ = l_Lean_MessageData_ofFormat(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1909_ = l_Lean_MessageData_ofFormat(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1910_){
_start:
{
if (lean_obj_tag(v_xs_1910_) == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1911_;
}
else
{
lean_object* v_tail_1912_; 
v_tail_1912_ = lean_ctor_get(v_xs_1910_, 1);
lean_inc(v_tail_1912_);
if (lean_obj_tag(v_tail_1912_) == 0)
{
lean_object* v_head_1913_; 
v_head_1913_ = lean_ctor_get(v_xs_1910_, 0);
lean_inc(v_head_1913_);
lean_dec_ref_known(v_xs_1910_, 2);
return v_head_1913_;
}
else
{
lean_object* v_tail_1914_; 
v_tail_1914_ = lean_ctor_get(v_tail_1912_, 1);
if (lean_obj_tag(v_tail_1914_) == 0)
{
lean_object* v_head_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1932_; 
v_head_1915_ = lean_ctor_get(v_xs_1910_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_xs_1910_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_xs_1910_, 1);
lean_dec(v_unused_1933_);
v___x_1917_ = v_xs_1910_;
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_head_1915_);
lean_dec(v_xs_1910_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_head_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1930_; 
v_head_1919_ = lean_ctor_get(v_tail_1912_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_tail_1912_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_tail_1912_, 1);
lean_dec(v_unused_1931_);
v___x_1921_ = v_tail_1912_;
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_head_1919_);
lean_dec(v_tail_1912_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 7);
lean_ctor_set(v___x_1921_, 1, v___x_1923_);
lean_ctor_set(v___x_1921_, 0, v_head_1915_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_head_1915_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 7);
lean_ctor_set(v___x_1917_, 1, v_head_1919_);
lean_ctor_set(v___x_1917_, 0, v___x_1925_);
v___x_1927_ = v___x_1917_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_head_1919_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
else
{
lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1957_; 
v_isSharedCheck_1957_ = !lean_is_exclusive(v_tail_1912_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; lean_object* v_unused_1959_; 
v_unused_1958_ = lean_ctor_get(v_tail_1912_, 1);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_tail_1912_, 0);
lean_dec(v_unused_1959_);
v___x_1935_ = v_tail_1912_;
v_isShared_1936_ = v_isSharedCheck_1957_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v_tail_1912_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1957_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1937_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1910_);
v___x_1938_ = lean_array_mk(v_xs_1910_);
v___x_1939_ = lean_array_pop(v___x_1938_);
v___x_1940_ = lean_array_to_list(v___x_1939_);
v___x_1941_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1942_ = l_Lean_MessageData_joinSep(v___x_1940_, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1936_ == 0)
{
lean_ctor_set_tag(v___x_1935_, 7);
lean_ctor_set(v___x_1935_, 1, v___x_1943_);
lean_ctor_set(v___x_1935_, 0, v___x_1942_);
v___x_1945_ = v___x_1935_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v___x_1946_ = l_List_getLast_x21___redArg(v___x_1937_, v_xs_1910_);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_xs_1910_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; lean_object* v_unused_1955_; 
v_unused_1954_ = lean_ctor_get(v_xs_1910_, 1);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_xs_1910_, 0);
lean_dec(v_unused_1955_);
v___x_1948_ = v_xs_1910_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v_xs_1910_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 7);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
lean_ctor_set(v___x_1948_, 0, v___x_1945_);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
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
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1964_ = l_Lean_MessageData_ofFormat(v___x_1963_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1969_ = l_Lean_MessageData_ofFormat(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1970_){
_start:
{
if (lean_obj_tag(v_xs_1970_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1971_;
}
else
{
lean_object* v_tail_1972_; 
v_tail_1972_ = lean_ctor_get(v_xs_1970_, 1);
lean_inc(v_tail_1972_);
if (lean_obj_tag(v_tail_1972_) == 0)
{
lean_object* v_head_1973_; 
v_head_1973_ = lean_ctor_get(v_xs_1970_, 0);
lean_inc(v_head_1973_);
lean_dec_ref_known(v_xs_1970_, 2);
return v_head_1973_;
}
else
{
lean_object* v_tail_1974_; 
v_tail_1974_ = lean_ctor_get(v_tail_1972_, 1);
if (lean_obj_tag(v_tail_1974_) == 0)
{
lean_object* v_head_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1992_; 
v_head_1975_ = lean_ctor_get(v_xs_1970_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_xs_1970_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_xs_1970_, 1);
lean_dec(v_unused_1993_);
v___x_1977_ = v_xs_1970_;
v_isShared_1978_ = v_isSharedCheck_1992_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_head_1975_);
lean_dec(v_xs_1970_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1992_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_head_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1990_; 
v_head_1979_ = lean_ctor_get(v_tail_1972_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_tail_1972_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v_tail_1972_, 1);
lean_dec(v_unused_1991_);
v___x_1981_ = v_tail_1972_;
v_isShared_1982_ = v_isSharedCheck_1990_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_head_1979_);
lean_dec(v_tail_1972_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1990_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 7);
lean_ctor_set(v___x_1981_, 1, v___x_1983_);
lean_ctor_set(v___x_1981_, 0, v_head_1975_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_head_1975_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v_head_1979_);
lean_ctor_set(v___x_1977_, 0, v___x_1985_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_head_1979_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
else
{
lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2017_; 
v_isSharedCheck_2017_ = !lean_is_exclusive(v_tail_1972_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; 
v_unused_2018_ = lean_ctor_get(v_tail_1972_, 1);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_tail_1972_, 0);
lean_dec(v_unused_2019_);
v___x_1995_ = v_tail_1972_;
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
else
{
lean_dec(v_tail_1972_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_1997_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1970_);
v___x_1998_ = lean_array_mk(v_xs_1970_);
v___x_1999_ = lean_array_pop(v___x_1998_);
v___x_2000_ = lean_array_to_list(v___x_1999_);
v___x_2001_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_2002_ = l_Lean_MessageData_joinSep(v___x_2000_, v___x_2001_);
v___x_2003_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 7);
lean_ctor_set(v___x_1995_, 1, v___x_2003_);
lean_ctor_set(v___x_1995_, 0, v___x_2002_);
v___x_2005_ = v___x_1995_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v___x_2006_ = l_List_getLast_x21___redArg(v___x_1997_, v_xs_1970_);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_xs_1970_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; lean_object* v_unused_2015_; 
v_unused_2014_ = lean_ctor_get(v_xs_1970_, 1);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_xs_1970_, 0);
lean_dec(v_unused_2015_);
v___x_2008_ = v_xs_1970_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_xs_1970_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 7);
lean_ctor_set(v___x_2008_, 1, v___x_2006_);
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
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
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2026_ = l_Lean_MessageData_ofFormat(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2028_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v___x_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_note_2030_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2037_ = l_Lean_MessageData_ofFormat(v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2039_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v_hint_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2048_ = lean_box(0);
v___x_2049_ = l_List_mapTR_loop___redArg(v___x_2047_, v_es_2046_, v___x_2048_);
v___x_2050_ = l_Lean_MessageData_ofList(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2054_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2055_ = l_Lean_instInhabitedPosition_default;
v___x_2056_ = lean_box(0);
v___x_2057_ = 0;
v___x_2058_ = 2;
v___x_2059_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2059_, 0, v___x_2054_);
lean_ctor_set(v___x_2059_, 1, v___x_2055_);
lean_ctor_set(v___x_2059_, 2, v___x_2056_);
lean_ctor_set(v___x_2059_, 3, v___x_2054_);
lean_ctor_set(v___x_2059_, 4, v_inst_2053_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*5, v___x_2057_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*5 + 1, v___x_2058_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*5 + 2, v___x_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2060_, lean_object* v_inst_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2065_, lean_object* v_inst_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v_fileName_2082_; lean_object* v_pos_2083_; lean_object* v_endPos_2084_; uint8_t v_keepFullRange_2085_; uint8_t v_severity_2086_; uint8_t v_isSilent_2087_; lean_object* v_caption_2088_; lean_object* v_data_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_fileName_2082_ = lean_ctor_get(v_x_2081_, 0);
lean_inc_ref(v_fileName_2082_);
v_pos_2083_ = lean_ctor_get(v_x_2081_, 1);
lean_inc_ref(v_pos_2083_);
v_endPos_2084_ = lean_ctor_get(v_x_2081_, 2);
lean_inc(v_endPos_2084_);
v_keepFullRange_2085_ = lean_ctor_get_uint8(v_x_2081_, sizeof(void*)*5);
v_severity_2086_ = lean_ctor_get_uint8(v_x_2081_, sizeof(void*)*5 + 1);
v_isSilent_2087_ = lean_ctor_get_uint8(v_x_2081_, sizeof(void*)*5 + 2);
v_caption_2088_ = lean_ctor_get(v_x_2081_, 3);
lean_inc_ref(v_caption_2088_);
v_data_2089_ = lean_ctor_get(v_x_2081_, 4);
lean_inc(v_data_2089_);
lean_dec_ref(v_x_2081_);
v___x_2090_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2091_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_fileName_2082_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2097_ = l_Lean_instToJsonPosition_toJson(v_pos_2083_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2094_);
v___x_2100_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2101_ = l_Option_toJson___redArg(v___x_2090_, v_endPos_2084_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2094_);
v___x_2104_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2105_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2105_, 0, v_keepFullRange_2085_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2094_);
v___x_2108_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2109_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2086_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2094_);
v___x_2112_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2113_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2113_, 0, v_isSilent_2087_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2094_);
v___x_2116_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_caption_2088_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2094_);
v___x_2120_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2121_ = lean_apply_1(v_inst_2080_, v_data_2089_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2094_);
v___x_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2094_);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2119_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2115_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2111_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2107_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2103_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2099_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2095_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2133_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2134_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2132_, v___x_2131_, v___x_2133_);
v___x_2135_ = l_Lean_Json_mkObj(v___x_2134_);
lean_dec(v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2136_, lean_object* v_inst_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2137_, v_x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2141_, 0, lean_box(0));
lean_closure_set(v___x_2141_, 1, v_inst_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2142_, lean_object* v_inst_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2144_, 0, lean_box(0));
lean_closure_set(v___x_2144_, 1, v_inst_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = 1;
v___x_2151_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2155_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2156_ = lean_string_append(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = 1;
v___x_2160_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2163_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2164_ = lean_string_append(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2167_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2168_ = lean_string_append(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = 1;
v___x_2175_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2178_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2179_ = lean_string_append(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2181_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2182_ = lean_string_append(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = 1;
v___x_2186_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2189_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2190_ = lean_string_append(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2192_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2193_ = lean_string_append(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = 1;
v___x_2198_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2201_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2202_ = lean_string_append(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2204_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2205_ = lean_string_append(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = 1;
v___x_2209_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2212_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2213_ = lean_string_append(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2215_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2216_ = lean_string_append(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = 1;
v___x_2220_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2223_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2224_ = lean_string_append(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2226_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2227_ = lean_string_append(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = 1;
v___x_2231_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2234_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2235_ = lean_string_append(v___x_2234_, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2237_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2238_ = lean_string_append(v___x_2237_, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = 1;
v___x_2242_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2242_, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2245_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2246_ = lean_string_append(v___x_2245_, v___x_2244_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2248_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2249_ = lean_string_append(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2250_, lean_object* v_json_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2253_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2251_);
v___x_2254_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2252_, v___x_2253_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2264_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2264_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2260_ = lean_string_append(v___x_2259_, v_a_2255_);
lean_dec(v_a_2255_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2260_);
v___x_2262_ = v___x_2257_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
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
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2265_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2254_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2254_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2273_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2274_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2275_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2276_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2251_);
v___x_2277_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2274_, v___x_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2287_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2287_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2282_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2283_ = lean_string_append(v___x_2282_, v_a_2278_);
lean_dec(v_a_2278_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2283_);
v___x_2285_ = v___x_2280_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
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
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2288_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2277_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2277_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 0);
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_a_2296_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2297_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2251_);
v___x_2298_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2275_, v___x_2297_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2303_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2304_ = lean_string_append(v___x_2303_, v_a_2299_);
lean_dec(v_a_2299_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
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
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2309_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2298_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2298_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 0);
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2317_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2318_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2319_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2251_);
v___x_2320_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2318_, v___x_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2330_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2330_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2325_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2326_ = lean_string_append(v___x_2325_, v_a_2321_);
lean_dec(v_a_2321_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2326_);
v___x_2328_ = v___x_2323_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2331_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2320_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2320_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 0);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2339_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2340_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2341_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2251_);
v___x_2342_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2340_, v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2347_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2348_ = lean_string_append(v___x_2347_, v_a_2343_);
lean_dec(v_a_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
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
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2353_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2342_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2342_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 0);
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2361_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2362_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2251_);
v___x_2363_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2318_, v___x_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2369_ = lean_string_append(v___x_2368_, v_a_2364_);
lean_dec(v_a_2364_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
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
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2374_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2363_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2363_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 0);
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2382_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2383_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2251_);
v___x_2384_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v___x_2252_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2382_);
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2394_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2394_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2389_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2390_ = lean_string_append(v___x_2389_, v_a_2385_);
lean_dec(v_a_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2390_);
v___x_2392_ = v___x_2387_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
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
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_a_2382_);
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
lean_dec(v_json_2251_);
lean_dec_ref(v_inst_2250_);
v_a_2395_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2384_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2384_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 0);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2403_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2404_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2405_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2251_, v_inst_2250_, v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_a_2403_);
lean_dec(v_a_2382_);
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2410_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2411_ = lean_string_append(v___x_2410_, v_a_2406_);
lean_dec(v_a_2406_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
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
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_a_2403_);
lean_dec(v_a_2382_);
lean_dec(v_a_2361_);
lean_dec(v_a_2339_);
lean_dec(v_a_2317_);
lean_dec(v_a_2296_);
lean_dec(v_a_2273_);
v_a_2416_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2405_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2405_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 0);
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2435_; 
v_a_2424_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2426_ = v___x_2405_;
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2405_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; uint8_t v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2433_; 
v___x_2428_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2428_, 0, v_a_2273_);
lean_ctor_set(v___x_2428_, 1, v_a_2296_);
lean_ctor_set(v___x_2428_, 2, v_a_2317_);
lean_ctor_set(v___x_2428_, 3, v_a_2403_);
lean_ctor_set(v___x_2428_, 4, v_a_2424_);
v___x_2429_ = lean_unbox(v_a_2339_);
lean_dec(v_a_2339_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*5, v___x_2429_);
v___x_2430_ = lean_unbox(v_a_2361_);
lean_dec(v_a_2361_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*5 + 1, v___x_2430_);
v___x_2431_ = lean_unbox(v_a_2382_);
lean_dec(v_a_2382_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*5 + 2, v___x_2431_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2428_);
v___x_2433_ = v___x_2426_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2436_, lean_object* v_inst_2437_, lean_object* v_json_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2437_, v_json_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2441_, 0, lean_box(0));
lean_closure_set(v___x_2441_, 1, v_inst_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2442_, lean_object* v_inst_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2444_, 0, lean_box(0));
lean_closure_set(v___x_2444_, 1, v_inst_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_box(0);
return v___x_2446_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2448_; 
v_val_2447_ = lean_ctor_get(v_x_2445_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v_x_2445_, 1);
v___x_2448_ = l_Lean_instToJsonPosition_toJson(v_val_2447_);
return v___x_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
if (lean_obj_tag(v_a_2449_) == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_array_to_list(v_a_2450_);
return v___x_2451_;
}
else
{
lean_object* v_head_2452_; lean_object* v_tail_2453_; lean_object* v___x_2454_; 
v_head_2452_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_head_2452_);
v_tail_2453_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_tail_2453_);
lean_dec_ref_known(v_a_2449_, 2);
v___x_2454_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2450_, v_head_2452_);
v_a_2449_ = v_tail_2453_;
v_a_2450_ = v___x_2454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2457_){
_start:
{
lean_object* v_toBaseMessage_2458_; lean_object* v_kind_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2524_; 
v_toBaseMessage_2458_ = lean_ctor_get(v_x_2457_, 0);
v_kind_2459_ = lean_ctor_get(v_x_2457_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_x_2457_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2461_ = v_x_2457_;
v_isShared_2462_ = v_isSharedCheck_2524_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_kind_2459_);
lean_inc(v_toBaseMessage_2458_);
lean_dec(v_x_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2524_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_fileName_2463_; lean_object* v_pos_2464_; lean_object* v_endPos_2465_; uint8_t v_keepFullRange_2466_; uint8_t v_severity_2467_; uint8_t v_isSilent_2468_; lean_object* v_caption_2469_; lean_object* v_data_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v_fileName_2463_ = lean_ctor_get(v_toBaseMessage_2458_, 0);
lean_inc_ref(v_fileName_2463_);
v_pos_2464_ = lean_ctor_get(v_toBaseMessage_2458_, 1);
lean_inc_ref(v_pos_2464_);
v_endPos_2465_ = lean_ctor_get(v_toBaseMessage_2458_, 2);
lean_inc(v_endPos_2465_);
v_keepFullRange_2466_ = lean_ctor_get_uint8(v_toBaseMessage_2458_, sizeof(void*)*5);
v_severity_2467_ = lean_ctor_get_uint8(v_toBaseMessage_2458_, sizeof(void*)*5 + 1);
v_isSilent_2468_ = lean_ctor_get_uint8(v_toBaseMessage_2458_, sizeof(void*)*5 + 2);
v_caption_2469_ = lean_ctor_get(v_toBaseMessage_2458_, 3);
lean_inc_ref(v_caption_2469_);
v_data_2470_ = lean_ctor_get(v_toBaseMessage_2458_, 4);
lean_inc(v_data_2470_);
lean_dec_ref(v_toBaseMessage_2458_);
v___x_2471_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_fileName_2463_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v___x_2472_);
lean_ctor_set(v___x_2461_, 0, v___x_2471_);
v___x_2474_ = v___x_2461_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2478_ = l_Lean_instToJsonPosition_toJson(v_pos_2464_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2475_);
v___x_2481_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2482_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2465_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2475_);
v___x_2485_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2486_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2486_, 0, v_keepFullRange_2466_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2475_);
v___x_2489_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2490_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2467_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2475_);
v___x_2493_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2494_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2494_, 0, v_isSilent_2468_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v___x_2475_);
v___x_2497_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_caption_2469_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2475_);
v___x_2501_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_data_2470_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2475_);
v___x_2505_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2506_ = 1;
v___x_2507_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2459_, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2505_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2475_);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2475_);
v___x_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2504_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2500_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2496_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2492_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2488_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2484_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2480_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2476_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2521_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2519_, v___x_2520_);
v___x_2522_ = l_Lean_Json_mkObj(v___x_2521_);
lean_dec(v___x_2521_);
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2527_, lean_object* v_k_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = l_Lean_Json_getObjValD(v_j_2527_, v_k_2528_);
v___x_2530_ = l_Lean_Json_getStr_x3f(v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2531_, lean_object* v_k_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2531_, v_k_2532_);
lean_dec_ref(v_k_2532_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2534_, lean_object* v_k_2535_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = l_Lean_Json_getObjValD(v_j_2534_, v_k_2535_);
v___x_2537_ = l_Lean_instFromJsonPosition_fromJson(v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2538_, lean_object* v_k_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2538_, v_k_2539_);
lean_dec_ref(v_k_2539_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2541_, lean_object* v_k_2542_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = l_Lean_Json_getObjValD(v_j_2541_, v_k_2542_);
v___x_2544_ = l_Lean_Json_getBool_x3f(v___x_2543_);
lean_dec(v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2545_, lean_object* v_k_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2545_, v_k_2546_);
lean_dec_ref(v_k_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2548_, lean_object* v_k_2549_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = l_Lean_Json_getObjValD(v_j_2548_, v_k_2549_);
v___x_2551_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2552_, lean_object* v_k_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2552_, v_k_2553_);
lean_dec_ref(v_k_2553_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2555_, lean_object* v_k_2556_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = l_Lean_Json_getObjValD(v_j_2555_, v_k_2556_);
v___x_2558_ = l_Lean_Name_fromJson_x3f(v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2559_, lean_object* v_k_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2559_, v_k_2560_);
lean_dec_ref(v_k_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_instFromJsonPosition_fromJson(v_x_2564_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2583_; 
v_a_2575_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2577_ = v___x_2566_;
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2566_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2579_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2584_, lean_object* v_k_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Lean_Json_getObjValD(v_j_2584_, v_k_2585_);
v___x_2587_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2588_, lean_object* v_k_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2588_, v_k_2589_);
lean_dec_ref(v_k_2589_);
return v_res_2590_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = 1;
v___x_2596_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2597_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2596_, v___x_2595_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2599_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2600_ = lean_string_append(v___x_2599_, v___x_2598_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2602_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2603_ = lean_string_append(v___x_2602_, v___x_2601_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2605_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2606_ = lean_string_append(v___x_2605_, v___x_2604_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2608_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2609_ = lean_string_append(v___x_2608_, v___x_2607_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2611_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2612_ = lean_string_append(v___x_2611_, v___x_2610_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2614_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2615_ = lean_string_append(v___x_2614_, v___x_2613_);
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2617_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2618_ = lean_string_append(v___x_2617_, v___x_2616_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2620_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2621_ = lean_string_append(v___x_2620_, v___x_2619_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2623_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2624_ = lean_string_append(v___x_2623_, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2626_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2627_ = lean_string_append(v___x_2626_, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2629_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2630_ = lean_string_append(v___x_2629_, v___x_2628_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2632_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2633_ = lean_string_append(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2635_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2636_ = lean_string_append(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2639_ = lean_string_append(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2641_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2642_ = lean_string_append(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2644_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2645_ = lean_string_append(v___x_2644_, v___x_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2647_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2648_ = lean_string_append(v___x_2647_, v___x_2646_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = 1;
v___x_2652_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2652_, v___x_2651_);
return v___x_2653_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2655_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2656_ = lean_string_append(v___x_2655_, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2658_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2659_ = lean_string_append(v___x_2658_, v___x_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2660_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2660_);
v___x_2662_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2660_, v___x_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_json_2660_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2668_ = lean_string_append(v___x_2667_, v_a_2663_);
lean_dec(v_a_2663_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
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
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_json_2660_);
v_a_2673_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2662_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2662_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 0);
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2682_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2660_);
v___x_2683_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2660_, v___x_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2689_ = lean_string_append(v___x_2688_, v_a_2684_);
lean_dec(v_a_2684_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
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
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2694_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2683_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2683_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 0);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2702_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2703_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2660_);
v___x_2704_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2660_, v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2709_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2710_ = lean_string_append(v___x_2709_, v_a_2705_);
lean_dec(v_a_2705_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2710_);
v___x_2712_ = v___x_2707_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
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
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2715_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2704_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2704_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set_tag(v___x_2717_, 0);
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2724_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2660_);
v___x_2725_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2660_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2731_ = lean_string_append(v___x_2730_, v_a_2726_);
lean_dec(v_a_2726_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
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
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2736_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2725_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2725_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 0);
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_a_2744_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2745_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2660_);
v___x_2746_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2660_, v___x_2745_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2751_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2752_ = lean_string_append(v___x_2751_, v_a_2747_);
lean_dec(v_a_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2752_);
v___x_2754_ = v___x_2749_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
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
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2757_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2746_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2746_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 0);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2766_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2660_);
v___x_2767_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2660_, v___x_2766_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2773_ = lean_string_append(v___x_2772_, v_a_2768_);
lean_dec(v_a_2768_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
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
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2778_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2767_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2767_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 0);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2787_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2660_);
v___x_2788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2660_, v___x_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2794_ = lean_string_append(v___x_2793_, v_a_2789_);
lean_dec(v_a_2789_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
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
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2799_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2788_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2807_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2808_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2660_);
v___x_2809_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2660_, v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2807_);
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2819_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2819_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2814_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2815_ = lean_string_append(v___x_2814_, v_a_2810_);
lean_dec(v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2815_);
v___x_2817_ = v___x_2812_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
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
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v_a_2807_);
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
lean_dec(v_json_2660_);
v_a_2820_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2809_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2809_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 0);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2829_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2660_, v___x_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2807_);
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2836_ = lean_string_append(v___x_2835_, v_a_2831_);
lean_dec(v_a_2831_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2836_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
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
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2807_);
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_a_2723_);
lean_dec(v_a_2702_);
lean_dec(v_a_2681_);
v_a_2841_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2830_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2830_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 0);
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2861_; 
v_a_2849_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2851_ = v___x_2830_;
v_isShared_2852_ = v_isSharedCheck_2861_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2830_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2861_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; uint8_t v___x_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2853_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2853_, 0, v_a_2681_);
lean_ctor_set(v___x_2853_, 1, v_a_2702_);
lean_ctor_set(v___x_2853_, 2, v_a_2723_);
lean_ctor_set(v___x_2853_, 3, v_a_2807_);
lean_ctor_set(v___x_2853_, 4, v_a_2828_);
v___x_2854_ = lean_unbox(v_a_2744_);
lean_dec(v_a_2744_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*5, v___x_2854_);
v___x_2855_ = lean_unbox(v_a_2765_);
lean_dec(v_a_2765_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*5 + 1, v___x_2855_);
v___x_2856_ = lean_unbox(v_a_2786_);
lean_dec(v_a_2786_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*5 + 2, v___x_2856_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2853_);
lean_ctor_set(v___x_2857_, 1, v_a_2849_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2857_);
v___x_2859_ = v___x_2851_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2868_ = l_Lean_Name_str___override(v_errorName_2866_, v___x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2869_, lean_object* v_name_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = l_Lean_kindOfErrorName(v_name_2870_);
v___x_2872_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v_msg_2869_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2874_){
_start:
{
switch(lean_obj_tag(v_a_2874_))
{
case 0:
{
return v_a_2874_;
}
case 1:
{
lean_object* v_pre_2875_; lean_object* v_str_2876_; lean_object* v_p_x27_2877_; uint8_t v___y_2879_; uint8_t v___x_2882_; 
v_pre_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_pre_2875_);
v_str_2876_ = lean_ctor_get(v_a_2874_, 1);
lean_inc_ref(v_str_2876_);
lean_dec_ref_known(v_a_2874_, 2);
v_p_x27_2877_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2875_);
v___x_2882_ = l_Lean_Name_isAnonymous(v_p_x27_2877_);
if (v___x_2882_ == 0)
{
v___y_2879_ = v___x_2882_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2884_ = lean_string_dec_eq(v_str_2876_, v___x_2883_);
v___y_2879_ = v___x_2884_;
goto v___jp_2878_;
}
v___jp_2878_:
{
if (v___y_2879_ == 0)
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Name_str___override(v_p_x27_2877_, v_str_2876_);
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; 
lean_dec(v_p_x27_2877_);
lean_dec_ref(v_str_2876_);
v___x_2881_ = lean_box(0);
return v___x_2881_;
}
}
}
default: 
{
lean_object* v_pre_2885_; lean_object* v_i_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_pre_2885_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_pre_2885_);
v_i_2886_ = lean_ctor_get(v_a_2874_, 1);
lean_inc(v_i_2886_);
lean_dec_ref_known(v_a_2874_, 2);
v___x_2887_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2885_);
v___x_2888_ = l_Lean_Name_num___override(v___x_2887_, v_i_2886_);
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2889_){
_start:
{
switch(lean_obj_tag(v_x_2889_))
{
case 3:
{
lean_object* v_a_2890_; lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_a_2890_ = lean_ctor_get(v_x_2889_, 0);
v_a_2891_ = lean_ctor_get(v_x_2889_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v_x_2889_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_inc(v_a_2890_);
lean_dec(v_x_2889_);
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
v_reuseFailAlloc_2898_ = lean_alloc_ctor(3, 2, 0);
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
case 4:
{
lean_object* v_a_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_a_2900_ = lean_ctor_get(v_x_2889_, 0);
v_a_2901_ = lean_ctor_get(v_x_2889_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v_x_2889_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_inc(v_a_2900_);
lean_dec(v_x_2889_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_MessageData_stripNestedTags(v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2900_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
case 8:
{
lean_object* v_a_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_a_2910_ = lean_ctor_get(v_x_2889_, 0);
v_a_2911_ = lean_ctor_get(v_x_2889_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v_x_2889_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_inc(v_a_2910_);
lean_dec(v_x_2889_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_a_2911_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
case 11:
{
lean_object* v_a_2920_; lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2929_; 
v_a_2920_ = lean_ctor_get(v_x_2889_, 0);
v_a_2921_ = lean_ctor_get(v_x_2889_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2923_ = v_x_2889_;
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_inc(v_a_2920_);
lean_dec(v_x_2889_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = l_Lean_MessageData_stripNestedTags(v_a_2921_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2925_);
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2920_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
default: 
{
return v_x_2889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2930_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 1)
{
lean_object* v_pre_2931_; lean_object* v_str_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_pre_2931_ = lean_ctor_get(v_x_2930_, 0);
v_str_2932_ = lean_ctor_get(v_x_2930_, 1);
v___x_2933_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2934_ = lean_string_dec_eq(v_str_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_box(0);
return v___x_2935_;
}
else
{
lean_object* v___x_2936_; 
lean_inc(v_pre_2931_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_pre_2931_);
return v___x_2936_;
}
}
else
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_box(0);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_errorNameOfKind_x3f(v_x_2938_);
lean_dec(v_x_2938_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = l_Lean_MessageData_kind(v_msg_2940_);
v___x_2942_ = l_Lean_errorNameOfKind_x3f(v___x_2941_);
lean_dec(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_MessageData_errorName_x3f(v_msg_2943_);
lean_dec_ref(v_msg_2943_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2945_){
_start:
{
lean_object* v_data_2946_; lean_object* v___x_2947_; 
v_data_2946_ = lean_ctor_get(v_msg_2945_, 4);
v___x_2947_ = l_Lean_MessageData_errorName_x3f(v_data_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Message_errorName_x3f(v_msg_2948_);
lean_dec_ref(v_msg_2948_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2950_){
_start:
{
lean_object* v_toBaseMessage_2951_; lean_object* v_fileName_2952_; lean_object* v_pos_2953_; lean_object* v_endPos_2954_; uint8_t v_keepFullRange_2955_; uint8_t v_severity_2956_; uint8_t v_isSilent_2957_; lean_object* v_caption_2958_; lean_object* v_data_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2968_; 
v_toBaseMessage_2951_ = lean_ctor_get(v_msg_2950_, 0);
lean_inc_ref(v_toBaseMessage_2951_);
lean_dec_ref(v_msg_2950_);
v_fileName_2952_ = lean_ctor_get(v_toBaseMessage_2951_, 0);
v_pos_2953_ = lean_ctor_get(v_toBaseMessage_2951_, 1);
v_endPos_2954_ = lean_ctor_get(v_toBaseMessage_2951_, 2);
v_keepFullRange_2955_ = lean_ctor_get_uint8(v_toBaseMessage_2951_, sizeof(void*)*5);
v_severity_2956_ = lean_ctor_get_uint8(v_toBaseMessage_2951_, sizeof(void*)*5 + 1);
v_isSilent_2957_ = lean_ctor_get_uint8(v_toBaseMessage_2951_, sizeof(void*)*5 + 2);
v_caption_2958_ = lean_ctor_get(v_toBaseMessage_2951_, 3);
v_data_2959_ = lean_ctor_get(v_toBaseMessage_2951_, 4);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_toBaseMessage_2951_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2961_ = v_toBaseMessage_2951_;
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_data_2959_);
lean_inc(v_caption_2958_);
lean_inc(v_endPos_2954_);
lean_inc(v_pos_2953_);
lean_inc(v_fileName_2952_);
lean_dec(v_toBaseMessage_2951_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_data_2959_);
v___x_2964_ = l_Lean_MessageData_ofFormat(v___x_2963_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_fileName_2952_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_pos_2953_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_endPos_2954_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_caption_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v___x_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*5, v_keepFullRange_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*5 + 1, v_severity_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*5 + 2, v_isSilent_2957_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2974_, uint8_t v_includeEndPos_2975_){
_start:
{
lean_object* v___y_2977_; uint8_t v___y_2981_; lean_object* v___y_2982_; uint32_t v___y_2983_; lean_object* v_str_2987_; lean_object* v_toBaseMessage_2999_; lean_object* v_kind_3000_; lean_object* v_fileName_3001_; lean_object* v_pos_3002_; lean_object* v_endPos_3003_; uint8_t v_severity_3004_; lean_object* v_caption_3005_; lean_object* v_data_3006_; lean_object* v___y_3008_; lean_object* v_str_3009_; lean_object* v___y_3017_; 
v_toBaseMessage_2999_ = lean_ctor_get(v_msg_2974_, 0);
lean_inc_ref(v_toBaseMessage_2999_);
v_kind_3000_ = lean_ctor_get(v_msg_2974_, 1);
lean_inc(v_kind_3000_);
lean_dec_ref(v_msg_2974_);
v_fileName_3001_ = lean_ctor_get(v_toBaseMessage_2999_, 0);
lean_inc_ref(v_fileName_3001_);
v_pos_3002_ = lean_ctor_get(v_toBaseMessage_2999_, 1);
lean_inc_ref(v_pos_3002_);
v_endPos_3003_ = lean_ctor_get(v_toBaseMessage_2999_, 2);
lean_inc(v_endPos_3003_);
v_severity_3004_ = lean_ctor_get_uint8(v_toBaseMessage_2999_, sizeof(void*)*5 + 1);
v_caption_3005_ = lean_ctor_get(v_toBaseMessage_2999_, 3);
lean_inc_ref(v_caption_3005_);
v_data_3006_ = lean_ctor_get(v_toBaseMessage_2999_, 4);
lean_inc(v_data_3006_);
lean_dec_ref(v_toBaseMessage_2999_);
if (v_includeEndPos_2975_ == 0)
{
lean_object* v___x_3023_; 
lean_dec(v_endPos_3003_);
v___x_3023_ = lean_box(0);
v___y_3017_ = v___x_3023_;
goto v___jp_3016_;
}
else
{
v___y_3017_ = v_endPos_3003_;
goto v___jp_3016_;
}
v___jp_2976_:
{
lean_object* v___x_2978_; lean_object* v_str_2979_; 
v___x_2978_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2979_ = lean_string_append(v___y_2977_, v___x_2978_);
return v_str_2979_;
}
v___jp_2980_:
{
uint32_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = 10;
v___x_2985_ = lean_uint32_dec_eq(v___y_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
v___y_2977_ = v___y_2982_;
goto v___jp_2976_;
}
else
{
if (v___y_2981_ == 0)
{
return v___y_2982_;
}
else
{
v___y_2977_ = v___y_2982_;
goto v___jp_2976_;
}
}
}
v___jp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_string_utf8_byte_size(v_str_2987_);
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_nat_dec_eq(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc_ref(v_str_2987_);
v___x_2991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2991_, 0, v_str_2987_);
lean_ctor_set(v___x_2991_, 1, v___x_2989_);
lean_ctor_set(v___x_2991_, 2, v___x_2988_);
v___x_2992_ = l_String_Slice_Pos_prev_x3f(v___x_2991_, v___x_2988_);
if (lean_obj_tag(v___x_2992_) == 0)
{
uint32_t v___x_2993_; 
lean_dec_ref_known(v___x_2991_, 3);
v___x_2993_ = 65;
v___y_2981_ = v___x_2990_;
v___y_2982_ = v_str_2987_;
v___y_2983_ = v___x_2993_;
goto v___jp_2980_;
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2995_; 
v_val_2994_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_2994_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2995_ = l_String_Slice_Pos_get_x3f(v___x_2991_, v_val_2994_);
lean_dec(v_val_2994_);
lean_dec_ref_known(v___x_2991_, 3);
if (lean_obj_tag(v___x_2995_) == 0)
{
uint32_t v___x_2996_; 
v___x_2996_ = 65;
v___y_2981_ = v___x_2990_;
v___y_2982_ = v_str_2987_;
v___y_2983_ = v___x_2996_;
goto v___jp_2980_;
}
else
{
lean_object* v_val_2997_; uint32_t v___x_2998_; 
v_val_2997_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2997_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2998_ = lean_unbox_uint32(v_val_2997_);
lean_dec(v_val_2997_);
v___y_2981_ = v___x_2990_;
v___y_2982_ = v_str_2987_;
v___y_2983_ = v___x_2998_;
goto v___jp_2980_;
}
}
}
else
{
v___y_2977_ = v_str_2987_;
goto v___jp_2976_;
}
}
v___jp_3007_:
{
switch(v_severity_3004_)
{
case 0:
{
lean_dec(v___y_3008_);
lean_dec_ref(v_pos_3002_);
lean_dec_ref(v_fileName_3001_);
lean_dec(v_kind_3000_);
v_str_2987_ = v_str_3009_;
goto v___jp_2986_;
}
case 1:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v_str_3012_; 
v___x_3010_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3011_ = l_Lean_errorNameOfKind_x3f(v_kind_3000_);
lean_dec(v_kind_3000_);
v_str_3012_ = l_Lean_mkErrorStringWithPos(v_fileName_3001_, v_pos_3002_, v_str_3009_, v___y_3008_, v___x_3010_, v___x_3011_);
lean_dec_ref(v_str_3009_);
v_str_2987_ = v_str_3012_;
goto v___jp_2986_;
}
default: 
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v_str_3015_; 
v___x_3013_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3014_ = l_Lean_errorNameOfKind_x3f(v_kind_3000_);
lean_dec(v_kind_3000_);
v_str_3015_ = l_Lean_mkErrorStringWithPos(v_fileName_3001_, v_pos_3002_, v_str_3009_, v___y_3008_, v___x_3013_, v___x_3014_);
lean_dec_ref(v_str_3009_);
v_str_2987_ = v_str_3015_;
goto v___jp_2986_;
}
}
}
v___jp_3016_:
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3019_ = lean_string_dec_eq(v_caption_3005_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_str_3022_; 
v___x_3020_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3021_ = lean_string_append(v_caption_3005_, v___x_3020_);
v_str_3022_ = lean_string_append(v___x_3021_, v_data_3006_);
lean_dec(v_data_3006_);
v___y_3008_ = v___y_3017_;
v_str_3009_ = v_str_3022_;
goto v___jp_3007_;
}
else
{
lean_dec_ref(v_caption_3005_);
v___y_3008_ = v___y_3017_;
v_str_3009_ = v_data_3006_;
goto v___jp_3007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3024_, lean_object* v_includeEndPos_3025_){
_start:
{
uint8_t v_includeEndPos_boxed_3026_; lean_object* v_res_3027_; 
v_includeEndPos_boxed_3026_ = lean_unbox(v_includeEndPos_3025_);
v_res_3027_ = l_Lean_SerialMessage_toString(v_msg_3024_, v_includeEndPos_boxed_3026_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3028_){
_start:
{
uint8_t v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = 0;
v___x_3030_ = l_Lean_SerialMessage_toString(v_msg_3028_, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3033_){
_start:
{
lean_object* v_data_3034_; lean_object* v___x_3035_; 
v_data_3034_ = lean_ctor_get(v_msg_3033_, 4);
v___x_3035_ = l_Lean_MessageData_kind(v_data_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Message_kind(v_msg_3036_);
lean_dec_ref(v_msg_3036_);
return v_res_3037_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3038_){
_start:
{
lean_object* v_data_3039_; uint8_t v___x_3040_; 
v_data_3039_ = lean_ctor_get(v_msg_3038_, 4);
v___x_3040_ = l_Lean_MessageData_isTrace(v_data_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3041_){
_start:
{
uint8_t v_res_3042_; lean_object* v_r_3043_; 
v_res_3042_ = l_Lean_Message_isTrace(v_msg_3041_);
lean_dec_ref(v_msg_3041_);
v_r_3043_ = lean_box(v_res_3042_);
return v_r_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3044_){
_start:
{
lean_object* v_fileName_3046_; lean_object* v_pos_3047_; lean_object* v_endPos_3048_; uint8_t v_keepFullRange_3049_; uint8_t v_severity_3050_; uint8_t v_isSilent_3051_; lean_object* v_caption_3052_; lean_object* v_data_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3063_; 
v_fileName_3046_ = lean_ctor_get(v_msg_3044_, 0);
v_pos_3047_ = lean_ctor_get(v_msg_3044_, 1);
v_endPos_3048_ = lean_ctor_get(v_msg_3044_, 2);
v_keepFullRange_3049_ = lean_ctor_get_uint8(v_msg_3044_, sizeof(void*)*5);
v_severity_3050_ = lean_ctor_get_uint8(v_msg_3044_, sizeof(void*)*5 + 1);
v_isSilent_3051_ = lean_ctor_get_uint8(v_msg_3044_, sizeof(void*)*5 + 2);
v_caption_3052_ = lean_ctor_get(v_msg_3044_, 3);
v_data_3053_ = lean_ctor_get(v_msg_3044_, 4);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_msg_3044_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3055_ = v_msg_3044_;
v_isShared_3056_ = v_isSharedCheck_3063_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_data_3053_);
lean_inc(v_caption_3052_);
lean_inc(v_endPos_3048_);
lean_inc(v_pos_3047_);
lean_inc(v_fileName_3046_);
lean_dec(v_msg_3044_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3063_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3059_; 
lean_inc(v_data_3053_);
v___x_3057_ = l_Lean_MessageData_toString(v_data_3053_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 4, v___x_3057_);
v___x_3059_ = v___x_3055_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_fileName_3046_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_pos_3047_);
lean_ctor_set(v_reuseFailAlloc_3062_, 2, v_endPos_3048_);
lean_ctor_set(v_reuseFailAlloc_3062_, 3, v_caption_3052_);
lean_ctor_set(v_reuseFailAlloc_3062_, 4, v___x_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, sizeof(void*)*5, v_keepFullRange_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, sizeof(void*)*5 + 1, v_severity_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, sizeof(void*)*5 + 2, v_isSilent_3051_);
v___x_3059_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = l_Lean_MessageData_kind(v_data_3053_);
lean_dec(v_data_3053_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
return v___x_3061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Message_serialize(v_msg_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3067_, uint8_t v_includeEndPos_3068_){
_start:
{
lean_object* v_fileName_3070_; lean_object* v_pos_3071_; lean_object* v_endPos_3072_; uint8_t v_severity_3073_; lean_object* v_caption_3074_; lean_object* v_data_3075_; lean_object* v___x_3076_; lean_object* v___y_3078_; lean_object* v___y_3082_; uint8_t v___y_3083_; uint32_t v___y_3084_; lean_object* v_str_3088_; lean_object* v___x_3100_; lean_object* v___y_3102_; lean_object* v_str_3103_; lean_object* v___y_3111_; 
v_fileName_3070_ = lean_ctor_get(v_msg_3067_, 0);
lean_inc_ref(v_fileName_3070_);
v_pos_3071_ = lean_ctor_get(v_msg_3067_, 1);
lean_inc_ref(v_pos_3071_);
v_endPos_3072_ = lean_ctor_get(v_msg_3067_, 2);
lean_inc(v_endPos_3072_);
v_severity_3073_ = lean_ctor_get_uint8(v_msg_3067_, sizeof(void*)*5 + 1);
v_caption_3074_ = lean_ctor_get(v_msg_3067_, 3);
lean_inc_ref(v_caption_3074_);
v_data_3075_ = lean_ctor_get(v_msg_3067_, 4);
lean_inc_n(v_data_3075_, 2);
lean_dec_ref(v_msg_3067_);
v___x_3076_ = l_Lean_MessageData_toString(v_data_3075_);
v___x_3100_ = l_Lean_MessageData_kind(v_data_3075_);
lean_dec(v_data_3075_);
if (v_includeEndPos_3068_ == 0)
{
lean_object* v___x_3117_; 
lean_dec(v_endPos_3072_);
v___x_3117_ = lean_box(0);
v___y_3111_ = v___x_3117_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v_endPos_3072_;
goto v___jp_3110_;
}
v___jp_3077_:
{
lean_object* v___x_3079_; lean_object* v_str_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3080_ = lean_string_append(v___y_3078_, v___x_3079_);
return v_str_3080_;
}
v___jp_3081_:
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 10;
v___x_3086_ = lean_uint32_dec_eq(v___y_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
v___y_3078_ = v___y_3082_;
goto v___jp_3077_;
}
else
{
if (v___y_3083_ == 0)
{
return v___y_3082_;
}
else
{
v___y_3078_ = v___y_3082_;
goto v___jp_3077_;
}
}
}
v___jp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3089_ = lean_string_utf8_byte_size(v_str_3088_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_nat_dec_eq(v___x_3089_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_inc_ref(v_str_3088_);
v___x_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3092_, 0, v_str_3088_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
v___x_3093_ = l_String_Slice_Pos_prev_x3f(v___x_3092_, v___x_3089_);
if (lean_obj_tag(v___x_3093_) == 0)
{
uint32_t v___x_3094_; 
lean_dec_ref_known(v___x_3092_, 3);
v___x_3094_ = 65;
v___y_3082_ = v_str_3088_;
v___y_3083_ = v___x_3091_;
v___y_3084_ = v___x_3094_;
goto v___jp_3081_;
}
else
{
lean_object* v_val_3095_; lean_object* v___x_3096_; 
v_val_3095_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3095_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3096_ = l_String_Slice_Pos_get_x3f(v___x_3092_, v_val_3095_);
lean_dec(v_val_3095_);
lean_dec_ref_known(v___x_3092_, 3);
if (lean_obj_tag(v___x_3096_) == 0)
{
uint32_t v___x_3097_; 
v___x_3097_ = 65;
v___y_3082_ = v_str_3088_;
v___y_3083_ = v___x_3091_;
v___y_3084_ = v___x_3097_;
goto v___jp_3081_;
}
else
{
lean_object* v_val_3098_; uint32_t v___x_3099_; 
v_val_3098_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3098_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3099_ = lean_unbox_uint32(v_val_3098_);
lean_dec(v_val_3098_);
v___y_3082_ = v_str_3088_;
v___y_3083_ = v___x_3091_;
v___y_3084_ = v___x_3099_;
goto v___jp_3081_;
}
}
}
else
{
v___y_3078_ = v_str_3088_;
goto v___jp_3077_;
}
}
v___jp_3101_:
{
switch(v_severity_3073_)
{
case 0:
{
lean_dec(v___y_3102_);
lean_dec(v___x_3100_);
lean_dec_ref(v_pos_3071_);
lean_dec_ref(v_fileName_3070_);
v_str_3088_ = v_str_3103_;
goto v___jp_3087_;
}
case 1:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_str_3106_; 
v___x_3104_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3105_ = l_Lean_errorNameOfKind_x3f(v___x_3100_);
lean_dec(v___x_3100_);
v_str_3106_ = l_Lean_mkErrorStringWithPos(v_fileName_3070_, v_pos_3071_, v_str_3103_, v___y_3102_, v___x_3104_, v___x_3105_);
lean_dec_ref(v_str_3103_);
v_str_3088_ = v_str_3106_;
goto v___jp_3087_;
}
default: 
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_str_3109_; 
v___x_3107_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3108_ = l_Lean_errorNameOfKind_x3f(v___x_3100_);
lean_dec(v___x_3100_);
v_str_3109_ = l_Lean_mkErrorStringWithPos(v_fileName_3070_, v_pos_3071_, v_str_3103_, v___y_3102_, v___x_3107_, v___x_3108_);
lean_dec_ref(v_str_3103_);
v_str_3088_ = v_str_3109_;
goto v___jp_3087_;
}
}
}
v___jp_3110_:
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3113_ = lean_string_dec_eq(v_caption_3074_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_str_3116_; 
v___x_3114_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3115_ = lean_string_append(v_caption_3074_, v___x_3114_);
v_str_3116_ = lean_string_append(v___x_3115_, v___x_3076_);
lean_dec_ref(v___x_3076_);
v___y_3102_ = v___y_3111_;
v_str_3103_ = v_str_3116_;
goto v___jp_3101_;
}
else
{
lean_dec_ref(v_caption_3074_);
v___y_3102_ = v___y_3111_;
v_str_3103_ = v___x_3076_;
goto v___jp_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3118_, lean_object* v_includeEndPos_3119_, lean_object* v_a_3120_){
_start:
{
uint8_t v_includeEndPos_boxed_3121_; lean_object* v_res_3122_; 
v_includeEndPos_boxed_3121_ = lean_unbox(v_includeEndPos_3119_);
v_res_3122_ = l_Lean_Message_toString(v_msg_3118_, v_includeEndPos_boxed_3121_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_3123_){
_start:
{
lean_object* v_fileName_3125_; lean_object* v_pos_3126_; lean_object* v_endPos_3127_; uint8_t v_keepFullRange_3128_; uint8_t v_severity_3129_; uint8_t v_isSilent_3130_; lean_object* v_caption_3131_; lean_object* v_data_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_fileName_3125_ = lean_ctor_get(v_msg_3123_, 0);
lean_inc_ref(v_fileName_3125_);
v_pos_3126_ = lean_ctor_get(v_msg_3123_, 1);
lean_inc_ref(v_pos_3126_);
v_endPos_3127_ = lean_ctor_get(v_msg_3123_, 2);
lean_inc(v_endPos_3127_);
v_keepFullRange_3128_ = lean_ctor_get_uint8(v_msg_3123_, sizeof(void*)*5);
v_severity_3129_ = lean_ctor_get_uint8(v_msg_3123_, sizeof(void*)*5 + 1);
v_isSilent_3130_ = lean_ctor_get_uint8(v_msg_3123_, sizeof(void*)*5 + 2);
v_caption_3131_ = lean_ctor_get(v_msg_3123_, 3);
lean_inc_ref(v_caption_3131_);
v_data_3132_ = lean_ctor_get(v_msg_3123_, 4);
lean_inc_n(v_data_3132_, 2);
lean_dec_ref(v_msg_3123_);
v___x_3133_ = l_Lean_MessageData_toString(v_data_3132_);
v___x_3134_ = l_Lean_MessageData_kind(v_data_3132_);
lean_dec(v_data_3132_);
v___x_3135_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_fileName_3125_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = lean_box(0);
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3137_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3141_ = l_Lean_instToJsonPosition_toJson(v_pos_3126_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v___x_3138_);
v___x_3144_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3145_ = l_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3127_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3138_);
v___x_3148_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3149_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3149_, 0, v_keepFullRange_3128_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3138_);
v___x_3152_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3153_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3129_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v___x_3138_);
v___x_3156_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3157_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3157_, 0, v_isSilent_3130_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___x_3138_);
v___x_3160_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_caption_3131_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v___x_3138_);
v___x_3164_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3133_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___x_3138_);
v___x_3168_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3169_ = 1;
v___x_3170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3134_, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3168_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3138_);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3138_);
v___x_3175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3167_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3163_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3159_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3155_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3151_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3147_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3143_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3139_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3184_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3182_, v___x_3183_);
v___x_3185_ = l_Lean_Json_mkObj(v___x_3184_);
lean_dec(v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Message_toJson(v_msg_3186_);
return v_res_3188_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unsigned_to_nat(32u);
v___x_3190_ = lean_mk_empty_array_with_capacity(v___x_3189_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3192_ = ((size_t)5ULL);
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = lean_unsigned_to_nat(32u);
v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
v___x_3196_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3197_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
lean_ctor_set(v___x_3197_, 2, v___x_3193_);
lean_ctor_set(v___x_3197_, 3, v___x_3193_);
lean_ctor_set_usize(v___x_3197_, 4, v___x_3192_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_NameSet_empty;
v___x_3199_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
lean_ctor_set(v___x_3200_, 2, v___x_3198_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = lean_unsigned_to_nat(32u);
v___x_3204_ = lean_mk_empty_array_with_capacity(v___x_3203_);
lean_dec_ref(v___x_3204_);
v___x_3205_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3206_){
_start:
{
lean_object* v_unreported_3207_; 
v_unreported_3207_ = lean_ctor_get(v_self_3206_, 1);
lean_inc_ref(v_unreported_3207_);
return v_unreported_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_MessageLog_msgs(v_self_3208_);
lean_dec_ref(v_self_3208_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3210_){
_start:
{
lean_object* v_reported_3211_; lean_object* v_unreported_3212_; lean_object* v___x_3213_; 
v_reported_3211_ = lean_ctor_get(v_x_3210_, 0);
lean_inc_ref(v_reported_3211_);
v_unreported_3212_ = lean_ctor_get(v_x_3210_, 1);
lean_inc_ref(v_unreported_3212_);
lean_dec_ref(v_x_3210_);
v___x_3213_ = l_Lean_PersistentArray_append___redArg(v_reported_3211_, v_unreported_3212_);
lean_dec_ref(v_unreported_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3214_){
_start:
{
lean_object* v_unreported_3215_; uint8_t v___x_3216_; 
v_unreported_3215_ = lean_ctor_get(v_log_3214_, 1);
v___x_3216_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3215_);
if (v___x_3216_ == 0)
{
uint8_t v___x_3217_; 
v___x_3217_ = 1;
return v___x_3217_;
}
else
{
uint8_t v___x_3218_; 
v___x_3218_ = 0;
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3219_){
_start:
{
uint8_t v_res_3220_; lean_object* v_r_3221_; 
v_res_3220_ = l_Lean_MessageLog_hasUnreported(v_log_3219_);
lean_dec_ref(v_log_3219_);
v_r_3221_ = lean_box(v_res_3220_);
return v_r_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3222_, lean_object* v_log_3223_){
_start:
{
lean_object* v_reported_3224_; lean_object* v_unreported_3225_; lean_object* v_loggedKinds_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3234_; 
v_reported_3224_ = lean_ctor_get(v_log_3223_, 0);
v_unreported_3225_ = lean_ctor_get(v_log_3223_, 1);
v_loggedKinds_3226_ = lean_ctor_get(v_log_3223_, 2);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_log_3223_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3228_ = v_log_3223_;
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_loggedKinds_3226_);
lean_inc(v_unreported_3225_);
lean_inc(v_reported_3224_);
lean_dec(v_log_3223_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_PersistentArray_push___redArg(v_unreported_3225_, v_msg_3222_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___x_3230_);
v___x_3232_ = v___x_3228_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_reported_3224_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_loggedKinds_3226_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3237_, lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_b_u2082_3237_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; 
v___x_3240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3241_, v_x_3242_);
lean_dec(v_x_3242_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3244_, lean_object* v_k_3245_, lean_object* v_t_3246_){
_start:
{
if (lean_obj_tag(v_t_3246_) == 0)
{
lean_object* v_size_3247_; lean_object* v_k_3248_; lean_object* v_v_3249_; lean_object* v_l_3250_; lean_object* v_r_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3266_; 
v_size_3247_ = lean_ctor_get(v_t_3246_, 0);
v_k_3248_ = lean_ctor_get(v_t_3246_, 1);
v_v_3249_ = lean_ctor_get(v_t_3246_, 2);
v_l_3250_ = lean_ctor_get(v_t_3246_, 3);
v_r_3251_ = lean_ctor_get(v_t_3246_, 4);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_t_3246_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3253_ = v_t_3246_;
v_isShared_3254_ = v_isSharedCheck_3266_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_r_3251_);
lean_inc(v_l_3250_);
lean_inc(v_v_3249_);
lean_inc(v_k_3248_);
lean_inc(v_size_3247_);
lean_dec(v_t_3246_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3266_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
uint8_t v___x_3255_; 
v___x_3255_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3245_, v_k_3248_);
switch(v___x_3255_)
{
case 0:
{
lean_object* v_impl_3256_; lean_object* v___x_3257_; 
lean_del_object(v___x_3253_);
lean_dec(v_size_3247_);
v_impl_3256_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3244_, v_k_3245_, v_l_3250_);
v___x_3257_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3248_, v_v_3249_, v_impl_3256_, v_r_3251_);
return v___x_3257_;
}
case 1:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v_val_3260_; lean_object* v___x_3262_; 
lean_dec(v_k_3248_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_v_3249_);
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3244_, v___x_3258_);
lean_dec_ref_known(v___x_3258_, 1);
v_val_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3260_);
lean_dec(v___x_3259_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 2, v_val_3260_);
lean_ctor_set(v___x_3253_, 1, v_k_3245_);
v___x_3262_ = v___x_3253_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_size_3247_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_val_3260_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_l_3250_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_r_3251_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
default: 
{
lean_object* v_impl_3264_; lean_object* v___x_3265_; 
lean_del_object(v___x_3253_);
lean_dec(v_size_3247_);
v_impl_3264_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3244_, v_k_3245_, v_r_3251_);
v___x_3265_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3248_, v_v_3249_, v_l_3250_, v_impl_3264_);
return v___x_3265_;
}
}
}
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_val_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3267_ = lean_box(0);
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3244_, v___x_3267_);
v_val_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_val_3269_);
lean_dec(v___x_3268_);
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v_k_3245_);
lean_ctor_set(v___x_3271_, 2, v_val_3269_);
lean_ctor_set(v___x_3271_, 3, v_t_3246_);
lean_ctor_set(v___x_3271_, 4, v_t_3246_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3272_, lean_object* v_x_3273_){
_start:
{
if (lean_obj_tag(v_x_3273_) == 0)
{
lean_object* v_k_3274_; lean_object* v_v_3275_; lean_object* v_l_3276_; lean_object* v_r_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_k_3274_ = lean_ctor_get(v_x_3273_, 1);
lean_inc(v_k_3274_);
v_v_3275_ = lean_ctor_get(v_x_3273_, 2);
lean_inc(v_v_3275_);
v_l_3276_ = lean_ctor_get(v_x_3273_, 3);
lean_inc(v_l_3276_);
v_r_3277_ = lean_ctor_get(v_x_3273_, 4);
lean_inc(v_r_3277_);
lean_dec_ref_known(v_x_3273_, 5);
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3272_, v_l_3276_);
v___x_3279_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3275_, v_k_3274_, v___x_3278_);
v_init_3272_ = v___x_3279_;
v_x_3273_ = v_r_3277_;
goto _start;
}
else
{
return v_init_3272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3281_, lean_object* v_l_u2082_3282_){
_start:
{
lean_object* v_reported_3283_; lean_object* v_unreported_3284_; lean_object* v_loggedKinds_3285_; lean_object* v_reported_3286_; lean_object* v_unreported_3287_; lean_object* v_loggedKinds_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3298_; 
v_reported_3283_ = lean_ctor_get(v_l_u2081_3281_, 0);
lean_inc_ref(v_reported_3283_);
v_unreported_3284_ = lean_ctor_get(v_l_u2081_3281_, 1);
lean_inc_ref(v_unreported_3284_);
v_loggedKinds_3285_ = lean_ctor_get(v_l_u2081_3281_, 2);
lean_inc(v_loggedKinds_3285_);
lean_dec_ref(v_l_u2081_3281_);
v_reported_3286_ = lean_ctor_get(v_l_u2082_3282_, 0);
v_unreported_3287_ = lean_ctor_get(v_l_u2082_3282_, 1);
v_loggedKinds_3288_ = lean_ctor_get(v_l_u2082_3282_, 2);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_l_u2082_3282_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3290_ = v_l_u2082_3282_;
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_loggedKinds_3288_);
lean_inc(v_unreported_3287_);
lean_inc(v_reported_3286_);
lean_dec(v_l_u2082_3282_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3292_ = l_Lean_PersistentArray_append___redArg(v_reported_3283_, v_reported_3286_);
lean_dec_ref(v_reported_3286_);
v___x_3293_ = l_Lean_PersistentArray_append___redArg(v_unreported_3284_, v_unreported_3287_);
lean_dec_ref(v_unreported_3287_);
v___x_3294_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3285_, v_loggedKinds_3288_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 2, v___x_3294_);
lean_ctor_set(v___x_3290_, 1, v___x_3293_);
lean_ctor_set(v___x_3290_, 0, v___x_3292_);
v___x_3296_ = v___x_3290_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3292_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3299_, lean_object* v_k_3300_, lean_object* v_t_3301_, lean_object* v_hl_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3299_, v_k_3300_, v_t_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3304_, lean_object* v_t_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3304_, v_t_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3309_, size_t v_i_3310_, size_t v_stop_3311_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = lean_usize_dec_eq(v_i_3310_, v_stop_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; uint8_t v_severity_3314_; uint8_t v___x_3315_; 
v___x_3313_ = lean_array_uget_borrowed(v_as_3309_, v_i_3310_);
v_severity_3314_ = lean_ctor_get_uint8(v___x_3313_, sizeof(void*)*5 + 1);
v___x_3315_ = 1;
if (v_severity_3314_ == 2)
{
return v___x_3315_;
}
else
{
if (v___x_3312_ == 0)
{
size_t v___x_3316_; size_t v___x_3317_; 
v___x_3316_ = ((size_t)1ULL);
v___x_3317_ = lean_usize_add(v_i_3310_, v___x_3316_);
v_i_3310_ = v___x_3317_;
goto _start;
}
else
{
return v___x_3315_;
}
}
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = 0;
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3320_, lean_object* v_i_3321_, lean_object* v_stop_3322_){
_start:
{
size_t v_i_boxed_3323_; size_t v_stop_boxed_3324_; uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_i_boxed_3323_ = lean_unbox_usize(v_i_3321_);
lean_dec(v_i_3321_);
v_stop_boxed_3324_ = lean_unbox_usize(v_stop_3322_);
lean_dec(v_stop_3322_);
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3320_, v_i_boxed_3323_, v_stop_boxed_3324_);
lean_dec_ref(v_as_3320_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
lean_object* v_cs_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v_cs_3328_ = lean_ctor_get(v_x_3327_, 0);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_array_get_size(v_cs_3328_);
v___x_3331_ = lean_nat_dec_lt(v___x_3329_, v___x_3330_);
if (v___x_3331_ == 0)
{
return v___x_3331_;
}
else
{
if (v___x_3331_ == 0)
{
return v___x_3331_;
}
else
{
size_t v___x_3332_; size_t v___x_3333_; uint8_t v___x_3334_; 
v___x_3332_ = ((size_t)0ULL);
v___x_3333_ = lean_usize_of_nat(v___x_3330_);
v___x_3334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3328_, v___x_3332_, v___x_3333_);
return v___x_3334_;
}
}
}
else
{
lean_object* v_vs_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_vs_3335_ = lean_ctor_get(v_x_3327_, 0);
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = lean_array_get_size(v_vs_3335_);
v___x_3338_ = lean_nat_dec_lt(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
return v___x_3338_;
}
else
{
if (v___x_3338_ == 0)
{
return v___x_3338_;
}
else
{
size_t v___x_3339_; size_t v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = ((size_t)0ULL);
v___x_3340_ = lean_usize_of_nat(v___x_3337_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3335_, v___x_3339_, v___x_3340_);
return v___x_3341_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3342_, size_t v_i_3343_, size_t v_stop_3344_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_usize_dec_eq(v_i_3343_, v_stop_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = lean_array_uget_borrowed(v_as_3342_, v_i_3343_);
v___x_3347_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3346_);
if (v___x_3347_ == 0)
{
size_t v___x_3348_; size_t v___x_3349_; 
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_add(v_i_3343_, v___x_3348_);
v_i_3343_ = v___x_3349_;
goto _start;
}
else
{
return v___x_3347_;
}
}
else
{
uint8_t v___x_3351_; 
v___x_3351_ = 0;
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3352_, lean_object* v_i_3353_, lean_object* v_stop_3354_){
_start:
{
size_t v_i_boxed_3355_; size_t v_stop_boxed_3356_; uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_i_boxed_3355_ = lean_unbox_usize(v_i_3353_);
lean_dec(v_i_3353_);
v_stop_boxed_3356_ = lean_unbox_usize(v_stop_3354_);
lean_dec(v_stop_3354_);
v_res_3357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3352_, v_i_boxed_3355_, v_stop_boxed_3356_);
lean_dec_ref(v_as_3352_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3359_){
_start:
{
uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_res_3360_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3359_);
lean_dec_ref(v_x_3359_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3362_){
_start:
{
lean_object* v_root_3363_; lean_object* v_tail_3364_; uint8_t v___x_3365_; 
v_root_3363_ = lean_ctor_get(v_t_3362_, 0);
v_tail_3364_ = lean_ctor_get(v_t_3362_, 1);
v___x_3365_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3363_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = lean_array_get_size(v_tail_3364_);
v___x_3368_ = lean_nat_dec_lt(v___x_3366_, v___x_3367_);
if (v___x_3368_ == 0)
{
return v___x_3365_;
}
else
{
if (v___x_3368_ == 0)
{
return v___x_3365_;
}
else
{
size_t v___x_3369_; size_t v___x_3370_; uint8_t v___x_3371_; 
v___x_3369_ = ((size_t)0ULL);
v___x_3370_ = lean_usize_of_nat(v___x_3367_);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3364_, v___x_3369_, v___x_3370_);
return v___x_3371_;
}
}
}
else
{
return v___x_3365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3372_){
_start:
{
uint8_t v_res_3373_; lean_object* v_r_3374_; 
v_res_3373_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3372_);
lean_dec_ref(v_t_3372_);
v_r_3374_ = lean_box(v_res_3373_);
return v_r_3374_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3375_, lean_object* v_as_3376_, size_t v_i_3377_, size_t v_stop_3378_){
_start:
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_usize_dec_eq(v_i_3377_, v_stop_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; uint8_t v_severity_3381_; uint8_t v___x_3382_; 
v___x_3380_ = lean_array_uget_borrowed(v_as_3376_, v_i_3377_);
v_severity_3381_ = lean_ctor_get_uint8(v___x_3380_, sizeof(void*)*5 + 1);
v___x_3382_ = 1;
if (v_severity_3381_ == 2)
{
return v___x_3382_;
}
else
{
if (v___x_3375_ == 0)
{
size_t v___x_3383_; size_t v___x_3384_; 
v___x_3383_ = ((size_t)1ULL);
v___x_3384_ = lean_usize_add(v_i_3377_, v___x_3383_);
v_i_3377_ = v___x_3384_;
goto _start;
}
else
{
return v___x_3382_;
}
}
}
else
{
uint8_t v___x_3386_; 
v___x_3386_ = 0;
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3387_, lean_object* v_as_3388_, lean_object* v_i_3389_, lean_object* v_stop_3390_){
_start:
{
uint8_t v___x_1884__boxed_3391_; size_t v_i_boxed_3392_; size_t v_stop_boxed_3393_; uint8_t v_res_3394_; lean_object* v_r_3395_; 
v___x_1884__boxed_3391_ = lean_unbox(v___x_3387_);
v_i_boxed_3392_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_stop_boxed_3393_ = lean_unbox_usize(v_stop_3390_);
lean_dec(v_stop_3390_);
v_res_3394_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1884__boxed_3391_, v_as_3388_, v_i_boxed_3392_, v_stop_boxed_3393_);
lean_dec_ref(v_as_3388_);
v_r_3395_ = lean_box(v_res_3394_);
return v_r_3395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3396_, lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_object* v_cs_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_cs_3398_ = lean_ctor_get(v_x_3397_, 0);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = lean_array_get_size(v_cs_3398_);
v___x_3401_ = lean_nat_dec_lt(v___x_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
return v___x_3401_;
}
else
{
if (v___x_3401_ == 0)
{
return v___x_3401_;
}
else
{
size_t v___x_3402_; size_t v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = ((size_t)0ULL);
v___x_3403_ = lean_usize_of_nat(v___x_3400_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3396_, v_cs_3398_, v___x_3402_, v___x_3403_);
return v___x_3404_;
}
}
}
else
{
lean_object* v_vs_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_vs_3405_ = lean_ctor_get(v_x_3397_, 0);
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = lean_array_get_size(v_vs_3405_);
v___x_3408_ = lean_nat_dec_lt(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
return v___x_3408_;
}
else
{
if (v___x_3408_ == 0)
{
return v___x_3408_;
}
else
{
size_t v___x_3409_; size_t v___x_3410_; uint8_t v___x_3411_; 
v___x_3409_ = ((size_t)0ULL);
v___x_3410_ = lean_usize_of_nat(v___x_3407_);
v___x_3411_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3396_, v_vs_3405_, v___x_3409_, v___x_3410_);
return v___x_3411_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3412_, lean_object* v_as_3413_, size_t v_i_3414_, size_t v_stop_3415_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_eq(v_i_3414_, v_stop_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_array_uget_borrowed(v_as_3413_, v_i_3414_);
v___x_3418_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3412_, v___x_3417_);
if (v___x_3418_ == 0)
{
size_t v___x_3419_; size_t v___x_3420_; 
v___x_3419_ = ((size_t)1ULL);
v___x_3420_ = lean_usize_add(v_i_3414_, v___x_3419_);
v_i_3414_ = v___x_3420_;
goto _start;
}
else
{
return v___x_3418_;
}
}
else
{
uint8_t v___x_3422_; 
v___x_3422_ = 0;
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3423_, lean_object* v_as_3424_, lean_object* v_i_3425_, lean_object* v_stop_3426_){
_start:
{
uint8_t v___x_1901__boxed_3427_; size_t v_i_boxed_3428_; size_t v_stop_boxed_3429_; uint8_t v_res_3430_; lean_object* v_r_3431_; 
v___x_1901__boxed_3427_ = lean_unbox(v___x_3423_);
v_i_boxed_3428_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_stop_boxed_3429_ = lean_unbox_usize(v_stop_3426_);
lean_dec(v_stop_3426_);
v_res_3430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1901__boxed_3427_, v_as_3424_, v_i_boxed_3428_, v_stop_boxed_3429_);
lean_dec_ref(v_as_3424_);
v_r_3431_ = lean_box(v_res_3430_);
return v_r_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3432_, lean_object* v_x_3433_){
_start:
{
uint8_t v___x_1909__boxed_3434_; uint8_t v_res_3435_; lean_object* v_r_3436_; 
v___x_1909__boxed_3434_ = lean_unbox(v___x_3432_);
v_res_3435_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1909__boxed_3434_, v_x_3433_);
lean_dec_ref(v_x_3433_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3437_, lean_object* v_t_3438_){
_start:
{
lean_object* v_root_3439_; lean_object* v_tail_3440_; uint8_t v___x_3441_; 
v_root_3439_ = lean_ctor_get(v_t_3438_, 0);
v_tail_3440_ = lean_ctor_get(v_t_3438_, 1);
v___x_3441_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3437_, v_root_3439_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = lean_array_get_size(v_tail_3440_);
v___x_3444_ = lean_nat_dec_lt(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
return v___x_3441_;
}
else
{
if (v___x_3444_ == 0)
{
return v___x_3441_;
}
else
{
size_t v___x_3445_; size_t v___x_3446_; uint8_t v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3443_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3437_, v_tail_3440_, v___x_3445_, v___x_3446_);
return v___x_3447_;
}
}
}
else
{
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3448_, lean_object* v_t_3449_){
_start:
{
uint8_t v___x_1952__boxed_3450_; uint8_t v_res_3451_; lean_object* v_r_3452_; 
v___x_1952__boxed_3450_ = lean_unbox(v___x_3448_);
v_res_3451_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1952__boxed_3450_, v_t_3449_);
lean_dec_ref(v_t_3449_);
v_r_3452_ = lean_box(v_res_3451_);
return v_r_3452_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3453_){
_start:
{
lean_object* v_reported_3454_; lean_object* v_unreported_3455_; uint8_t v___x_3456_; 
v_reported_3454_ = lean_ctor_get(v_log_3453_, 0);
v_unreported_3455_ = lean_ctor_get(v_log_3453_, 1);
v___x_3456_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3454_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
v___x_3457_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3456_, v_unreported_3455_);
return v___x_3457_;
}
else
{
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3458_){
_start:
{
uint8_t v_res_3459_; lean_object* v_r_3460_; 
v_res_3459_ = l_Lean_MessageLog_hasErrors(v_log_3458_);
lean_dec_ref(v_log_3458_);
v_r_3460_ = lean_box(v_res_3459_);
return v_r_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3461_){
_start:
{
lean_object* v_reported_3462_; lean_object* v_unreported_3463_; lean_object* v_loggedKinds_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3475_; 
v_reported_3462_ = lean_ctor_get(v_log_3461_, 0);
v_unreported_3463_ = lean_ctor_get(v_log_3461_, 1);
v_loggedKinds_3464_ = lean_ctor_get(v_log_3461_, 2);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_log_3461_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3466_ = v_log_3461_;
v_isShared_3467_ = v_isSharedCheck_3475_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_loggedKinds_3464_);
lean_inc(v_unreported_3463_);
lean_inc(v_reported_3462_);
lean_dec(v_log_3461_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3475_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3468_ = l_Lean_PersistentArray_append___redArg(v_reported_3462_, v_unreported_3463_);
lean_dec_ref(v_unreported_3463_);
v___x_3469_ = lean_unsigned_to_nat(32u);
v___x_3470_ = lean_mk_empty_array_with_capacity(v___x_3469_);
lean_dec_ref(v___x_3470_);
v___x_3471_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v___x_3471_);
lean_ctor_set(v___x_3466_, 0, v___x_3468_);
v___x_3473_ = v___x_3466_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_loggedKinds_3464_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_bs_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3479_ == 0)
{
return v_bs_3478_;
}
else
{
lean_object* v_v_3480_; lean_object* v_fileName_3481_; lean_object* v_pos_3482_; lean_object* v_endPos_3483_; uint8_t v_keepFullRange_3484_; uint8_t v_severity_3485_; uint8_t v_isSilent_3486_; lean_object* v_caption_3487_; lean_object* v_data_3488_; lean_object* v___x_3489_; lean_object* v_bs_x27_3490_; lean_object* v___y_3492_; 
v_v_3480_ = lean_array_uget(v_bs_3478_, v_i_3477_);
v_fileName_3481_ = lean_ctor_get(v_v_3480_, 0);
v_pos_3482_ = lean_ctor_get(v_v_3480_, 1);
v_endPos_3483_ = lean_ctor_get(v_v_3480_, 2);
v_keepFullRange_3484_ = lean_ctor_get_uint8(v_v_3480_, sizeof(void*)*5);
v_severity_3485_ = lean_ctor_get_uint8(v_v_3480_, sizeof(void*)*5 + 1);
v_isSilent_3486_ = lean_ctor_get_uint8(v_v_3480_, sizeof(void*)*5 + 2);
v_caption_3487_ = lean_ctor_get(v_v_3480_, 3);
v_data_3488_ = lean_ctor_get(v_v_3480_, 4);
v___x_3489_ = lean_unsigned_to_nat(0u);
v_bs_x27_3490_ = lean_array_uset(v_bs_3478_, v_i_3477_, v___x_3489_);
if (v_severity_3485_ == 2)
{
lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3504_; 
lean_inc(v_data_3488_);
lean_inc_ref(v_caption_3487_);
lean_inc(v_endPos_3483_);
lean_inc_ref(v_pos_3482_);
lean_inc_ref(v_fileName_3481_);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_v_3480_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; lean_object* v_unused_3506_; lean_object* v_unused_3507_; lean_object* v_unused_3508_; lean_object* v_unused_3509_; 
v_unused_3505_ = lean_ctor_get(v_v_3480_, 4);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_v_3480_, 3);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_v_3480_, 2);
lean_dec(v_unused_3507_);
v_unused_3508_ = lean_ctor_get(v_v_3480_, 1);
lean_dec(v_unused_3508_);
v_unused_3509_ = lean_ctor_get(v_v_3480_, 0);
lean_dec(v_unused_3509_);
v___x_3498_ = v_v_3480_;
v_isShared_3499_ = v_isSharedCheck_3504_;
goto v_resetjp_3497_;
}
else
{
lean_dec(v_v_3480_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3504_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
uint8_t v___x_3500_; lean_object* v___x_3502_; 
v___x_3500_ = 1;
if (v_isShared_3499_ == 0)
{
v___x_3502_ = v___x_3498_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fileName_3481_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_pos_3482_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_endPos_3483_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_caption_3487_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_data_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3503_, sizeof(void*)*5, v_keepFullRange_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3503_, sizeof(void*)*5 + 2, v_isSilent_3486_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_ctor_set_uint8(v___x_3502_, sizeof(void*)*5 + 1, v___x_3500_);
v___y_3492_ = v___x_3502_;
goto v___jp_3491_;
}
}
}
else
{
v___y_3492_ = v_v_3480_;
goto v___jp_3491_;
}
v___jp_3491_:
{
size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3477_, v___x_3493_);
v___x_3495_ = lean_array_uset(v_bs_x27_3490_, v_i_3477_, v___y_3492_);
v_i_3477_ = v___x_3494_;
v_bs_3478_ = v___x_3495_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_bs_3512_){
_start:
{
size_t v_sz_boxed_3513_; size_t v_i_boxed_3514_; lean_object* v_res_3515_; 
v_sz_boxed_3513_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3514_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3513_, v_i_boxed_3514_, v_bs_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3516_, size_t v_i_3517_, lean_object* v_bs_3518_){
_start:
{
uint8_t v___x_3519_; 
v___x_3519_ = lean_usize_dec_lt(v_i_3517_, v_sz_3516_);
if (v___x_3519_ == 0)
{
return v_bs_3518_;
}
else
{
lean_object* v_v_3520_; lean_object* v___x_3521_; lean_object* v_bs_x27_3522_; lean_object* v___x_3523_; size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v_v_3520_ = lean_array_uget(v_bs_3518_, v_i_3517_);
v___x_3521_ = lean_unsigned_to_nat(0u);
v_bs_x27_3522_ = lean_array_uset(v_bs_3518_, v_i_3517_, v___x_3521_);
v___x_3523_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3520_);
v___x_3524_ = ((size_t)1ULL);
v___x_3525_ = lean_usize_add(v_i_3517_, v___x_3524_);
v___x_3526_ = lean_array_uset(v_bs_x27_3522_, v_i_3517_, v___x_3523_);
v_i_3517_ = v___x_3525_;
v_bs_3518_ = v___x_3526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 0)
{
lean_object* v_cs_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3539_; 
v_cs_3529_ = lean_ctor_get(v_x_3528_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_x_3528_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3531_ = v_x_3528_;
v_isShared_3532_ = v_isSharedCheck_3539_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_cs_3529_);
lean_dec(v_x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3539_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
size_t v_sz_3533_; size_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; 
v_sz_3533_ = lean_array_size(v_cs_3529_);
v___x_3534_ = ((size_t)0ULL);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3533_, v___x_3534_, v_cs_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3535_);
v___x_3537_ = v___x_3531_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_object* v_vs_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3550_; 
v_vs_3540_ = lean_ctor_get(v_x_3528_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_x_3528_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3542_ = v_x_3528_;
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_vs_3540_);
lean_dec(v_x_3528_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
size_t v_sz_3544_; size_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v_sz_3544_ = lean_array_size(v_vs_3540_);
v___x_3545_ = ((size_t)0ULL);
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3544_, v___x_3545_, v_vs_3540_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3546_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3551_, lean_object* v_i_3552_, lean_object* v_bs_3553_){
_start:
{
size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3551_);
lean_dec(v_sz_3551_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3554_, v_i_boxed_3555_, v_bs_3553_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3557_){
_start:
{
lean_object* v_root_3558_; lean_object* v_tail_3559_; lean_object* v_size_3560_; size_t v_shift_3561_; lean_object* v_tailOff_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3573_; 
v_root_3558_ = lean_ctor_get(v_t_3557_, 0);
v_tail_3559_ = lean_ctor_get(v_t_3557_, 1);
v_size_3560_ = lean_ctor_get(v_t_3557_, 2);
v_shift_3561_ = lean_ctor_get_usize(v_t_3557_, 4);
v_tailOff_3562_ = lean_ctor_get(v_t_3557_, 3);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_t_3557_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3564_ = v_t_3557_;
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_tailOff_3562_);
lean_inc(v_size_3560_);
lean_inc(v_tail_3559_);
lean_inc(v_root_3558_);
lean_dec(v_t_3557_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3573_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; size_t v_sz_3567_; size_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3566_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3558_);
v_sz_3567_ = lean_array_size(v_tail_3559_);
v___x_3568_ = ((size_t)0ULL);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3567_, v___x_3568_, v_tail_3559_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3569_);
lean_ctor_set(v___x_3564_, 0, v___x_3566_);
v___x_3571_ = v___x_3564_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_size_3560_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_tailOff_3562_);
lean_ctor_set_usize(v_reuseFailAlloc_3572_, 4, v_shift_3561_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3574_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v_unreported_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3587_; 
v___x_3575_ = lean_unsigned_to_nat(32u);
v___x_3576_ = lean_mk_empty_array_with_capacity(v___x_3575_);
lean_dec_ref(v___x_3576_);
v___x_3577_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3578_ = lean_ctor_get(v_log_3574_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_log_3574_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; lean_object* v_unused_3589_; 
v_unused_3588_ = lean_ctor_get(v_log_3574_, 2);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_log_3574_, 0);
lean_dec(v_unused_3589_);
v___x_3580_ = v_log_3574_;
v_isShared_3581_ = v_isSharedCheck_3587_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_unreported_3578_);
lean_dec(v_log_3574_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3587_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3582_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3578_);
v___x_3583_ = l_Lean_NameSet_empty;
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 2, v___x_3583_);
lean_ctor_set(v___x_3580_, 1, v___x_3582_);
lean_ctor_set(v___x_3580_, 0, v___x_3577_);
v___x_3585_ = v___x_3580_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3590_, size_t v_i_3591_, lean_object* v_bs_3592_){
_start:
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_usize_dec_lt(v_i_3591_, v_sz_3590_);
if (v___x_3593_ == 0)
{
return v_bs_3592_;
}
else
{
lean_object* v_v_3594_; lean_object* v_fileName_3595_; lean_object* v_pos_3596_; lean_object* v_endPos_3597_; uint8_t v_keepFullRange_3598_; uint8_t v_severity_3599_; uint8_t v_isSilent_3600_; lean_object* v_caption_3601_; lean_object* v_data_3602_; lean_object* v___x_3603_; lean_object* v_bs_x27_3604_; lean_object* v___y_3606_; 
v_v_3594_ = lean_array_uget(v_bs_3592_, v_i_3591_);
v_fileName_3595_ = lean_ctor_get(v_v_3594_, 0);
v_pos_3596_ = lean_ctor_get(v_v_3594_, 1);
v_endPos_3597_ = lean_ctor_get(v_v_3594_, 2);
v_keepFullRange_3598_ = lean_ctor_get_uint8(v_v_3594_, sizeof(void*)*5);
v_severity_3599_ = lean_ctor_get_uint8(v_v_3594_, sizeof(void*)*5 + 1);
v_isSilent_3600_ = lean_ctor_get_uint8(v_v_3594_, sizeof(void*)*5 + 2);
v_caption_3601_ = lean_ctor_get(v_v_3594_, 3);
v_data_3602_ = lean_ctor_get(v_v_3594_, 4);
v___x_3603_ = lean_unsigned_to_nat(0u);
v_bs_x27_3604_ = lean_array_uset(v_bs_3592_, v_i_3591_, v___x_3603_);
if (v_severity_3599_ == 2)
{
lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3618_; 
lean_inc(v_data_3602_);
lean_inc_ref(v_caption_3601_);
lean_inc(v_endPos_3597_);
lean_inc_ref(v_pos_3596_);
lean_inc_ref(v_fileName_3595_);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_v_3594_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3619_ = lean_ctor_get(v_v_3594_, 4);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v_v_3594_, 3);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_v_3594_, 2);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_v_3594_, 1);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_v_3594_, 0);
lean_dec(v_unused_3623_);
v___x_3612_ = v_v_3594_;
v_isShared_3613_ = v_isSharedCheck_3618_;
goto v_resetjp_3611_;
}
else
{
lean_dec(v_v_3594_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3618_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
uint8_t v___x_3614_; lean_object* v___x_3616_; 
v___x_3614_ = 0;
if (v_isShared_3613_ == 0)
{
v___x_3616_ = v___x_3612_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_fileName_3595_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_pos_3596_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_endPos_3597_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_caption_3601_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v_data_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, sizeof(void*)*5, v_keepFullRange_3598_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, sizeof(void*)*5 + 2, v_isSilent_3600_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*5 + 1, v___x_3614_);
v___y_3606_ = v___x_3616_;
goto v___jp_3605_;
}
}
}
else
{
v___y_3606_ = v_v_3594_;
goto v___jp_3605_;
}
v___jp_3605_:
{
size_t v___x_3607_; size_t v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_add(v_i_3591_, v___x_3607_);
v___x_3609_ = lean_array_uset(v_bs_x27_3604_, v_i_3591_, v___y_3606_);
v_i_3591_ = v___x_3608_;
v_bs_3592_ = v___x_3609_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_bs_3626_){
_start:
{
size_t v_sz_boxed_3627_; size_t v_i_boxed_3628_; lean_object* v_res_3629_; 
v_sz_boxed_3627_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3628_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3627_, v_i_boxed_3628_, v_bs_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3630_, size_t v_i_3631_, lean_object* v_bs_3632_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_lt(v_i_3631_, v_sz_3630_);
if (v___x_3633_ == 0)
{
return v_bs_3632_;
}
else
{
lean_object* v_v_3634_; lean_object* v___x_3635_; lean_object* v_bs_x27_3636_; lean_object* v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; lean_object* v___x_3640_; 
v_v_3634_ = lean_array_uget(v_bs_3632_, v_i_3631_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v_bs_x27_3636_ = lean_array_uset(v_bs_3632_, v_i_3631_, v___x_3635_);
v___x_3637_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3634_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_add(v_i_3631_, v___x_3638_);
v___x_3640_ = lean_array_uset(v_bs_x27_3636_, v_i_3631_, v___x_3637_);
v_i_3631_ = v___x_3639_;
v_bs_3632_ = v___x_3640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3642_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_object* v_cs_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3653_; 
v_cs_3643_ = lean_ctor_get(v_x_3642_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_x_3642_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3645_ = v_x_3642_;
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_cs_3643_);
lean_dec(v_x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
size_t v_sz_3647_; size_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v_sz_3647_ = lean_array_size(v_cs_3643_);
v___x_3648_ = ((size_t)0ULL);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3647_, v___x_3648_, v_cs_3643_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3649_);
v___x_3651_ = v___x_3645_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_object* v_vs_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3664_; 
v_vs_3654_ = lean_ctor_get(v_x_3642_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_x_3642_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3656_ = v_x_3642_;
v_isShared_3657_ = v_isSharedCheck_3664_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_vs_3654_);
lean_dec(v_x_3642_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3664_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
size_t v_sz_3658_; size_t v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
v_sz_3658_ = lean_array_size(v_vs_3654_);
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3658_, v___x_3659_, v_vs_3654_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3660_);
v___x_3662_ = v___x_3656_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_bs_3667_){
_start:
{
size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3668_, v_i_boxed_3669_, v_bs_3667_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3671_){
_start:
{
lean_object* v_root_3672_; lean_object* v_tail_3673_; lean_object* v_size_3674_; size_t v_shift_3675_; lean_object* v_tailOff_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3687_; 
v_root_3672_ = lean_ctor_get(v_t_3671_, 0);
v_tail_3673_ = lean_ctor_get(v_t_3671_, 1);
v_size_3674_ = lean_ctor_get(v_t_3671_, 2);
v_shift_3675_ = lean_ctor_get_usize(v_t_3671_, 4);
v_tailOff_3676_ = lean_ctor_get(v_t_3671_, 3);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_t_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3678_ = v_t_3671_;
v_isShared_3679_ = v_isSharedCheck_3687_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_tailOff_3676_);
lean_inc(v_size_3674_);
lean_inc(v_tail_3673_);
lean_inc(v_root_3672_);
lean_dec(v_t_3671_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3687_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; size_t v_sz_3681_; size_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3680_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3672_);
v_sz_3681_ = lean_array_size(v_tail_3673_);
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3681_, v___x_3682_, v_tail_3673_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 1, v___x_3683_);
lean_ctor_set(v___x_3678_, 0, v___x_3680_);
v___x_3685_ = v___x_3678_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_size_3674_);
lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_tailOff_3676_);
lean_ctor_set_usize(v_reuseFailAlloc_3686_, 4, v_shift_3675_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3688_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v_unreported_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3701_; 
v___x_3689_ = lean_unsigned_to_nat(32u);
v___x_3690_ = lean_mk_empty_array_with_capacity(v___x_3689_);
lean_dec_ref(v___x_3690_);
v___x_3691_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3692_ = lean_ctor_get(v_log_3688_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_log_3688_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; lean_object* v_unused_3703_; 
v_unused_3702_ = lean_ctor_get(v_log_3688_, 2);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v_log_3688_, 0);
lean_dec(v_unused_3703_);
v___x_3694_ = v_log_3688_;
v_isShared_3695_ = v_isSharedCheck_3701_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_unreported_3692_);
lean_dec(v_log_3688_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3701_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3696_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3692_);
v___x_3697_ = l_Lean_NameSet_empty;
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 2, v___x_3697_);
lean_ctor_set(v___x_3694_, 1, v___x_3696_);
lean_ctor_set(v___x_3694_, 0, v___x_3691_);
v___x_3699_ = v___x_3694_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3704_, size_t v_i_3705_, size_t v_stop_3706_, lean_object* v_b_3707_){
_start:
{
lean_object* v___y_3709_; uint8_t v___x_3713_; 
v___x_3713_ = lean_usize_dec_eq(v_i_3705_, v_stop_3706_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; uint8_t v_severity_3715_; 
v___x_3714_ = lean_array_uget_borrowed(v_as_3704_, v_i_3705_);
v_severity_3715_ = lean_ctor_get_uint8(v___x_3714_, sizeof(void*)*5 + 1);
if (v_severity_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_inc(v___x_3714_);
v___x_3716_ = l_Lean_PersistentArray_push___redArg(v_b_3707_, v___x_3714_);
v___y_3709_ = v___x_3716_;
goto v___jp_3708_;
}
else
{
v___y_3709_ = v_b_3707_;
goto v___jp_3708_;
}
}
else
{
return v_b_3707_;
}
v___jp_3708_:
{
size_t v___x_3710_; size_t v___x_3711_; 
v___x_3710_ = ((size_t)1ULL);
v___x_3711_ = lean_usize_add(v_i_3705_, v___x_3710_);
v_i_3705_ = v___x_3711_;
v_b_3707_ = v___y_3709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3717_, lean_object* v_i_3718_, lean_object* v_stop_3719_, lean_object* v_b_3720_){
_start:
{
size_t v_i_boxed_3721_; size_t v_stop_boxed_3722_; lean_object* v_res_3723_; 
v_i_boxed_3721_ = lean_unbox_usize(v_i_3718_);
lean_dec(v_i_3718_);
v_stop_boxed_3722_ = lean_unbox_usize(v_stop_3719_);
lean_dec(v_stop_3719_);
v_res_3723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3717_, v_i_boxed_3721_, v_stop_boxed_3722_, v_b_3720_);
lean_dec_ref(v_as_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3724_) == 0)
{
lean_object* v_cs_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_cs_3726_ = lean_ctor_get(v_x_3724_, 0);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = lean_array_get_size(v_cs_3726_);
v___x_3729_ = lean_nat_dec_lt(v___x_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
return v_x_3725_;
}
else
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_nat_dec_le(v___x_3728_, v___x_3728_);
if (v___x_3730_ == 0)
{
if (v___x_3729_ == 0)
{
return v_x_3725_;
}
else
{
size_t v___x_3731_; size_t v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = ((size_t)0ULL);
v___x_3732_ = lean_usize_of_nat(v___x_3728_);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3726_, v___x_3731_, v___x_3732_, v_x_3725_);
return v___x_3733_;
}
}
else
{
size_t v___x_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = ((size_t)0ULL);
v___x_3735_ = lean_usize_of_nat(v___x_3728_);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3726_, v___x_3734_, v___x_3735_, v_x_3725_);
return v___x_3736_;
}
}
}
else
{
lean_object* v_vs_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v_vs_3737_ = lean_ctor_get(v_x_3724_, 0);
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_array_get_size(v_vs_3737_);
v___x_3740_ = lean_nat_dec_lt(v___x_3738_, v___x_3739_);
if (v___x_3740_ == 0)
{
return v_x_3725_;
}
else
{
uint8_t v___x_3741_; 
v___x_3741_ = lean_nat_dec_le(v___x_3739_, v___x_3739_);
if (v___x_3741_ == 0)
{
if (v___x_3740_ == 0)
{
return v_x_3725_;
}
else
{
size_t v___x_3742_; size_t v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = ((size_t)0ULL);
v___x_3743_ = lean_usize_of_nat(v___x_3739_);
v___x_3744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3737_, v___x_3742_, v___x_3743_, v_x_3725_);
return v___x_3744_;
}
}
else
{
size_t v___x_3745_; size_t v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = ((size_t)0ULL);
v___x_3746_ = lean_usize_of_nat(v___x_3739_);
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3737_, v___x_3745_, v___x_3746_, v_x_3725_);
return v___x_3747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3748_, size_t v_i_3749_, size_t v_stop_3750_, lean_object* v_b_3751_){
_start:
{
uint8_t v___x_3752_; 
v___x_3752_ = lean_usize_dec_eq(v_i_3749_, v_stop_3750_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; size_t v___x_3755_; size_t v___x_3756_; 
v___x_3753_ = lean_array_uget_borrowed(v_as_3748_, v_i_3749_);
v___x_3754_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3753_, v_b_3751_);
v___x_3755_ = ((size_t)1ULL);
v___x_3756_ = lean_usize_add(v_i_3749_, v___x_3755_);
v_i_3749_ = v___x_3756_;
v_b_3751_ = v___x_3754_;
goto _start;
}
else
{
return v_b_3751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3758_, lean_object* v_i_3759_, lean_object* v_stop_3760_, lean_object* v_b_3761_){
_start:
{
size_t v_i_boxed_3762_; size_t v_stop_boxed_3763_; lean_object* v_res_3764_; 
v_i_boxed_3762_ = lean_unbox_usize(v_i_3759_);
lean_dec(v_i_3759_);
v_stop_boxed_3763_ = lean_unbox_usize(v_stop_3760_);
lean_dec(v_stop_3760_);
v_res_3764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3758_, v_i_boxed_3762_, v_stop_boxed_3763_, v_b_3761_);
lean_dec_ref(v_as_3758_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3765_, v_x_3766_);
lean_dec_ref(v_x_3765_);
return v_res_3767_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3769_, size_t v_x_3770_, size_t v_x_3771_, lean_object* v_x_3772_){
_start:
{
if (lean_obj_tag(v_x_3769_) == 0)
{
lean_object* v_cs_3773_; lean_object* v___x_3774_; size_t v___x_3775_; lean_object* v_j_3776_; lean_object* v___x_3777_; size_t v___x_3778_; size_t v___x_3779_; size_t v___x_3780_; size_t v___x_3781_; size_t v___x_3782_; size_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v_cs_3773_ = lean_ctor_get(v_x_3769_, 0);
v___x_3774_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3775_ = lean_usize_shift_right(v_x_3770_, v_x_3771_);
v_j_3776_ = lean_usize_to_nat(v___x_3775_);
v___x_3777_ = lean_array_get_borrowed(v___x_3774_, v_cs_3773_, v_j_3776_);
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_shift_left(v___x_3778_, v_x_3771_);
v___x_3780_ = lean_usize_sub(v___x_3779_, v___x_3778_);
v___x_3781_ = lean_usize_land(v_x_3770_, v___x_3780_);
v___x_3782_ = ((size_t)5ULL);
v___x_3783_ = lean_usize_sub(v_x_3771_, v___x_3782_);
v___x_3784_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3777_, v___x_3781_, v___x_3783_, v_x_3772_);
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_nat_add(v_j_3776_, v___x_3785_);
lean_dec(v_j_3776_);
v___x_3787_ = lean_array_get_size(v_cs_3773_);
v___x_3788_ = lean_nat_dec_lt(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_dec(v___x_3786_);
return v___x_3784_;
}
else
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_nat_dec_le(v___x_3787_, v___x_3787_);
if (v___x_3789_ == 0)
{
if (v___x_3788_ == 0)
{
lean_dec(v___x_3786_);
return v___x_3784_;
}
else
{
size_t v___x_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_usize_of_nat(v___x_3786_);
lean_dec(v___x_3786_);
v___x_3791_ = lean_usize_of_nat(v___x_3787_);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3773_, v___x_3790_, v___x_3791_, v___x_3784_);
return v___x_3792_;
}
}
else
{
size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = lean_usize_of_nat(v___x_3786_);
lean_dec(v___x_3786_);
v___x_3794_ = lean_usize_of_nat(v___x_3787_);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3773_, v___x_3793_, v___x_3794_, v___x_3784_);
return v___x_3795_;
}
}
}
else
{
lean_object* v_vs_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v_vs_3796_ = lean_ctor_get(v_x_3769_, 0);
v___x_3797_ = lean_usize_to_nat(v_x_3770_);
v___x_3798_ = lean_array_get_size(v_vs_3796_);
v___x_3799_ = lean_nat_dec_lt(v___x_3797_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_dec(v___x_3797_);
return v_x_3772_;
}
else
{
uint8_t v___x_3800_; 
v___x_3800_ = lean_nat_dec_le(v___x_3798_, v___x_3798_);
if (v___x_3800_ == 0)
{
if (v___x_3799_ == 0)
{
lean_dec(v___x_3797_);
return v_x_3772_;
}
else
{
size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_usize_of_nat(v___x_3797_);
lean_dec(v___x_3797_);
v___x_3802_ = lean_usize_of_nat(v___x_3798_);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3796_, v___x_3801_, v___x_3802_, v_x_3772_);
return v___x_3803_;
}
}
else
{
size_t v___x_3804_; size_t v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_usize_of_nat(v___x_3797_);
lean_dec(v___x_3797_);
v___x_3805_ = lean_usize_of_nat(v___x_3798_);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3796_, v___x_3804_, v___x_3805_, v_x_3772_);
return v___x_3806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3807_, lean_object* v_x_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_){
_start:
{
size_t v_x_1528__boxed_3811_; size_t v_x_1529__boxed_3812_; lean_object* v_res_3813_; 
v_x_1528__boxed_3811_ = lean_unbox_usize(v_x_3808_);
lean_dec(v_x_3808_);
v_x_1529__boxed_3812_ = lean_unbox_usize(v_x_3809_);
lean_dec(v_x_3809_);
v_res_3813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3807_, v_x_1528__boxed_3811_, v_x_1529__boxed_3812_, v_x_3810_);
lean_dec_ref(v_x_3807_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3814_, lean_object* v_init_3815_, lean_object* v_start_3816_){
_start:
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = lean_unsigned_to_nat(0u);
v___x_3818_ = lean_nat_dec_eq(v_start_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v_root_3819_; lean_object* v_tail_3820_; size_t v_shift_3821_; lean_object* v_tailOff_3822_; uint8_t v___x_3823_; 
v_root_3819_ = lean_ctor_get(v_t_3814_, 0);
v_tail_3820_ = lean_ctor_get(v_t_3814_, 1);
v_shift_3821_ = lean_ctor_get_usize(v_t_3814_, 4);
v_tailOff_3822_ = lean_ctor_get(v_t_3814_, 3);
v___x_3823_ = lean_nat_dec_le(v_tailOff_3822_, v_start_3816_);
if (v___x_3823_ == 0)
{
size_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3824_ = lean_usize_of_nat(v_start_3816_);
v___x_3825_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3819_, v___x_3824_, v_shift_3821_, v_init_3815_);
v___x_3826_ = lean_array_get_size(v_tail_3820_);
v___x_3827_ = lean_nat_dec_lt(v___x_3817_, v___x_3826_);
if (v___x_3827_ == 0)
{
return v___x_3825_;
}
else
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_le(v___x_3826_, v___x_3826_);
if (v___x_3828_ == 0)
{
if (v___x_3827_ == 0)
{
return v___x_3825_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = ((size_t)0ULL);
v___x_3830_ = lean_usize_of_nat(v___x_3826_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3820_, v___x_3829_, v___x_3830_, v___x_3825_);
return v___x_3831_;
}
}
else
{
size_t v___x_3832_; size_t v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = ((size_t)0ULL);
v___x_3833_ = lean_usize_of_nat(v___x_3826_);
v___x_3834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3820_, v___x_3832_, v___x_3833_, v___x_3825_);
return v___x_3834_;
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v___x_3835_ = lean_nat_sub(v_start_3816_, v_tailOff_3822_);
v___x_3836_ = lean_array_get_size(v_tail_3820_);
v___x_3837_ = lean_nat_dec_lt(v___x_3835_, v___x_3836_);
if (v___x_3837_ == 0)
{
lean_dec(v___x_3835_);
return v_init_3815_;
}
else
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_nat_dec_le(v___x_3836_, v___x_3836_);
if (v___x_3838_ == 0)
{
if (v___x_3837_ == 0)
{
lean_dec(v___x_3835_);
return v_init_3815_;
}
else
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_usize_of_nat(v___x_3835_);
lean_dec(v___x_3835_);
v___x_3840_ = lean_usize_of_nat(v___x_3836_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3820_, v___x_3839_, v___x_3840_, v_init_3815_);
return v___x_3841_;
}
}
else
{
size_t v___x_3842_; size_t v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = lean_usize_of_nat(v___x_3835_);
lean_dec(v___x_3835_);
v___x_3843_ = lean_usize_of_nat(v___x_3836_);
v___x_3844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3820_, v___x_3842_, v___x_3843_, v_init_3815_);
return v___x_3844_;
}
}
}
}
else
{
lean_object* v_root_3845_; lean_object* v_tail_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_root_3845_ = lean_ctor_get(v_t_3814_, 0);
v_tail_3846_ = lean_ctor_get(v_t_3814_, 1);
v___x_3847_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3845_, v_init_3815_);
v___x_3848_ = lean_array_get_size(v_tail_3846_);
v___x_3849_ = lean_nat_dec_lt(v___x_3817_, v___x_3848_);
if (v___x_3849_ == 0)
{
return v___x_3847_;
}
else
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_nat_dec_le(v___x_3848_, v___x_3848_);
if (v___x_3850_ == 0)
{
if (v___x_3849_ == 0)
{
return v___x_3847_;
}
else
{
size_t v___x_3851_; size_t v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = ((size_t)0ULL);
v___x_3852_ = lean_usize_of_nat(v___x_3848_);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3846_, v___x_3851_, v___x_3852_, v___x_3847_);
return v___x_3853_;
}
}
else
{
size_t v___x_3854_; size_t v___x_3855_; lean_object* v___x_3856_; 
v___x_3854_ = ((size_t)0ULL);
v___x_3855_ = lean_usize_of_nat(v___x_3848_);
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3846_, v___x_3854_, v___x_3855_, v___x_3847_);
return v___x_3856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3857_, lean_object* v_init_3858_, lean_object* v_start_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3857_, v_init_3858_, v_start_3859_);
lean_dec(v_start_3859_);
lean_dec_ref(v_t_3857_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3861_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v_unreported_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3875_; 
v___x_3862_ = lean_unsigned_to_nat(32u);
v___x_3863_ = lean_mk_empty_array_with_capacity(v___x_3862_);
lean_dec_ref(v___x_3863_);
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3866_ = lean_ctor_get(v_log_3861_, 1);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_log_3861_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; lean_object* v_unused_3877_; 
v_unused_3876_ = lean_ctor_get(v_log_3861_, 2);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_log_3861_, 0);
lean_dec(v_unused_3877_);
v___x_3868_ = v_log_3861_;
v_isShared_3869_ = v_isSharedCheck_3875_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_unreported_3866_);
lean_dec(v_log_3861_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3875_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3870_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3866_, v___x_3865_, v___x_3864_);
lean_dec_ref(v_unreported_3866_);
v___x_3871_ = l_Lean_NameSet_empty;
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 2, v___x_3871_);
lean_ctor_set(v___x_3868_, 1, v___x_3870_);
lean_ctor_set(v___x_3868_, 0, v___x_3865_);
v___x_3873_ = v___x_3868_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3878_, size_t v_i_3879_, size_t v_stop_3880_, lean_object* v_b_3881_){
_start:
{
lean_object* v___y_3883_; uint8_t v___x_3887_; 
v___x_3887_ = lean_usize_dec_eq(v_i_3879_, v_stop_3880_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; uint8_t v_severity_3889_; 
v___x_3888_ = lean_array_uget_borrowed(v_as_3878_, v_i_3879_);
v_severity_3889_ = lean_ctor_get_uint8(v___x_3888_, sizeof(void*)*5 + 1);
if (v_severity_3889_ == 1)
{
lean_object* v___x_3890_; 
lean_inc(v___x_3888_);
v___x_3890_ = l_Lean_PersistentArray_push___redArg(v_b_3881_, v___x_3888_);
v___y_3883_ = v___x_3890_;
goto v___jp_3882_;
}
else
{
v___y_3883_ = v_b_3881_;
goto v___jp_3882_;
}
}
else
{
return v_b_3881_;
}
v___jp_3882_:
{
size_t v___x_3884_; size_t v___x_3885_; 
v___x_3884_ = ((size_t)1ULL);
v___x_3885_ = lean_usize_add(v_i_3879_, v___x_3884_);
v_i_3879_ = v___x_3885_;
v_b_3881_ = v___y_3883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3891_, lean_object* v_i_3892_, lean_object* v_stop_3893_, lean_object* v_b_3894_){
_start:
{
size_t v_i_boxed_3895_; size_t v_stop_boxed_3896_; lean_object* v_res_3897_; 
v_i_boxed_3895_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_stop_boxed_3896_ = lean_unbox_usize(v_stop_3893_);
lean_dec(v_stop_3893_);
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3891_, v_i_boxed_3895_, v_stop_boxed_3896_, v_b_3894_);
lean_dec_ref(v_as_3891_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3898_) == 0)
{
lean_object* v_cs_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; 
v_cs_3900_ = lean_ctor_get(v_x_3898_, 0);
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = lean_array_get_size(v_cs_3900_);
v___x_3903_ = lean_nat_dec_lt(v___x_3901_, v___x_3902_);
if (v___x_3903_ == 0)
{
return v_x_3899_;
}
else
{
uint8_t v___x_3904_; 
v___x_3904_ = lean_nat_dec_le(v___x_3902_, v___x_3902_);
if (v___x_3904_ == 0)
{
if (v___x_3903_ == 0)
{
return v_x_3899_;
}
else
{
size_t v___x_3905_; size_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = lean_usize_of_nat(v___x_3902_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3900_, v___x_3905_, v___x_3906_, v_x_3899_);
return v___x_3907_;
}
}
else
{
size_t v___x_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = ((size_t)0ULL);
v___x_3909_ = lean_usize_of_nat(v___x_3902_);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3900_, v___x_3908_, v___x_3909_, v_x_3899_);
return v___x_3910_;
}
}
}
else
{
lean_object* v_vs_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_vs_3911_ = lean_ctor_get(v_x_3898_, 0);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = lean_array_get_size(v_vs_3911_);
v___x_3914_ = lean_nat_dec_lt(v___x_3912_, v___x_3913_);
if (v___x_3914_ == 0)
{
return v_x_3899_;
}
else
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_nat_dec_le(v___x_3913_, v___x_3913_);
if (v___x_3915_ == 0)
{
if (v___x_3914_ == 0)
{
return v_x_3899_;
}
else
{
size_t v___x_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = ((size_t)0ULL);
v___x_3917_ = lean_usize_of_nat(v___x_3913_);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3911_, v___x_3916_, v___x_3917_, v_x_3899_);
return v___x_3918_;
}
}
else
{
size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = ((size_t)0ULL);
v___x_3920_ = lean_usize_of_nat(v___x_3913_);
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3911_, v___x_3919_, v___x_3920_, v_x_3899_);
return v___x_3921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3922_, size_t v_i_3923_, size_t v_stop_3924_, lean_object* v_b_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_usize_dec_eq(v_i_3923_, v_stop_3924_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3928_; size_t v___x_3929_; size_t v___x_3930_; 
v___x_3927_ = lean_array_uget_borrowed(v_as_3922_, v_i_3923_);
v___x_3928_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3927_, v_b_3925_);
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_i_3923_, v___x_3929_);
v_i_3923_ = v___x_3930_;
v_b_3925_ = v___x_3928_;
goto _start;
}
else
{
return v_b_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3932_, lean_object* v_i_3933_, lean_object* v_stop_3934_, lean_object* v_b_3935_){
_start:
{
size_t v_i_boxed_3936_; size_t v_stop_boxed_3937_; lean_object* v_res_3938_; 
v_i_boxed_3936_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_stop_boxed_3937_ = lean_unbox_usize(v_stop_3934_);
lean_dec(v_stop_3934_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3932_, v_i_boxed_3936_, v_stop_boxed_3937_, v_b_3935_);
lean_dec_ref(v_as_3932_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3939_, lean_object* v_x_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3939_, v_x_3940_);
lean_dec_ref(v_x_3939_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3942_, size_t v_x_3943_, size_t v_x_3944_, lean_object* v_x_3945_){
_start:
{
if (lean_obj_tag(v_x_3942_) == 0)
{
lean_object* v_cs_3946_; lean_object* v___x_3947_; size_t v___x_3948_; lean_object* v_j_3949_; lean_object* v___x_3950_; size_t v___x_3951_; size_t v___x_3952_; size_t v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; size_t v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v_cs_3946_ = lean_ctor_get(v_x_3942_, 0);
v___x_3947_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3948_ = lean_usize_shift_right(v_x_3943_, v_x_3944_);
v_j_3949_ = lean_usize_to_nat(v___x_3948_);
v___x_3950_ = lean_array_get_borrowed(v___x_3947_, v_cs_3946_, v_j_3949_);
v___x_3951_ = ((size_t)1ULL);
v___x_3952_ = lean_usize_shift_left(v___x_3951_, v_x_3944_);
v___x_3953_ = lean_usize_sub(v___x_3952_, v___x_3951_);
v___x_3954_ = lean_usize_land(v_x_3943_, v___x_3953_);
v___x_3955_ = ((size_t)5ULL);
v___x_3956_ = lean_usize_sub(v_x_3944_, v___x_3955_);
v___x_3957_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3950_, v___x_3954_, v___x_3956_, v_x_3945_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_add(v_j_3949_, v___x_3958_);
lean_dec(v_j_3949_);
v___x_3960_ = lean_array_get_size(v_cs_3946_);
v___x_3961_ = lean_nat_dec_lt(v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_dec(v___x_3959_);
return v___x_3957_;
}
else
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_nat_dec_le(v___x_3960_, v___x_3960_);
if (v___x_3962_ == 0)
{
if (v___x_3961_ == 0)
{
lean_dec(v___x_3959_);
return v___x_3957_;
}
else
{
size_t v___x_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_usize_of_nat(v___x_3959_);
lean_dec(v___x_3959_);
v___x_3964_ = lean_usize_of_nat(v___x_3960_);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3946_, v___x_3963_, v___x_3964_, v___x_3957_);
return v___x_3965_;
}
}
else
{
size_t v___x_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = lean_usize_of_nat(v___x_3959_);
lean_dec(v___x_3959_);
v___x_3967_ = lean_usize_of_nat(v___x_3960_);
v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3946_, v___x_3966_, v___x_3967_, v___x_3957_);
return v___x_3968_;
}
}
}
else
{
lean_object* v_vs_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v_vs_3969_ = lean_ctor_get(v_x_3942_, 0);
v___x_3970_ = lean_usize_to_nat(v_x_3943_);
v___x_3971_ = lean_array_get_size(v_vs_3969_);
v___x_3972_ = lean_nat_dec_lt(v___x_3970_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_dec(v___x_3970_);
return v_x_3945_;
}
else
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_nat_dec_le(v___x_3971_, v___x_3971_);
if (v___x_3973_ == 0)
{
if (v___x_3972_ == 0)
{
lean_dec(v___x_3970_);
return v_x_3945_;
}
else
{
size_t v___x_3974_; size_t v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = lean_usize_of_nat(v___x_3970_);
lean_dec(v___x_3970_);
v___x_3975_ = lean_usize_of_nat(v___x_3971_);
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3969_, v___x_3974_, v___x_3975_, v_x_3945_);
return v___x_3976_;
}
}
else
{
size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_usize_of_nat(v___x_3970_);
lean_dec(v___x_3970_);
v___x_3978_ = lean_usize_of_nat(v___x_3971_);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3969_, v___x_3977_, v___x_3978_, v_x_3945_);
return v___x_3979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3980_, lean_object* v_x_3981_, lean_object* v_x_3982_, lean_object* v_x_3983_){
_start:
{
size_t v_x_1527__boxed_3984_; size_t v_x_1528__boxed_3985_; lean_object* v_res_3986_; 
v_x_1527__boxed_3984_ = lean_unbox_usize(v_x_3981_);
lean_dec(v_x_3981_);
v_x_1528__boxed_3985_ = lean_unbox_usize(v_x_3982_);
lean_dec(v_x_3982_);
v_res_3986_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3980_, v_x_1527__boxed_3984_, v_x_1528__boxed_3985_, v_x_3983_);
lean_dec_ref(v_x_3980_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3987_, lean_object* v_init_3988_, lean_object* v_start_3989_){
_start:
{
lean_object* v___x_3990_; uint8_t v___x_3991_; 
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = lean_nat_dec_eq(v_start_3989_, v___x_3990_);
if (v___x_3991_ == 0)
{
lean_object* v_root_3992_; lean_object* v_tail_3993_; size_t v_shift_3994_; lean_object* v_tailOff_3995_; uint8_t v___x_3996_; 
v_root_3992_ = lean_ctor_get(v_t_3987_, 0);
v_tail_3993_ = lean_ctor_get(v_t_3987_, 1);
v_shift_3994_ = lean_ctor_get_usize(v_t_3987_, 4);
v_tailOff_3995_ = lean_ctor_get(v_t_3987_, 3);
v___x_3996_ = lean_nat_dec_le(v_tailOff_3995_, v_start_3989_);
if (v___x_3996_ == 0)
{
size_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3997_ = lean_usize_of_nat(v_start_3989_);
v___x_3998_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3992_, v___x_3997_, v_shift_3994_, v_init_3988_);
v___x_3999_ = lean_array_get_size(v_tail_3993_);
v___x_4000_ = lean_nat_dec_lt(v___x_3990_, v___x_3999_);
if (v___x_4000_ == 0)
{
return v___x_3998_;
}
else
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_nat_dec_le(v___x_3999_, v___x_3999_);
if (v___x_4001_ == 0)
{
if (v___x_4000_ == 0)
{
return v___x_3998_;
}
else
{
size_t v___x_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = ((size_t)0ULL);
v___x_4003_ = lean_usize_of_nat(v___x_3999_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3993_, v___x_4002_, v___x_4003_, v___x_3998_);
return v___x_4004_;
}
}
else
{
size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = ((size_t)0ULL);
v___x_4006_ = lean_usize_of_nat(v___x_3999_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3993_, v___x_4005_, v___x_4006_, v___x_3998_);
return v___x_4007_;
}
}
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4008_ = lean_nat_sub(v_start_3989_, v_tailOff_3995_);
v___x_4009_ = lean_array_get_size(v_tail_3993_);
v___x_4010_ = lean_nat_dec_lt(v___x_4008_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_dec(v___x_4008_);
return v_init_3988_;
}
else
{
uint8_t v___x_4011_; 
v___x_4011_ = lean_nat_dec_le(v___x_4009_, v___x_4009_);
if (v___x_4011_ == 0)
{
if (v___x_4010_ == 0)
{
lean_dec(v___x_4008_);
return v_init_3988_;
}
else
{
size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = lean_usize_of_nat(v___x_4008_);
lean_dec(v___x_4008_);
v___x_4013_ = lean_usize_of_nat(v___x_4009_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3993_, v___x_4012_, v___x_4013_, v_init_3988_);
return v___x_4014_;
}
}
else
{
size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_usize_of_nat(v___x_4008_);
lean_dec(v___x_4008_);
v___x_4016_ = lean_usize_of_nat(v___x_4009_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3993_, v___x_4015_, v___x_4016_, v_init_3988_);
return v___x_4017_;
}
}
}
}
else
{
lean_object* v_root_4018_; lean_object* v_tail_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v_root_4018_ = lean_ctor_get(v_t_3987_, 0);
v_tail_4019_ = lean_ctor_get(v_t_3987_, 1);
v___x_4020_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_4018_, v_init_3988_);
v___x_4021_ = lean_array_get_size(v_tail_4019_);
v___x_4022_ = lean_nat_dec_lt(v___x_3990_, v___x_4021_);
if (v___x_4022_ == 0)
{
return v___x_4020_;
}
else
{
uint8_t v___x_4023_; 
v___x_4023_ = lean_nat_dec_le(v___x_4021_, v___x_4021_);
if (v___x_4023_ == 0)
{
if (v___x_4022_ == 0)
{
return v___x_4020_;
}
else
{
size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = ((size_t)0ULL);
v___x_4025_ = lean_usize_of_nat(v___x_4021_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4019_, v___x_4024_, v___x_4025_, v___x_4020_);
return v___x_4026_;
}
}
else
{
size_t v___x_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = ((size_t)0ULL);
v___x_4028_ = lean_usize_of_nat(v___x_4021_);
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4019_, v___x_4027_, v___x_4028_, v___x_4020_);
return v___x_4029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_4030_, lean_object* v_init_4031_, lean_object* v_start_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_4030_, v_init_4031_, v_start_4032_);
lean_dec(v_start_4032_);
lean_dec_ref(v_t_4030_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_4034_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v_unreported_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4048_; 
v___x_4035_ = lean_unsigned_to_nat(32u);
v___x_4036_ = lean_mk_empty_array_with_capacity(v___x_4035_);
lean_dec_ref(v___x_4036_);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_4039_ = lean_ctor_get(v_log_4034_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_log_4034_);
if (v_isSharedCheck_4048_ == 0)
{
lean_object* v_unused_4049_; lean_object* v_unused_4050_; 
v_unused_4049_ = lean_ctor_get(v_log_4034_, 2);
lean_dec(v_unused_4049_);
v_unused_4050_ = lean_ctor_get(v_log_4034_, 0);
lean_dec(v_unused_4050_);
v___x_4041_ = v_log_4034_;
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_unreported_4039_);
lean_dec(v_log_4034_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4043_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_4039_, v___x_4038_, v___x_4037_);
lean_dec_ref(v_unreported_4039_);
v___x_4044_ = l_Lean_NameSet_empty;
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 2, v___x_4044_);
lean_ctor_set(v___x_4041_, 1, v___x_4043_);
lean_ctor_set(v___x_4041_, 0, v___x_4038_);
v___x_4046_ = v___x_4041_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4043_);
lean_ctor_set(v_reuseFailAlloc_4047_, 2, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_4051_, lean_object* v_log_4052_, lean_object* v_f_4053_){
_start:
{
lean_object* v_unreported_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_unreported_4054_ = lean_ctor_get(v_log_4052_, 1);
lean_inc_ref(v_unreported_4054_);
lean_dec_ref(v_log_4052_);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = l_Lean_PersistentArray_forM___redArg(v_inst_4051_, v_unreported_4054_, v_f_4053_, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_4057_, lean_object* v_inst_4058_, lean_object* v_log_4059_, lean_object* v_f_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_MessageLog_forM___redArg(v_inst_4058_, v_log_4059_, v_f_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_4062_){
_start:
{
lean_object* v_unreported_4063_; lean_object* v___x_4064_; 
v_unreported_4063_ = lean_ctor_get(v_log_4062_, 1);
v___x_4064_ = l_Lean_PersistentArray_toList___redArg(v_unreported_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_MessageLog_toList(v_log_4065_);
lean_dec_ref(v_log_4065_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4067_){
_start:
{
lean_object* v_unreported_4068_; lean_object* v___x_4069_; 
v_unreported_4068_ = lean_ctor_get(v_log_4067_, 1);
v___x_4069_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_MessageLog_toArray(v_log_4070_);
lean_dec_ref(v_log_4070_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4072_){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_unsigned_to_nat(2u);
v___x_4074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v_msg_4072_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4075_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v_msg_4075_);
v___x_4078_ = l_Lean_MessageData_nestD(v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4079_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = l_Lean_MessageData_ofExpr(v_e_4079_);
v___x_4081_ = l_Lean_indentD(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4082_, lean_object* v_msg_4083_){
_start:
{
lean_object* v_env_4085_; lean_object* v_mctx_4086_; lean_object* v_lctx_4087_; lean_object* v_opts_4088_; lean_object* v_currNamespace_4089_; lean_object* v_openDecls_4090_; lean_object* v___x_4091_; lean_object* v_msg_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_env_4085_ = lean_ctor_get(v_ctx_4082_, 0);
v_mctx_4086_ = lean_ctor_get(v_ctx_4082_, 1);
v_lctx_4087_ = lean_ctor_get(v_ctx_4082_, 2);
v_opts_4088_ = lean_ctor_get(v_ctx_4082_, 3);
v_currNamespace_4089_ = lean_ctor_get(v_ctx_4082_, 4);
v_openDecls_4090_ = lean_ctor_get(v_ctx_4082_, 5);
lean_inc(v_openDecls_4090_);
lean_inc(v_currNamespace_4089_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_currNamespace_4089_);
lean_ctor_set(v___x_4091_, 1, v_openDecls_4090_);
v_msg_4092_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4092_, 0, v___x_4091_);
lean_ctor_set(v_msg_4092_, 1, v_msg_4083_);
lean_inc_ref(v_opts_4088_);
lean_inc_ref(v_lctx_4087_);
lean_inc_ref(v_mctx_4086_);
lean_inc_ref(v_env_4085_);
v___x_4093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4093_, 0, v_env_4085_);
lean_ctor_set(v___x_4093_, 1, v_mctx_4086_);
lean_ctor_set(v___x_4093_, 2, v_lctx_4087_);
lean_ctor_set(v___x_4093_, 3, v_opts_4088_);
v___x_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
v___x_4095_ = l_Lean_MessageData_format(v_msg_4092_, v___x_4094_);
v___x_4096_ = l_Std_Format_defWidth;
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = l_Std_Format_pretty(v___x_4095_, v___x_4096_, v___x_4097_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4099_, lean_object* v_msg_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4099_, v_msg_4100_);
lean_dec_ref(v_ctx_4099_);
return v_res_4102_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4103_, lean_object* v_a_4104_, uint8_t v_b_4105_){
_start:
{
lean_object* v_str_4106_; lean_object* v_startInclusive_4107_; lean_object* v_endExclusive_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v_str_4106_ = lean_ctor_get(v_s_4103_, 0);
v_startInclusive_4107_ = lean_ctor_get(v_s_4103_, 1);
v_endExclusive_4108_ = lean_ctor_get(v_s_4103_, 2);
v___x_4109_ = lean_nat_sub(v_endExclusive_4108_, v_startInclusive_4107_);
v___x_4110_ = lean_nat_dec_eq(v_a_4104_, v___x_4109_);
lean_dec(v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; uint32_t v___x_4112_; uint32_t v___x_4113_; uint8_t v___x_4114_; 
v___x_4111_ = lean_nat_add(v_startInclusive_4107_, v_a_4104_);
lean_dec(v_a_4104_);
v___x_4112_ = lean_string_utf8_get_fast(v_str_4106_, v___x_4111_);
v___x_4113_ = 10;
v___x_4114_ = lean_uint32_dec_eq(v___x_4112_, v___x_4113_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = lean_string_utf8_next_fast(v_str_4106_, v___x_4111_);
lean_dec(v___x_4111_);
v___x_4116_ = lean_nat_sub(v___x_4115_, v_startInclusive_4107_);
v_a_4104_ = v___x_4116_;
v_b_4105_ = v___x_4114_;
goto _start;
}
else
{
lean_dec(v___x_4111_);
return v___x_4114_;
}
}
else
{
lean_dec(v_a_4104_);
return v_b_4105_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4118_, lean_object* v_a_4119_, lean_object* v_b_4120_){
_start:
{
uint8_t v_b_boxed_4121_; uint8_t v_res_4122_; lean_object* v_r_4123_; 
v_b_boxed_4121_ = lean_unbox(v_b_4120_);
v_res_4122_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4118_, v_a_4119_, v_b_boxed_4121_);
lean_dec_ref(v_s_4118_);
v_r_4123_ = lean_box(v_res_4122_);
return v_r_4123_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4124_){
_start:
{
lean_object* v_searcher_4125_; uint8_t v___x_4126_; uint8_t v___x_4127_; 
v_searcher_4125_ = lean_unsigned_to_nat(0u);
v___x_4126_ = 0;
v___x_4127_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4124_, v_searcher_4125_, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4128_){
_start:
{
uint8_t v_res_4129_; lean_object* v_r_4130_; 
v_res_4129_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4128_);
lean_dec_ref(v_s_4128_);
v_r_4130_ = lean_box(v_res_4129_);
return v_r_4130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4131_, lean_object* v_val_4132_, lean_object* v_a_4133_, lean_object* v_b_4134_){
_start:
{
lean_object* v_startInclusive_4135_; lean_object* v_endExclusive_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v_startInclusive_4135_ = lean_ctor_get(v___x_4131_, 1);
v_endExclusive_4136_ = lean_ctor_get(v___x_4131_, 2);
v___x_4137_ = lean_nat_sub(v_endExclusive_4136_, v_startInclusive_4135_);
v___x_4138_ = lean_nat_dec_eq(v_a_4133_, v___x_4137_);
lean_dec(v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = lean_string_utf8_next_fast(v_val_4132_, v_a_4133_);
lean_dec(v_a_4133_);
v___x_4140_ = lean_unsigned_to_nat(1u);
v___x_4141_ = lean_nat_add(v_b_4134_, v___x_4140_);
lean_dec(v_b_4134_);
v_a_4133_ = v___x_4139_;
v_b_4134_ = v___x_4141_;
goto _start;
}
else
{
lean_dec(v_a_4133_);
return v_b_4134_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4143_, lean_object* v_val_4144_, lean_object* v_a_4145_, lean_object* v_b_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4143_, v_val_4144_, v_a_4145_, v_b_4146_);
lean_dec_ref(v_val_4144_);
lean_dec_ref(v___x_4143_);
return v_res_4147_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_4152_ = l_Lean_MessageData_ofFormat(v___x_4151_);
return v___x_4152_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_4157_ = l_Lean_MessageData_ofFormat(v___x_4156_);
return v___x_4157_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4159_ = l_Lean_MessageData_ofFormat(v___x_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4160_, lean_object* v_maxInlineLength_4161_, lean_object* v_ctx_4162_){
_start:
{
lean_object* v_msg_4164_; lean_object* v___x_4165_; uint8_t v___y_4167_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_msg_4164_ = l_Lean_MessageData_ofExpr(v_e_4160_);
lean_inc_ref(v_msg_4164_);
v___x_4165_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4162_, v_msg_4164_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = lean_string_utf8_byte_size(v___x_4165_);
lean_inc_ref(v___x_4165_);
v___x_4177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4165_);
lean_ctor_set(v___x_4177_, 1, v___x_4175_);
lean_ctor_set(v___x_4177_, 2, v___x_4176_);
v___x_4178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4177_, v___x_4165_, v___x_4175_, v___x_4175_);
lean_dec_ref(v___x_4165_);
v___x_4179_ = lean_nat_dec_lt(v_maxInlineLength_4161_, v___x_4178_);
lean_dec(v___x_4178_);
if (v___x_4179_ == 0)
{
uint8_t v___x_4180_; 
v___x_4180_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4177_);
lean_dec_ref_known(v___x_4177_, 3);
v___y_4167_ = v___x_4180_;
goto v___jp_4166_;
}
else
{
lean_dec_ref_known(v___x_4177_, 3);
v___y_4167_ = v___x_4179_;
goto v___jp_4166_;
}
v___jp_4166_:
{
if (v___y_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v_msg_4164_);
v___x_4170_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
return v___x_4171_;
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = l_Lean_indentD(v_msg_4164_);
v___x_4173_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4181_, lean_object* v_maxInlineLength_4182_, lean_object* v_ctx_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_inlineExpr___lam__0(v_e_4181_, v_maxInlineLength_4182_, v_ctx_4183_);
lean_dec_ref(v_ctx_4183_);
lean_dec(v_maxInlineLength_4182_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4186_, lean_object* v_x_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4189_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4190_ = l_Lean_MessageData_ofExpr(v_e_4186_);
v___x_4191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4191_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4194_, lean_object* v_x_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_inlineExpr___lam__2(v_e_4194_, v_x_4195_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4198_, lean_object* v_maxInlineLength_4199_){
_start:
{
lean_object* v___f_4200_; lean_object* v___f_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; 
lean_inc_ref_n(v_e_4198_, 2);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4200_, 0, v_e_4198_);
lean_closure_set(v___f_4200_, 1, v_maxInlineLength_4199_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4201_, 0, v_e_4198_);
v___f_4202_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4202_, 0, v_e_4198_);
v___x_4203_ = l_Lean_MessageData_lazy(v___f_4200_, v___f_4201_, v___f_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4204_, lean_object* v_val_4205_, lean_object* v_inst_4206_, lean_object* v_R_4207_, lean_object* v_a_4208_, lean_object* v_b_4209_, lean_object* v_c_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4204_, v_val_4205_, v_a_4208_, v_b_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4212_, lean_object* v_val_4213_, lean_object* v_inst_4214_, lean_object* v_R_4215_, lean_object* v_a_4216_, lean_object* v_b_4217_, lean_object* v_c_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4212_, v_val_4213_, v_inst_4214_, v_R_4215_, v_a_4216_, v_b_4217_, v_c_4218_);
lean_dec_ref(v_val_4213_);
lean_dec_ref(v___x_4212_);
return v_res_4219_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4220_, lean_object* v_inst_4221_, lean_object* v_R_4222_, lean_object* v_a_4223_, uint8_t v_b_4224_, lean_object* v_c_4225_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4220_, v_a_4223_, v_b_4224_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4227_, lean_object* v_inst_4228_, lean_object* v_R_4229_, lean_object* v_a_4230_, lean_object* v_b_4231_, lean_object* v_c_4232_){
_start:
{
uint8_t v_b_boxed_4233_; uint8_t v_res_4234_; lean_object* v_r_4235_; 
v_b_boxed_4233_ = lean_unbox(v_b_4231_);
v_res_4234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4227_, v_inst_4228_, v_R_4229_, v_a_4230_, v_b_boxed_4233_, v_c_4232_);
lean_dec_ref(v_s_4227_);
v_r_4235_ = lean_box(v_res_4234_);
return v_r_4235_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4240_ = l_Lean_MessageData_ofFormat(v___x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4241_, lean_object* v_maxInlineLength_4242_, lean_object* v_ctx_4243_){
_start:
{
lean_object* v_msg_4245_; lean_object* v___x_4246_; uint8_t v___y_4248_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_msg_4245_ = l_Lean_MessageData_ofExpr(v_e_4241_);
lean_inc_ref(v_msg_4245_);
v___x_4246_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4243_, v_msg_4245_);
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = lean_string_utf8_byte_size(v___x_4246_);
lean_inc_ref(v___x_4246_);
v___x_4256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4246_);
lean_ctor_set(v___x_4256_, 1, v___x_4254_);
lean_ctor_set(v___x_4256_, 2, v___x_4255_);
v___x_4257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4256_, v___x_4246_, v___x_4254_, v___x_4254_);
lean_dec_ref(v___x_4246_);
v___x_4258_ = lean_nat_dec_lt(v_maxInlineLength_4242_, v___x_4257_);
lean_dec(v___x_4257_);
if (v___x_4258_ == 0)
{
uint8_t v___x_4259_; 
v___x_4259_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4256_);
lean_dec_ref_known(v___x_4256_, 3);
v___y_4248_ = v___x_4259_;
goto v___jp_4247_;
}
else
{
lean_dec_ref_known(v___x_4256_, 3);
v___y_4248_ = v___x_4258_;
goto v___jp_4247_;
}
v___jp_4247_:
{
if (v___y_4248_ == 0)
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4249_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
lean_ctor_set(v___x_4250_, 1, v_msg_4245_);
v___x_4251_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
return v___x_4252_;
}
else
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_indentD(v_msg_4245_);
return v___x_4253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4260_, lean_object* v_maxInlineLength_4261_, lean_object* v_ctx_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_inlineExprTrailing___lam__0(v_e_4260_, v_maxInlineLength_4261_, v_ctx_4262_);
lean_dec_ref(v_ctx_4262_);
lean_dec(v_maxInlineLength_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4265_, lean_object* v_x_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4268_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4269_ = l_Lean_MessageData_ofExpr(v_e_4265_);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4268_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_inlineExprTrailing___lam__2(v_e_4273_, v_x_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4277_, lean_object* v_maxInlineLength_4278_){
_start:
{
lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___x_4282_; 
lean_inc_ref_n(v_e_4277_, 2);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4279_, 0, v_e_4277_);
lean_closure_set(v___f_4279_, 1, v_maxInlineLength_4278_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4280_, 0, v_e_4277_);
v___f_4281_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4281_, 0, v_e_4277_);
v___x_4282_ = l_Lean_MessageData_lazy(v___f_4279_, v___f_4280_, v___f_4281_);
return v___x_4282_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4287_ = l_Lean_MessageData_ofFormat(v___x_4286_);
return v___x_4287_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4292_ = l_Lean_MessageData_ofFormat(v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4293_){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4294_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
lean_ctor_set(v___x_4295_, 1, v_msg_4293_);
v___x_4296_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4298_, lean_object* v_inst_4299_, lean_object* v_msg_4300_){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = lean_apply_1(v_inst_4298_, v_msg_4300_);
v___x_4302_ = lean_apply_2(v_inst_4299_, lean_box(0), v___x_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4303_, lean_object* v_inst_4304_){
_start:
{
lean_object* v___f_4305_; 
v___f_4305_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4305_, 0, v_inst_4304_);
lean_closure_set(v___f_4305_, 1, v_inst_4303_);
return v___f_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4306_, lean_object* v_n_4307_, lean_object* v_inst_4308_, lean_object* v_inst_4309_){
_start:
{
lean_object* v___f_4310_; 
v___f_4310_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4310_, 0, v_inst_4309_);
lean_closure_set(v___f_4310_, 1, v_inst_4308_);
return v___f_4310_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = lean_unsigned_to_nat(32u);
v___x_4312_ = lean_mk_empty_array_with_capacity(v___x_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4314_ = ((size_t)5ULL);
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = lean_unsigned_to_nat(32u);
v___x_4317_ = lean_mk_empty_array_with_capacity(v___x_4316_);
v___x_4318_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v___x_4317_);
lean_ctor_set(v___x_4319_, 2, v___x_4315_);
lean_ctor_set(v___x_4319_, 3, v___x_4315_);
lean_ctor_set_usize(v___x_4319_, 4, v___x_4314_);
return v___x_4319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4320_ = lean_box(1);
v___x_4321_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4322_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
lean_ctor_set(v___x_4323_, 1, v___x_4321_);
lean_ctor_set(v___x_4323_, 2, v___x_4320_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4324_, lean_object* v_msgData_4325_, lean_object* v_toPure_4326_, lean_object* v_opts_4327_){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4328_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4329_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4330_, 0, v_env_4324_);
lean_ctor_set(v___x_4330_, 1, v___x_4328_);
lean_ctor_set(v___x_4330_, 2, v___x_4329_);
lean_ctor_set(v___x_4330_, 3, v_opts_4327_);
v___x_4331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
lean_ctor_set(v___x_4331_, 1, v_msgData_4325_);
v___x_4332_ = lean_apply_2(v_toPure_4326_, lean_box(0), v___x_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4333_, lean_object* v_toPure_4334_, lean_object* v_toBind_4335_, lean_object* v_inst_4336_, lean_object* v_env_4337_){
_start:
{
lean_object* v___f_4338_; lean_object* v___x_4339_; 
v___f_4338_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4338_, 0, v_env_4337_);
lean_closure_set(v___f_4338_, 1, v_msgData_4333_);
lean_closure_set(v___f_4338_, 2, v_toPure_4334_);
v___x_4339_ = lean_apply_4(v_toBind_4335_, lean_box(0), lean_box(0), v_inst_4336_, v___f_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4340_, lean_object* v_inst_4341_, lean_object* v_inst_4342_, lean_object* v_msgData_4343_){
_start:
{
lean_object* v_toApplicative_4344_; lean_object* v_toBind_4345_; lean_object* v_getEnv_4346_; lean_object* v_toPure_4347_; lean_object* v___f_4348_; lean_object* v___x_4349_; 
v_toApplicative_4344_ = lean_ctor_get(v_inst_4340_, 0);
lean_inc_ref(v_toApplicative_4344_);
v_toBind_4345_ = lean_ctor_get(v_inst_4340_, 1);
lean_inc_n(v_toBind_4345_, 2);
lean_dec_ref(v_inst_4340_);
v_getEnv_4346_ = lean_ctor_get(v_inst_4341_, 0);
lean_inc(v_getEnv_4346_);
lean_dec_ref(v_inst_4341_);
v_toPure_4347_ = lean_ctor_get(v_toApplicative_4344_, 1);
lean_inc(v_toPure_4347_);
lean_dec_ref(v_toApplicative_4344_);
v___f_4348_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4348_, 0, v_msgData_4343_);
lean_closure_set(v___f_4348_, 1, v_toPure_4347_);
lean_closure_set(v___f_4348_, 2, v_toBind_4345_);
lean_closure_set(v___f_4348_, 3, v_inst_4342_);
v___x_4349_ = lean_apply_4(v_toBind_4345_, lean_box(0), lean_box(0), v_getEnv_4346_, v___f_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4350_, lean_object* v_inst_4351_, lean_object* v_inst_4352_, lean_object* v_inst_4353_, lean_object* v_msgData_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Lean_addMessageContextPartial___redArg(v_inst_4351_, v_inst_4352_, v_inst_4353_, v_msgData_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4356_, lean_object* v_mctx_4357_, lean_object* v_lctx_4358_, lean_object* v_msgData_4359_, lean_object* v_toPure_4360_, lean_object* v_opts_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4362_, 0, v_env_4356_);
lean_ctor_set(v___x_4362_, 1, v_mctx_4357_);
lean_ctor_set(v___x_4362_, 2, v_lctx_4358_);
lean_ctor_set(v___x_4362_, 3, v_opts_4361_);
v___x_4363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set(v___x_4363_, 1, v_msgData_4359_);
v___x_4364_ = lean_apply_2(v_toPure_4360_, lean_box(0), v___x_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4365_, lean_object* v_mctx_4366_, lean_object* v_msgData_4367_, lean_object* v_toPure_4368_, lean_object* v_toBind_4369_, lean_object* v_inst_4370_, lean_object* v_lctx_4371_){
_start:
{
lean_object* v___f_4372_; lean_object* v___x_4373_; 
v___f_4372_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4372_, 0, v_env_4365_);
lean_closure_set(v___f_4372_, 1, v_mctx_4366_);
lean_closure_set(v___f_4372_, 2, v_lctx_4371_);
lean_closure_set(v___f_4372_, 3, v_msgData_4367_);
lean_closure_set(v___f_4372_, 4, v_toPure_4368_);
v___x_4373_ = lean_apply_4(v_toBind_4369_, lean_box(0), lean_box(0), v_inst_4370_, v___f_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4374_, lean_object* v_msgData_4375_, lean_object* v_toPure_4376_, lean_object* v_toBind_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_mctx_4380_){
_start:
{
lean_object* v___f_4381_; lean_object* v___x_4382_; 
lean_inc(v_toBind_4377_);
v___f_4381_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4381_, 0, v_env_4374_);
lean_closure_set(v___f_4381_, 1, v_mctx_4380_);
lean_closure_set(v___f_4381_, 2, v_msgData_4375_);
lean_closure_set(v___f_4381_, 3, v_toPure_4376_);
lean_closure_set(v___f_4381_, 4, v_toBind_4377_);
lean_closure_set(v___f_4381_, 5, v_inst_4378_);
v___x_4382_ = lean_apply_4(v_toBind_4377_, lean_box(0), lean_box(0), v_inst_4379_, v___f_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4383_, lean_object* v_msgData_4384_, lean_object* v_toPure_4385_, lean_object* v_toBind_4386_, lean_object* v_inst_4387_, lean_object* v_inst_4388_, lean_object* v_env_4389_){
_start:
{
lean_object* v_getMCtx_4390_; lean_object* v___f_4391_; lean_object* v___x_4392_; 
v_getMCtx_4390_ = lean_ctor_get(v_inst_4383_, 0);
lean_inc(v_getMCtx_4390_);
lean_dec_ref(v_inst_4383_);
lean_inc(v_toBind_4386_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4391_, 0, v_env_4389_);
lean_closure_set(v___f_4391_, 1, v_msgData_4384_);
lean_closure_set(v___f_4391_, 2, v_toPure_4385_);
lean_closure_set(v___f_4391_, 3, v_toBind_4386_);
lean_closure_set(v___f_4391_, 4, v_inst_4387_);
lean_closure_set(v___f_4391_, 5, v_inst_4388_);
v___x_4392_ = lean_apply_4(v_toBind_4386_, lean_box(0), lean_box(0), v_getMCtx_4390_, v___f_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_inst_4395_, lean_object* v_inst_4396_, lean_object* v_inst_4397_, lean_object* v_msgData_4398_){
_start:
{
lean_object* v_toApplicative_4399_; lean_object* v_toBind_4400_; lean_object* v_getEnv_4401_; lean_object* v_toPure_4402_; lean_object* v___f_4403_; lean_object* v___x_4404_; 
v_toApplicative_4399_ = lean_ctor_get(v_inst_4393_, 0);
lean_inc_ref(v_toApplicative_4399_);
v_toBind_4400_ = lean_ctor_get(v_inst_4393_, 1);
lean_inc_n(v_toBind_4400_, 2);
lean_dec_ref(v_inst_4393_);
v_getEnv_4401_ = lean_ctor_get(v_inst_4394_, 0);
lean_inc(v_getEnv_4401_);
lean_dec_ref(v_inst_4394_);
v_toPure_4402_ = lean_ctor_get(v_toApplicative_4399_, 1);
lean_inc(v_toPure_4402_);
lean_dec_ref(v_toApplicative_4399_);
v___f_4403_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4403_, 0, v_inst_4395_);
lean_closure_set(v___f_4403_, 1, v_msgData_4398_);
lean_closure_set(v___f_4403_, 2, v_toPure_4402_);
lean_closure_set(v___f_4403_, 3, v_toBind_4400_);
lean_closure_set(v___f_4403_, 4, v_inst_4397_);
lean_closure_set(v___f_4403_, 5, v_inst_4396_);
v___x_4404_ = lean_apply_4(v_toBind_4400_, lean_box(0), lean_box(0), v_getEnv_4401_, v___f_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4405_, lean_object* v_inst_4406_, lean_object* v_inst_4407_, lean_object* v_inst_4408_, lean_object* v_inst_4409_, lean_object* v_inst_4410_, lean_object* v_msgData_4411_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_addMessageContextFull___redArg(v_inst_4406_, v_inst_4407_, v_inst_4408_, v_inst_4409_, v_inst_4410_, v_msgData_4411_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4415_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4417_);
lean_dec_ref(v_s_4417_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4419_, lean_object* v___x_4420_, lean_object* v___x_4421_, lean_object* v_a_4422_, lean_object* v_b_4423_){
_start:
{
lean_object* v_it_4425_; lean_object* v_startInclusive_4426_; lean_object* v_endExclusive_4427_; 
if (lean_obj_tag(v_a_4422_) == 0)
{
lean_object* v_currPos_4433_; lean_object* v_searcher_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4460_; 
v_currPos_4433_ = lean_ctor_get(v_a_4422_, 0);
v_searcher_4434_ = lean_ctor_get(v_a_4422_, 1);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_a_4422_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4436_ = v_a_4422_;
v_isShared_4437_ = v_isSharedCheck_4460_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_searcher_4434_);
lean_inc(v_currPos_4433_);
lean_dec(v_a_4422_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4460_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_startInclusive_4438_; lean_object* v_endExclusive_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v_startInclusive_4438_ = lean_ctor_get(v___x_4420_, 1);
v_endExclusive_4439_ = lean_ctor_get(v___x_4420_, 2);
v___x_4440_ = lean_nat_sub(v_endExclusive_4439_, v_startInclusive_4438_);
v___x_4441_ = lean_nat_dec_eq(v_searcher_4434_, v___x_4440_);
lean_dec(v___x_4440_);
if (v___x_4441_ == 0)
{
uint32_t v___x_4442_; uint32_t v___x_4443_; uint8_t v___x_4444_; 
v___x_4442_ = 10;
v___x_4443_ = lean_string_utf8_get_fast(v_str_4419_, v_searcher_4434_);
v___x_4444_ = lean_uint32_dec_eq(v___x_4443_, v___x_4442_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
v___x_4445_ = lean_string_utf8_next_fast(v_str_4419_, v_searcher_4434_);
lean_dec(v_searcher_4434_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 1, v___x_4445_);
v___x_4447_ = v___x_4436_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_currPos_4433_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
v_a_4422_ = v___x_4447_;
goto _start;
}
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v_slice_4453_; lean_object* v_nextIt_4455_; 
v___x_4450_ = lean_string_utf8_next_fast(v_str_4419_, v_searcher_4434_);
v___x_4451_ = lean_nat_sub(v___x_4450_, v_searcher_4434_);
v___x_4452_ = lean_nat_add(v_searcher_4434_, v___x_4451_);
lean_dec(v___x_4451_);
v_slice_4453_ = l_String_Slice_subslice_x21(v___x_4420_, v_currPos_4433_, v_searcher_4434_);
lean_inc(v___x_4452_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 1, v___x_4452_);
lean_ctor_set(v___x_4436_, 0, v___x_4452_);
v_nextIt_4455_ = v___x_4436_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v___x_4452_);
v_nextIt_4455_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v_startInclusive_4456_; lean_object* v_endExclusive_4457_; 
v_startInclusive_4456_ = lean_ctor_get(v_slice_4453_, 0);
lean_inc(v_startInclusive_4456_);
v_endExclusive_4457_ = lean_ctor_get(v_slice_4453_, 1);
lean_inc(v_endExclusive_4457_);
lean_dec_ref(v_slice_4453_);
v_it_4425_ = v_nextIt_4455_;
v_startInclusive_4426_ = v_startInclusive_4456_;
v_endExclusive_4427_ = v_endExclusive_4457_;
goto v___jp_4424_;
}
}
}
else
{
lean_object* v___x_4459_; 
lean_del_object(v___x_4436_);
lean_dec(v_searcher_4434_);
v___x_4459_ = lean_box(1);
lean_inc(v___x_4421_);
v_it_4425_ = v___x_4459_;
v_startInclusive_4426_ = v_currPos_4433_;
v_endExclusive_4427_ = v___x_4421_;
goto v___jp_4424_;
}
}
}
else
{
lean_dec(v___x_4421_);
return v_b_4423_;
}
v___jp_4424_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4428_ = lean_string_utf8_extract(v_str_4419_, v_startInclusive_4426_, v_endExclusive_4427_);
lean_dec(v_endExclusive_4427_);
lean_dec(v_startInclusive_4426_);
v___x_4429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
v___x_4430_ = l_Lean_MessageData_ofFormat(v___x_4429_);
v___x_4431_ = lean_array_push(v_b_4423_, v___x_4430_);
v_a_4422_ = v_it_4425_;
v_b_4423_ = v___x_4431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4461_, lean_object* v___x_4462_, lean_object* v___x_4463_, lean_object* v_a_4464_, lean_object* v_b_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4461_, v___x_4462_, v___x_4463_, v_a_4464_, v_b_4465_);
lean_dec_ref(v___x_4462_);
lean_dec_ref(v_str_4461_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4469_){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_lines_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = lean_string_utf8_byte_size(v_str_4469_);
lean_inc_ref(v_str_4469_);
v___x_4472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4472_, 0, v_str_4469_);
lean_ctor_set(v___x_4472_, 1, v___x_4470_);
lean_ctor_set(v___x_4472_, 2, v___x_4471_);
v_lines_4473_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4472_);
v___x_4474_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4475_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4469_, v___x_4472_, v___x_4471_, v_lines_4473_, v___x_4474_);
lean_dec_ref_known(v___x_4472_, 3);
lean_dec_ref(v_str_4469_);
v___x_4476_ = lean_array_to_list(v___x_4475_);
v___x_4477_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4478_ = l_Lean_MessageData_joinSep(v___x_4476_, v___x_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4479_, lean_object* v___x_4480_, lean_object* v___x_4481_, lean_object* v_inst_4482_, lean_object* v_R_4483_, lean_object* v_a_4484_, lean_object* v_b_4485_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4479_, v___x_4480_, v___x_4481_, v_a_4484_, v_b_4485_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4487_, lean_object* v___x_4488_, lean_object* v___x_4489_, lean_object* v_inst_4490_, lean_object* v_R_4491_, lean_object* v_a_4492_, lean_object* v_b_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4487_, v___x_4488_, v___x_4489_, v_inst_4490_, v_R_4491_, v_a_4492_, v_b_4493_);
lean_dec_ref(v___x_4488_);
lean_dec_ref(v_str_4487_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4495_){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4496_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4497_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4497_, 0, lean_box(0));
lean_closure_set(v___x_4497_, 1, lean_box(0));
lean_closure_set(v___x_4497_, 2, lean_box(0));
lean_closure_set(v___x_4497_, 3, v___x_4496_);
lean_closure_set(v___x_4497_, 4, v_inst_4495_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4498_, lean_object* v_inst_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4507_){
_start:
{
lean_object* v___f_4508_; 
v___f_4508_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_instToMessageDataTSyntax(v_k_4509_);
lean_dec(v_k_4509_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4515_, lean_object* v_as_4516_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = lean_box(0);
v___x_4518_ = l_List_mapTR_loop___redArg(v_inst_4515_, v_as_4516_, v___x_4517_);
v___x_4519_ = l_Lean_MessageData_ofList(v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4520_){
_start:
{
lean_object* v___f_4521_; 
v___f_4521_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4521_, 0, v_inst_4520_);
return v___f_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4522_, lean_object* v_inst_4523_){
_start:
{
lean_object* v___f_4524_; 
v___f_4524_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4524_, 0, v_inst_4523_);
return v___f_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4525_, lean_object* v_as_4526_){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4527_ = lean_array_to_list(v_as_4526_);
v___x_4528_ = lean_box(0);
v___x_4529_ = l_List_mapTR_loop___redArg(v_inst_4525_, v___x_4527_, v___x_4528_);
v___x_4530_ = l_Lean_MessageData_ofList(v___x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4531_){
_start:
{
lean_object* v___f_4532_; 
v___f_4532_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4532_, 0, v_inst_4531_);
return v___f_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4533_, lean_object* v_inst_4534_){
_start:
{
lean_object* v___f_4535_; 
v___f_4535_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4535_, 0, v_inst_4534_);
return v___f_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4536_, lean_object* v_acc_4537_, lean_object* v_recur_4538_){
_start:
{
lean_object* v_array_4539_; lean_object* v_start_4540_; lean_object* v_stop_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4554_; 
v_array_4539_ = lean_ctor_get(v_it_4536_, 0);
v_start_4540_ = lean_ctor_get(v_it_4536_, 1);
v_stop_4541_ = lean_ctor_get(v_it_4536_, 2);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_it_4536_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4543_ = v_it_4536_;
v_isShared_4544_ = v_isSharedCheck_4554_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_stop_4541_);
lean_inc(v_start_4540_);
lean_inc(v_array_4539_);
lean_dec(v_it_4536_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4554_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_nat_dec_lt(v_start_4540_, v_stop_4541_);
if (v___x_4545_ == 0)
{
lean_del_object(v___x_4543_);
lean_dec(v_stop_4541_);
lean_dec(v_start_4540_);
lean_dec_ref(v_array_4539_);
lean_dec_ref(v_recur_4538_);
return v_acc_4537_;
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4546_ = lean_unsigned_to_nat(1u);
v___x_4547_ = lean_nat_add(v_start_4540_, v___x_4546_);
lean_inc_ref(v_array_4539_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 1, v___x_4547_);
v___x_4549_ = v___x_4543_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_array_4539_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_stop_4541_);
v___x_4549_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = lean_array_fget(v_array_4539_, v_start_4540_);
lean_dec(v_start_4540_);
lean_dec_ref(v_array_4539_);
v___x_4551_ = lean_array_push(v_acc_4537_, v___x_4550_);
v___x_4552_ = lean_apply_3(v_recur_4538_, v___x_4549_, v___x_4551_, lean_box(0));
return v___x_4552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4557_, lean_object* v_inst_4558_, lean_object* v_as_4559_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4560_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4561_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4557_, v_as_4559_, v___x_4560_);
v___x_4562_ = lean_array_to_list(v___x_4561_);
v___x_4563_ = lean_box(0);
v___x_4564_ = l_List_mapTR_loop___redArg(v_inst_4558_, v___x_4562_, v___x_4563_);
v___x_4565_ = l_Lean_MessageData_ofList(v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4567_){
_start:
{
lean_object* v___f_4568_; lean_object* v___f_4569_; 
v___f_4568_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4569_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4569_, 0, v___f_4568_);
lean_closure_set(v___f_4569_, 1, v_inst_4567_);
return v___f_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4570_, lean_object* v_inst_4571_){
_start:
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4577_ = l_Lean_MessageData_ofFormat(v___x_4576_);
return v___x_4577_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4580_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4581_ = l_Lean_MessageData_ofFormat(v___x_4580_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4582_, lean_object* v_x_4583_){
_start:
{
if (lean_obj_tag(v_x_4583_) == 0)
{
lean_object* v___x_4584_; 
lean_dec_ref(v_inst_4582_);
v___x_4584_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4584_;
}
else
{
lean_object* v_val_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v_val_4585_ = lean_ctor_get(v_x_4583_, 0);
lean_inc(v_val_4585_);
lean_dec_ref_known(v_x_4583_, 1);
v___x_4586_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4587_ = lean_apply_1(v_inst_4582_, v_val_4585_);
v___x_4588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4588_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
return v___x_4590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4591_){
_start:
{
lean_object* v___f_4592_; 
v___f_4592_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4592_, 0, v_inst_4591_);
return v___f_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4593_, lean_object* v_inst_4594_){
_start:
{
lean_object* v___f_4595_; 
v___f_4595_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4595_, 0, v_inst_4594_);
return v___f_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4596_, lean_object* v_inst_4597_, lean_object* v_x_4598_){
_start:
{
lean_object* v_fst_4599_; lean_object* v_snd_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4614_; 
v_fst_4599_ = lean_ctor_get(v_x_4598_, 0);
v_snd_4600_ = lean_ctor_get(v_x_4598_, 1);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_x_4598_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4602_ = v_x_4598_;
v_isShared_4603_ = v_isSharedCheck_4614_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_snd_4600_);
lean_inc(v_fst_4599_);
lean_dec(v_x_4598_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4614_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4604_ = lean_apply_1(v_inst_4596_, v_fst_4599_);
v___x_4605_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4603_ == 0)
{
lean_ctor_set_tag(v___x_4602_, 7);
lean_ctor_set(v___x_4602_, 1, v___x_4605_);
lean_ctor_set(v___x_4602_, 0, v___x_4604_);
v___x_4607_ = v___x_4602_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4608_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4607_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = lean_apply_1(v_inst_4597_, v_snd_4600_);
v___x_4611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = l_Lean_MessageData_paren(v___x_4611_);
return v___x_4612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4615_, lean_object* v_inst_4616_){
_start:
{
lean_object* v___f_4617_; 
v___f_4617_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4617_, 0, v_inst_4615_);
lean_closure_set(v___f_4617_, 1, v_inst_4616_);
return v___f_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4618_, lean_object* v_00_u03b2_4619_, lean_object* v_inst_4620_, lean_object* v_inst_4621_){
_start:
{
lean_object* v___f_4622_; 
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4622_, 0, v_inst_4620_);
lean_closure_set(v___f_4622_, 1, v_inst_4621_);
return v___f_4622_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4627_ = l_Lean_MessageData_ofFormat(v___x_4626_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4628_){
_start:
{
if (lean_obj_tag(v_x_4628_) == 0)
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4629_;
}
else
{
lean_object* v_val_4630_; lean_object* v___x_4631_; 
v_val_4630_ = lean_ctor_get(v_x_4628_, 0);
lean_inc(v_val_4630_);
lean_dec_ref_known(v_x_4628_, 1);
v___x_4631_ = l_Lean_MessageData_ofExpr(v_val_4630_);
return v___x_4631_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_138_));
v___x_4666_ = l_String_toRawSubstring_x27(v___x_4665_);
return v___x_4666_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4682_ = l_String_toRawSubstring_x27(v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4699_; uint8_t v___x_4700_; 
v___x_4699_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4696_);
v___x_4700_ = l_Lean_Syntax_isOfKind(v_x_4696_, v___x_4699_);
if (v___x_4700_ == 0)
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
lean_dec(v_x_4696_);
v___x_4701_ = lean_box(1);
v___x_4702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
lean_ctor_set(v___x_4702_, 1, v_a_4698_);
return v___x_4702_;
}
else
{
lean_object* v_quotContext_4703_; lean_object* v_currMacroScope_4704_; lean_object* v_ref_4705_; lean_object* v___x_4706_; lean_object* v_interpStr_4707_; uint8_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v_quotContext_4703_ = lean_ctor_get(v_a_4697_, 1);
v_currMacroScope_4704_ = lean_ctor_get(v_a_4697_, 2);
v_ref_4705_ = lean_ctor_get(v_a_4697_, 5);
v___x_4706_ = lean_unsigned_to_nat(1u);
v_interpStr_4707_ = l_Lean_Syntax_getArg(v_x_4696_, v___x_4706_);
lean_dec(v_x_4696_);
v___x_4708_ = 0;
v___x_4709_ = l_Lean_SourceInfo_fromRef(v_ref_4705_, v___x_4708_);
v___x_4710_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4711_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4704_, 2);
lean_inc_n(v_quotContext_4703_, 2);
v___x_4712_ = l_Lean_addMacroScope(v_quotContext_4703_, v___x_4711_, v_currMacroScope_4704_);
v___x_4713_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4709_);
v___x_4714_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4709_);
lean_ctor_set(v___x_4714_, 1, v___x_4710_);
lean_ctor_set(v___x_4714_, 2, v___x_4712_);
lean_ctor_set(v___x_4714_, 3, v___x_4713_);
v___x_4715_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4716_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4717_ = l_Lean_addMacroScope(v_quotContext_4703_, v___x_4716_, v_currMacroScope_4704_);
v___x_4718_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4709_);
lean_ctor_set(v___x_4719_, 1, v___x_4715_);
lean_ctor_set(v___x_4719_, 2, v___x_4717_);
lean_ctor_set(v___x_4719_, 3, v___x_4718_);
lean_inc_ref(v___x_4719_);
v___x_4720_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4707_, v___x_4714_, v___x_4719_, v___x_4719_, v_a_4697_, v_a_4698_);
lean_dec(v_interpStr_4707_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_a_4722_ = lean_ctor_get(v___x_4720_, 1);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4720_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4721_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4730_ = lean_ctor_get(v___x_4720_, 0);
v_a_4731_ = lean_ctor_get(v___x_4720_, 1);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4720_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_inc(v_a_4730_);
lean_dec(v___x_4720_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4730_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4739_, v_a_4740_, v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4742_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4745_ = l_Lean_stringToMessageData(v___x_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4746_){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4747_ = lean_array_to_list(v_msgs_4746_);
v___x_4748_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4749_ = l_Lean_MessageData_joinSep(v___x_4747_, v___x_4748_);
v___x_4750_ = l_Lean_indentD(v___x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4751_, lean_object* v_lctx_4752_, lean_object* v_opts_4753_, lean_object* v_msg_4754_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4755_ = lean_elab_environment_of_kernel_env(v_env_4751_);
v___x_4756_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4757_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
lean_ctor_set(v___x_4757_, 2, v_lctx_4752_);
lean_ctor_set(v___x_4757_, 3, v_opts_4753_);
v___x_4758_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
lean_ctor_set(v___x_4758_, 1, v_msg_4754_);
return v___x_4758_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4761_ = l_Lean_stringToMessageData(v___x_4760_);
return v___x_4761_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4764_ = l_Lean_stringToMessageData(v___x_4763_);
return v___x_4764_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4767_ = l_Lean_stringToMessageData(v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4768_, lean_object* v_n_4769_, lean_object* v_expectedType_4770_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4771_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4772_ = l_Lean_MessageData_ofName(v_n_4769_);
v___x_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4773_);
lean_ctor_set(v___x_4775_, 1, v___x_4774_);
v___x_4776_ = l_Lean_indentExpr(v_givenType_4768_);
v___x_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v___x_4778_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4777_);
lean_ctor_set(v___x_4779_, 1, v___x_4778_);
v___x_4780_ = l_Lean_indentExpr(v_expectedType_4770_);
v___x_4781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
return v___x_4781_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4782_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4783_);
return v___x_4784_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4785_ = lean_box(1);
v___x_4786_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4787_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4787_);
lean_ctor_set(v___x_4788_, 1, v___x_4786_);
lean_ctor_set(v___x_4788_, 2, v___x_4785_);
return v___x_4788_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4790_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4791_ = l_Lean_stringToMessageData(v___x_4790_);
return v___x_4791_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4793_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4794_ = l_Lean_stringToMessageData(v___x_4793_);
return v___x_4794_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4797_ = l_Lean_stringToMessageData(v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4802_ = l_Lean_MessageData_ofFormat(v___x_4801_);
return v___x_4802_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4805_ = l_Lean_stringToMessageData(v___x_4804_);
return v___x_4805_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4808_ = l_Lean_stringToMessageData(v___x_4807_);
return v___x_4808_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4811_ = l_Lean_stringToMessageData(v___x_4810_);
return v___x_4811_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4813_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4814_ = l_Lean_stringToMessageData(v___x_4813_);
return v___x_4814_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4816_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4817_ = l_Lean_stringToMessageData(v___x_4816_);
return v___x_4817_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4819_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4820_ = l_Lean_stringToMessageData(v___x_4819_);
return v___x_4820_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4823_ = l_Lean_stringToMessageData(v___x_4822_);
return v___x_4823_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4826_ = l_Lean_stringToMessageData(v___x_4825_);
return v___x_4826_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4829_ = l_Lean_stringToMessageData(v___x_4828_);
return v___x_4829_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
return v___x_4832_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4835_ = l_Lean_stringToMessageData(v___x_4834_);
return v___x_4835_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4838_ = l_Lean_stringToMessageData(v___x_4837_);
return v___x_4838_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4841_ = l_Lean_stringToMessageData(v___x_4840_);
return v___x_4841_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4844_ = l_Lean_stringToMessageData(v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4849_ = l_Lean_MessageData_ofFormat(v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4854_ = l_Lean_MessageData_ofFormat(v___x_4853_);
return v___x_4854_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4859_ = l_Lean_MessageData_ofFormat(v___x_4858_);
return v___x_4859_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4864_ = l_Lean_MessageData_ofFormat(v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4865_, lean_object* v_opts_4866_){
_start:
{
switch(lean_obj_tag(v_e_4865_))
{
case 0:
{
lean_object* v_env_4867_; lean_object* v_name_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4881_; 
v_env_4867_ = lean_ctor_get(v_e_4865_, 0);
v_name_4868_ = lean_ctor_get(v_e_4865_, 1);
v_isSharedCheck_4881_ = !lean_is_exclusive(v_e_4865_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4870_ = v_e_4865_;
v_isShared_4871_ = v_isSharedCheck_4881_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_name_4868_);
lean_inc(v_env_4867_);
lean_dec(v_e_4865_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4881_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4872_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4873_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4874_ = l_Lean_MessageData_ofName(v_name_4868_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set_tag(v___x_4870_, 7);
lean_ctor_set(v___x_4870_, 1, v___x_4874_);
lean_ctor_set(v___x_4870_, 0, v___x_4873_);
v___x_4876_ = v___x_4870_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4873_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4876_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
v___x_4879_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4867_, v___x_4872_, v_opts_4866_, v___x_4878_);
return v___x_4879_;
}
}
}
case 1:
{
lean_object* v_env_4882_; lean_object* v_name_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4897_; 
v_env_4882_ = lean_ctor_get(v_e_4865_, 0);
v_name_4883_ = lean_ctor_get(v_e_4865_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_e_4865_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4885_ = v_e_4865_;
v_isShared_4886_ = v_isSharedCheck_4897_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_name_4883_);
lean_inc(v_env_4882_);
lean_dec(v_e_4865_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4897_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; uint8_t v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v___x_4887_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4888_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4889_ = 1;
v___x_4890_ = l_Lean_MessageData_ofConstName(v_name_4883_, v___x_4889_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set_tag(v___x_4885_, 7);
lean_ctor_set(v___x_4885_, 1, v___x_4890_);
lean_ctor_set(v___x_4885_, 0, v___x_4888_);
v___x_4892_ = v___x_4885_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4888_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4892_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4882_, v___x_4887_, v_opts_4866_, v___x_4894_);
return v___x_4895_;
}
}
}
case 2:
{
lean_object* v_env_4898_; lean_object* v_decl_4899_; lean_object* v_givenType_4900_; lean_object* v___x_4901_; 
v_env_4898_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4898_);
v_decl_4899_ = lean_ctor_get(v_e_4865_, 1);
lean_inc(v_decl_4899_);
v_givenType_4900_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_givenType_4900_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4901_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4899_))
{
case 1:
{
lean_object* v_val_4902_; lean_object* v_toConstantVal_4903_; lean_object* v_name_4904_; lean_object* v_type_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
v_val_4902_ = lean_ctor_get(v_decl_4899_, 0);
lean_inc_ref(v_val_4902_);
lean_dec_ref_known(v_decl_4899_, 1);
v_toConstantVal_4903_ = lean_ctor_get(v_val_4902_, 0);
lean_inc_ref(v_toConstantVal_4903_);
lean_dec_ref(v_val_4902_);
v_name_4904_ = lean_ctor_get(v_toConstantVal_4903_, 0);
lean_inc(v_name_4904_);
v_type_4905_ = lean_ctor_get(v_toConstantVal_4903_, 2);
lean_inc_ref(v_type_4905_);
lean_dec_ref(v_toConstantVal_4903_);
v___x_4906_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4900_, v_name_4904_, v_type_4905_);
v___x_4907_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4898_, v___x_4901_, v_opts_4866_, v___x_4906_);
return v___x_4907_;
}
case 2:
{
lean_object* v_val_4908_; lean_object* v_toConstantVal_4909_; lean_object* v_name_4910_; lean_object* v_type_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_val_4908_ = lean_ctor_get(v_decl_4899_, 0);
lean_inc_ref(v_val_4908_);
lean_dec_ref_known(v_decl_4899_, 1);
v_toConstantVal_4909_ = lean_ctor_get(v_val_4908_, 0);
lean_inc_ref(v_toConstantVal_4909_);
lean_dec_ref(v_val_4908_);
v_name_4910_ = lean_ctor_get(v_toConstantVal_4909_, 0);
lean_inc(v_name_4910_);
v_type_4911_ = lean_ctor_get(v_toConstantVal_4909_, 2);
lean_inc_ref(v_type_4911_);
lean_dec_ref(v_toConstantVal_4909_);
v___x_4912_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4900_, v_name_4910_, v_type_4911_);
v___x_4913_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4898_, v___x_4901_, v_opts_4866_, v___x_4912_);
return v___x_4913_;
}
default: 
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec_ref(v_givenType_4900_);
lean_dec(v_decl_4899_);
v___x_4914_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4915_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4898_, v___x_4901_, v_opts_4866_, v___x_4914_);
return v___x_4915_;
}
}
}
case 3:
{
lean_object* v_env_4916_; lean_object* v_name_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v_env_4916_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4916_);
v_name_4917_ = lean_ctor_get(v_e_4865_, 1);
lean_inc(v_name_4917_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4918_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4919_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4920_ = 1;
v___x_4921_ = l_Lean_MessageData_ofConstName(v_name_4917_, v___x_4920_);
v___x_4922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4919_);
lean_ctor_set(v___x_4922_, 1, v___x_4921_);
v___x_4923_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4922_);
lean_ctor_set(v___x_4924_, 1, v___x_4923_);
v___x_4925_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4916_, v___x_4918_, v_opts_4866_, v___x_4924_);
return v___x_4925_;
}
case 4:
{
lean_object* v_env_4926_; lean_object* v_name_4927_; lean_object* v_expr_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v_env_4926_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4926_);
v_name_4927_ = lean_ctor_get(v_e_4865_, 1);
lean_inc(v_name_4927_);
v_expr_4928_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_expr_4928_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4929_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4930_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4931_ = 1;
v___x_4932_ = l_Lean_MessageData_ofConstName(v_name_4927_, v___x_4931_);
v___x_4933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4930_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4933_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = l_Lean_indentExpr(v_expr_4928_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4926_, v___x_4929_, v_opts_4866_, v___x_4937_);
return v___x_4938_;
}
case 5:
{
lean_object* v_env_4939_; lean_object* v_lctx_4940_; lean_object* v_expr_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v_env_4939_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4939_);
v_lctx_4940_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4940_);
v_expr_4941_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_expr_4941_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4942_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4943_ = l_Lean_indentExpr(v_expr_4941_);
v___x_4944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4942_);
lean_ctor_set(v___x_4944_, 1, v___x_4943_);
v___x_4945_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4939_, v_lctx_4940_, v_opts_4866_, v___x_4944_);
return v___x_4945_;
}
case 6:
{
lean_object* v_env_4946_; lean_object* v_lctx_4947_; lean_object* v_expr_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v_env_4946_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4946_);
v_lctx_4947_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4947_);
v_expr_4948_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_expr_4948_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4949_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4950_ = l_Lean_indentExpr(v_expr_4948_);
v___x_4951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4949_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
v___x_4952_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4946_, v_lctx_4947_, v_opts_4866_, v___x_4951_);
return v___x_4952_;
}
case 7:
{
lean_object* v_env_4953_; lean_object* v_lctx_4954_; lean_object* v_name_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v_env_4953_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4953_);
v_lctx_4954_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4954_);
v_name_4955_ = lean_ctor_get(v_e_4865_, 2);
lean_inc(v_name_4955_);
lean_dec_ref_known(v_e_4865_, 5);
v___x_4956_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4957_ = l_Lean_MessageData_ofName(v_name_4955_);
v___x_4958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4953_, v_lctx_4954_, v_opts_4866_, v___x_4960_);
return v___x_4961_;
}
case 8:
{
lean_object* v_env_4962_; lean_object* v_lctx_4963_; lean_object* v_expr_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_env_4962_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4962_);
v_lctx_4963_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4963_);
v_expr_4964_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_expr_4964_);
lean_dec_ref_known(v_e_4865_, 4);
v___x_4965_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4966_ = l_Lean_indentExpr(v_expr_4964_);
v___x_4967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4965_);
lean_ctor_set(v___x_4967_, 1, v___x_4966_);
v___x_4968_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4962_, v_lctx_4963_, v_opts_4866_, v___x_4967_);
return v___x_4968_;
}
case 9:
{
lean_object* v_env_4969_; lean_object* v_lctx_4970_; lean_object* v_app_4971_; lean_object* v_funType_4972_; lean_object* v_argType_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_env_4969_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4969_);
v_lctx_4970_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4970_);
v_app_4971_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_app_4971_);
v_funType_4972_ = lean_ctor_get(v_e_4865_, 3);
lean_inc_ref(v_funType_4972_);
v_argType_4973_ = lean_ctor_get(v_e_4865_, 4);
lean_inc_ref(v_argType_4973_);
lean_dec_ref_known(v_e_4865_, 5);
v___x_4974_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4975_ = l_Lean_indentExpr(v_app_4971_);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = l_Lean_indentExpr(v_argType_4973_);
v___x_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4978_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
v___x_4981_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = l_Lean_indentExpr(v_funType_4972_);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4969_, v_lctx_4970_, v_opts_4866_, v___x_4984_);
return v___x_4985_;
}
case 10:
{
lean_object* v_env_4986_; lean_object* v_lctx_4987_; lean_object* v_proj_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v_env_4986_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4986_);
v_lctx_4987_ = lean_ctor_get(v_e_4865_, 1);
lean_inc_ref(v_lctx_4987_);
v_proj_4988_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_proj_4988_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4989_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4990_ = l_Lean_indentExpr(v_proj_4988_);
v___x_4991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4989_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4986_, v_lctx_4987_, v_opts_4866_, v___x_4991_);
return v___x_4992_;
}
case 11:
{
lean_object* v_env_4993_; lean_object* v_name_4994_; lean_object* v_type_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v_env_4993_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_env_4993_);
v_name_4994_ = lean_ctor_get(v_e_4865_, 1);
lean_inc(v_name_4994_);
v_type_4995_ = lean_ctor_get(v_e_4865_, 2);
lean_inc_ref(v_type_4995_);
lean_dec_ref_known(v_e_4865_, 3);
v___x_4996_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4997_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4998_ = 1;
v___x_4999_ = l_Lean_MessageData_ofConstName(v_name_4994_, v___x_4998_);
v___x_5000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4997_);
lean_ctor_set(v___x_5000_, 1, v___x_4999_);
v___x_5001_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_5002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5000_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = l_Lean_indentExpr(v_type_4995_);
v___x_5004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5002_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
v___x_5005_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4993_, v___x_4996_, v_opts_4866_, v___x_5004_);
return v___x_5005_;
}
case 12:
{
lean_object* v_msg_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
lean_dec_ref(v_opts_4866_);
v_msg_5006_ = lean_ctor_get(v_e_4865_, 0);
lean_inc_ref(v_msg_5006_);
lean_dec_ref_known(v_e_4865_, 1);
v___x_5007_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_5008_ = l_Lean_stringToMessageData(v_msg_5006_);
v___x_5009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5007_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
return v___x_5009_;
}
case 13:
{
lean_object* v___x_5010_; 
lean_dec_ref(v_opts_4866_);
v___x_5010_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_5010_;
}
case 14:
{
lean_object* v___x_5011_; 
lean_dec_ref(v_opts_4866_);
v___x_5011_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_5011_;
}
case 15:
{
lean_object* v___x_5012_; 
lean_dec_ref(v_opts_4866_);
v___x_5012_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_5012_;
}
default: 
{
lean_object* v___x_5013_; 
lean_dec_ref(v_opts_4866_);
v___x_5013_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_5013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_5014_, lean_object* v_e_5015_, lean_object* v_cls_5016_){
_start:
{
lean_object* v___x_5017_; double v___x_5018_; uint8_t v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5017_ = lean_box(0);
v___x_5018_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_5019_ = 1;
v___x_5020_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_5021_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5021_, 0, v_cls_5016_);
lean_ctor_set(v___x_5021_, 1, v___x_5017_);
lean_ctor_set(v___x_5021_, 2, v___x_5020_);
lean_ctor_set_float(v___x_5021_, sizeof(void*)*3, v___x_5018_);
lean_ctor_set_float(v___x_5021_, sizeof(void*)*3 + 8, v___x_5018_);
lean_ctor_set_uint8(v___x_5021_, sizeof(void*)*3 + 16, v___x_5019_);
v___x_5022_ = lean_apply_1(v_inst_5014_, v_e_5015_);
v___x_5023_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_5024_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5021_);
lean_ctor_set(v___x_5024_, 1, v___x_5022_);
lean_ctor_set(v___x_5024_, 2, v___x_5023_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_5025_, lean_object* v_inst_5026_, lean_object* v_e_5027_, lean_object* v_cls_5028_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l_Lean_toTraceElem___redArg(v_inst_5026_, v_e_5027_, v_cls_5028_);
return v___x_5029_;
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
