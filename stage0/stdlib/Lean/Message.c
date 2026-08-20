// Lean compiler output
// Module: Lean.Message
// Imports: public import Init.Data.Slice.Array public import Lean.Util.PPExt public import Lean.Util.Sorry public import Lean.Linter.CodeQuality.Basic import Init.Data.String.Search import Init.Data.Format.Macro import Init.Data.Iterators.Consumers.Collect import Init.Data.String.Length
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
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedMessageData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedMessageData_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData_default = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMessageData = (const lean_object*)&l_Lean_instInhabitedMessageData_default___closed__0_value;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameMessageData = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value;
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
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
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
static const lean_ctor_object l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_instFromJsonSerialMessage_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_termM_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value)}};
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
static const lean_ctor_object l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Message_4238524789____hygCtx___hyg_150__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
lean_inc_ref(v___y_39_);
v___x_43_ = lean_string_append(v___y_39_, v___y_42_);
if (lean_obj_tag(v___y_40_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___y_41_;
v___y_33_ = v___x_43_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_40_, 1);
v___y_32_ = v___y_41_;
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
v___y_39_ = v___x_49_;
v___y_40_ = v___y_48_;
v___y_41_ = v___y_47_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___x_49_;
v___y_40_ = v___y_48_;
v___y_41_ = v___y_47_;
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
case 11:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(11u);
return v___x_378_;
}
default: 
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(12u);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_MessageData_ctorIdx(v_x_380_);
lean_dec_ref(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_382_, lean_object* v_k_383_){
_start:
{
switch(lean_obj_tag(v_t_382_))
{
case 0:
{
lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_384_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_t_382_, 1);
v___x_385_ = lean_apply_1(v_k_383_, v_a_384_);
return v___x_385_;
}
case 1:
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v_t_382_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v_t_382_, 1);
v___x_387_ = lean_apply_1(v_k_383_, v_a_386_);
return v___x_387_;
}
case 5:
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_388_ = lean_ctor_get(v_t_382_, 0);
lean_inc(v_a_388_);
v_a_389_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_a_389_);
lean_dec_ref_known(v_t_382_, 2);
v___x_390_ = lean_apply_2(v_k_383_, v_a_388_, v_a_389_);
return v___x_390_;
}
case 6:
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_a_391_);
lean_dec_ref_known(v_t_382_, 1);
v___x_392_ = lean_apply_1(v_k_383_, v_a_391_);
return v___x_392_;
}
case 8:
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v_t_382_, 0);
lean_inc(v_a_393_);
v_a_394_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_a_394_);
lean_dec_ref_known(v_t_382_, 2);
v___x_395_ = lean_apply_2(v_k_383_, v_a_393_, v_a_394_);
return v___x_395_;
}
case 9:
{
lean_object* v_data_396_; lean_object* v_msg_397_; lean_object* v_children_398_; lean_object* v___x_399_; 
v_data_396_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_data_396_);
v_msg_397_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_msg_397_);
v_children_398_ = lean_ctor_get(v_t_382_, 2);
lean_inc_ref(v_children_398_);
lean_dec_ref_known(v_t_382_, 3);
v___x_399_ = lean_apply_3(v_k_383_, v_data_396_, v_msg_397_, v_children_398_);
return v___x_399_;
}
case 11:
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v_t_382_, 0);
lean_inc(v_a_400_);
v_a_401_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_a_401_);
lean_dec_ref_known(v_t_382_, 2);
v___x_402_ = lean_apply_2(v_k_383_, v_a_400_, v_a_401_);
return v___x_402_;
}
default: 
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_403_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_a_403_);
v_a_404_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_a_404_);
lean_dec_ref(v_t_382_);
v___x_405_ = lean_apply_2(v_k_383_, v_a_403_, v_a_404_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_406_, lean_object* v_ctorIdx_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_k_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_MessageData_ctorElim___redArg(v_t_408_, v_k_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_412_, lean_object* v_ctorIdx_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_k_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_MessageData_ctorElim(v_motive__1_412_, v_ctorIdx_413_, v_t_414_, v_h_415_, v_k_416_);
lean_dec(v_ctorIdx_413_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_418_, lean_object* v_ofFormatWithInfos_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_MessageData_ctorElim___redArg(v_t_418_, v_ofFormatWithInfos_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_ofFormatWithInfos_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_MessageData_ctorElim___redArg(v_t_422_, v_ofFormatWithInfos_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_426_, lean_object* v_ofGoal_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_MessageData_ctorElim___redArg(v_t_426_, v_ofGoal_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_429_, lean_object* v_t_430_, lean_object* v_h_431_, lean_object* v_ofGoal_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_MessageData_ctorElim___redArg(v_t_430_, v_ofGoal_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_434_, lean_object* v_ofWidget_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_MessageData_ctorElim___redArg(v_t_434_, v_ofWidget_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_ofWidget_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_MessageData_ctorElim___redArg(v_t_438_, v_ofWidget_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_442_, lean_object* v_withContext_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_MessageData_ctorElim___redArg(v_t_442_, v_withContext_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_withContext_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_MessageData_ctorElim___redArg(v_t_446_, v_withContext_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_450_, lean_object* v_withNamingContext_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_MessageData_ctorElim___redArg(v_t_450_, v_withNamingContext_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_withNamingContext_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_MessageData_ctorElim___redArg(v_t_454_, v_withNamingContext_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_458_, lean_object* v_nest_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_MessageData_ctorElim___redArg(v_t_458_, v_nest_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_nest_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_MessageData_ctorElim___redArg(v_t_462_, v_nest_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_466_, lean_object* v_group_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_MessageData_ctorElim___redArg(v_t_466_, v_group_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_group_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_MessageData_ctorElim___redArg(v_t_470_, v_group_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_474_, lean_object* v_compose_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_MessageData_ctorElim___redArg(v_t_474_, v_compose_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_compose_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_MessageData_ctorElim___redArg(v_t_478_, v_compose_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_482_, lean_object* v_tagged_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_MessageData_ctorElim___redArg(v_t_482_, v_tagged_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_tagged_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_MessageData_ctorElim___redArg(v_t_486_, v_tagged_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_490_, lean_object* v_trace_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_MessageData_ctorElim___redArg(v_t_490_, v_trace_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_493_, lean_object* v_t_494_, lean_object* v_h_495_, lean_object* v_trace_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_MessageData_ctorElim___redArg(v_t_494_, v_trace_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_498_, lean_object* v_ofLazy_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_MessageData_ctorElim___redArg(v_t_498_, v_ofLazy_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_ofLazy_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_MessageData_ctorElim___redArg(v_t_502_, v_ofLazy_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_506_, lean_object* v_ofOriginatingSyntax_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_MessageData_ctorElim___redArg(v_t_506_, v_ofOriginatingSyntax_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_ofOriginatingSyntax_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_MessageData_ctorElim___redArg(v_t_510_, v_ofOriginatingSyntax_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim___redArg(lean_object* v_t_514_, lean_object* v_ofCodeQualityEntry_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_MessageData_ctorElim___redArg(v_t_514_, v_ofCodeQualityEntry_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim(lean_object* v_motive__1_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_ofCodeQualityEntry_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_MessageData_ctorElim___redArg(v_t_518_, v_ofCodeQualityEntry_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_fmt_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_537_, lean_object* v_onMissingContext_538_, lean_object* v_f_539_, lean_object* v_ctx_x3f_540_){
_start:
{
lean_object* v_msg_543_; 
if (lean_obj_tag(v_ctx_x3f_540_) == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_f_539_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_apply_2(v_onMissingContext_538_, v___x_545_, lean_box(0));
v_msg_543_ = v___x_546_;
goto v___jp_542_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; 
lean_dec_ref(v_onMissingContext_538_);
v_val_547_ = lean_ctor_get(v_ctx_x3f_540_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_ctx_x3f_540_, 1);
v___x_548_ = lean_apply_2(v_f_539_, v_val_547_, lean_box(0));
v_msg_543_ = v___x_548_;
goto v___jp_542_;
}
v___jp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_537_);
lean_ctor_set(v___x_544_, 1, v_msg_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_549_, lean_object* v_onMissingContext_550_, lean_object* v_f_551_, lean_object* v_ctx_x3f_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_MessageData_lazy___lam__0(v___x_549_, v_onMissingContext_550_, v_f_551_, v_ctx_x3f_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_555_, lean_object* v_hasSyntheticSorry_556_, lean_object* v_onMissingContext_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v___x_558_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_559_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_559_, 0, v___x_558_);
lean_closure_set(v___f_559_, 1, v_onMissingContext_557_);
lean_closure_set(v___f_559_, 2, v_f_555_);
v___x_560_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_560_, 0, v___f_559_);
lean_ctor_set(v___x_560_, 1, v_hasSyntheticSorry_556_);
return v___x_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_561_, lean_object* v_x_562_){
_start:
{
switch(lean_obj_tag(v_x_562_))
{
case 3:
{
lean_object* v_a_563_; 
v_a_563_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_563_);
lean_dec_ref_known(v_x_562_, 2);
v_x_562_ = v_a_563_;
goto _start;
}
case 4:
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v_x_562_, 2);
v_x_562_ = v_a_565_;
goto _start;
}
case 5:
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_567_);
lean_dec_ref_known(v_x_562_, 2);
v_x_562_ = v_a_567_;
goto _start;
}
case 6:
{
lean_object* v_a_569_; 
v_a_569_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_a_569_);
lean_dec_ref_known(v_x_562_, 1);
v_x_562_ = v_a_569_;
goto _start;
}
case 7:
{
lean_object* v_a_571_; lean_object* v_a_572_; uint8_t v___x_573_; 
v_a_571_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_a_571_);
v_a_572_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_572_);
lean_dec_ref_known(v_x_562_, 2);
lean_inc_ref(v_p_561_);
v___x_573_ = l_Lean_MessageData_hasTag(v_p_561_, v_a_571_);
if (v___x_573_ == 0)
{
v_x_562_ = v_a_572_;
goto _start;
}
else
{
lean_dec_ref(v_a_572_);
lean_dec_ref(v_p_561_);
return v___x_573_;
}
}
case 8:
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_a_575_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_a_575_);
v_a_576_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_576_);
lean_dec_ref_known(v_x_562_, 2);
lean_inc_ref(v_p_561_);
v___x_577_ = lean_apply_1(v_p_561_, v_a_575_);
v___x_578_ = lean_unbox(v___x_577_);
if (v___x_578_ == 0)
{
v_x_562_ = v_a_576_;
goto _start;
}
else
{
uint8_t v___x_580_; 
lean_dec_ref(v_a_576_);
lean_dec_ref(v_p_561_);
v___x_580_ = lean_unbox(v___x_577_);
return v___x_580_;
}
}
case 9:
{
lean_object* v_data_581_; lean_object* v_msg_582_; lean_object* v_children_583_; lean_object* v_cls_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_data_581_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_data_581_);
v_msg_582_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_msg_582_);
v_children_583_ = lean_ctor_get(v_x_562_, 2);
lean_inc_ref(v_children_583_);
lean_dec_ref_known(v_x_562_, 3);
v_cls_584_ = lean_ctor_get(v_data_581_, 0);
lean_inc(v_cls_584_);
lean_dec_ref(v_data_581_);
lean_inc_ref(v_p_561_);
v___x_585_ = lean_apply_1(v_p_561_, v_cls_584_);
v___x_586_ = lean_unbox(v___x_585_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
lean_inc_ref(v_p_561_);
v___x_587_ = l_Lean_MessageData_hasTag(v_p_561_, v_msg_582_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_array_get_size(v_children_583_);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec_ref(v_children_583_);
lean_dec_ref(v_p_561_);
return v___x_590_;
}
else
{
if (v___x_590_ == 0)
{
lean_dec_ref(v_children_583_);
lean_dec_ref(v_p_561_);
return v___x_590_;
}
else
{
size_t v___x_591_; size_t v___x_592_; uint8_t v___x_593_; 
v___x_591_ = ((size_t)0ULL);
v___x_592_ = lean_usize_of_nat(v___x_589_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_561_, v_children_583_, v___x_591_, v___x_592_);
lean_dec_ref(v_children_583_);
return v___x_593_;
}
}
}
else
{
lean_dec_ref(v_children_583_);
lean_dec_ref(v_p_561_);
return v___x_587_;
}
}
else
{
uint8_t v___x_594_; 
lean_dec_ref(v_children_583_);
lean_dec_ref(v_msg_582_);
lean_dec_ref(v_p_561_);
v___x_594_ = lean_unbox(v___x_585_);
return v___x_594_;
}
}
case 11:
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_595_);
lean_dec_ref_known(v_x_562_, 2);
v_x_562_ = v_a_595_;
goto _start;
}
case 12:
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_a_597_);
lean_dec_ref_known(v_x_562_, 2);
v_x_562_ = v_a_597_;
goto _start;
}
default: 
{
uint8_t v___x_599_; 
lean_dec_ref(v_x_562_);
lean_dec_ref(v_p_561_);
v___x_599_ = 0;
return v___x_599_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_600_, lean_object* v_as_601_, size_t v_i_602_, size_t v_stop_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_eq(v_i_602_, v_stop_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_uget_borrowed(v_as_601_, v_i_602_);
lean_inc(v___x_605_);
lean_inc_ref(v_p_600_);
v___x_606_ = l_Lean_MessageData_hasTag(v_p_600_, v___x_605_);
if (v___x_606_ == 0)
{
size_t v___x_607_; size_t v___x_608_; 
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_602_, v___x_607_);
v_i_602_ = v___x_608_;
goto _start;
}
else
{
lean_dec_ref(v_p_600_);
return v___x_606_;
}
}
else
{
uint8_t v___x_610_; 
lean_dec_ref(v_p_600_);
v___x_610_ = 0;
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; uint8_t v_res_617_; lean_object* v_r_618_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_611_, v_as_612_, v_i_boxed_615_, v_stop_boxed_616_);
lean_dec_ref(v_as_612_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_619_, lean_object* v_x_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Lean_MessageData_hasTag(v_p_619_, v_x_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_623_){
_start:
{
switch(lean_obj_tag(v_x_623_))
{
case 3:
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v_x_623_, 1);
v_x_623_ = v_a_624_;
goto _start;
}
case 4:
{
lean_object* v_a_626_; 
v_a_626_ = lean_ctor_get(v_x_623_, 1);
v_x_623_ = v_a_626_;
goto _start;
}
case 8:
{
lean_object* v_a_628_; 
v_a_628_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_a_628_);
return v_a_628_;
}
case 9:
{
lean_object* v_data_629_; lean_object* v_cls_630_; 
v_data_629_ = lean_ctor_get(v_x_623_, 0);
v_cls_630_ = lean_ctor_get(v_data_629_, 0);
lean_inc(v_cls_630_);
return v_cls_630_;
}
case 11:
{
lean_object* v_a_631_; 
v_a_631_ = lean_ctor_get(v_x_623_, 1);
v_x_623_ = v_a_631_;
goto _start;
}
case 12:
{
lean_object* v_a_633_; 
v_a_633_ = lean_ctor_get(v_x_623_, 1);
v_x_623_ = v_a_633_;
goto _start;
}
default: 
{
lean_object* v___x_635_; 
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_MessageData_kind(v_x_636_);
lean_dec_ref(v_x_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 11)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_a_639_ = lean_ctor_get(v_x_638_, 0);
v_a_640_ = lean_ctor_get(v_x_638_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_648_ == 0)
{
v___x_642_ = v_x_638_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v_x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_a_639_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 0);
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_a_640_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_x_638_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f(lean_object* v_x_651_){
_start:
{
switch(lean_obj_tag(v_x_651_))
{
case 12:
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v_x_651_, 0);
lean_inc_ref(v_a_652_);
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_a_652_);
return v___x_653_;
}
case 3:
{
lean_object* v_a_654_; 
v_a_654_ = lean_ctor_get(v_x_651_, 1);
v_x_651_ = v_a_654_;
goto _start;
}
case 4:
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v_x_651_, 1);
v_x_651_ = v_a_656_;
goto _start;
}
case 8:
{
lean_object* v_a_658_; 
v_a_658_ = lean_ctor_get(v_x_651_, 1);
v_x_651_ = v_a_658_;
goto _start;
}
case 11:
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v_x_651_, 1);
v_x_651_ = v_a_660_;
goto _start;
}
default: 
{
lean_object* v___x_662_; 
v___x_662_ = lean_box(0);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f___boxed(lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_MessageData_codeQualityEntry_x3f(v_x_663_);
lean_dec_ref(v_x_663_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_665_){
_start:
{
switch(lean_obj_tag(v_x_665_))
{
case 3:
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v_x_665_, 1);
v_x_665_ = v_a_666_;
goto _start;
}
case 4:
{
lean_object* v_a_668_; 
v_a_668_ = lean_ctor_get(v_x_665_, 1);
v_x_665_ = v_a_668_;
goto _start;
}
case 8:
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v_x_665_, 1);
v_x_665_ = v_a_670_;
goto _start;
}
case 9:
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
case 11:
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v_x_665_, 1);
v_x_665_ = v_a_673_;
goto _start;
}
case 12:
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v_x_665_, 1);
v_x_665_ = v_a_675_;
goto _start;
}
default: 
{
uint8_t v___x_677_; 
v___x_677_ = 0;
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Lean_MessageData_isTrace(v_x_678_);
lean_dec_ref(v_x_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
switch(lean_obj_tag(v_x_681_))
{
case 3:
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_683_ = lean_ctor_get(v_x_681_, 0);
v_a_684_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v_x_681_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_inc(v_a_683_);
lean_dec(v_x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_MessageData_composePreservingKind(v_a_684_, v_x_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_683_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
case 4:
{
lean_object* v_a_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_702_; 
v_a_693_ = lean_ctor_get(v_x_681_, 0);
v_a_694_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_702_ == 0)
{
v___x_696_ = v_x_681_;
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_inc(v_a_693_);
lean_dec(v_x_681_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_702_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_MessageData_composePreservingKind(v_a_694_, v_x_682_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_693_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
case 8:
{
lean_object* v_a_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_a_703_ = lean_ctor_get(v_x_681_, 0);
v_a_704_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_712_ == 0)
{
v___x_706_ = v_x_681_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_inc(v_a_703_);
lean_dec(v_x_681_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 7);
lean_ctor_set(v___x_706_, 1, v_x_682_);
lean_ctor_set(v___x_706_, 0, v_a_704_);
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_704_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_x_682_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_710_, 0, v_a_703_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
return v___x_710_;
}
}
}
case 11:
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_a_713_ = lean_ctor_get(v_x_681_, 0);
v_a_714_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v_x_681_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_inc(v_a_713_);
lean_dec(v_x_681_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_MessageData_composePreservingKind(v_a_714_, v_x_682_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_713_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
case 12:
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_a_723_ = lean_ctor_get(v_x_681_, 0);
v_a_724_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v_x_681_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_inc(v_a_723_);
lean_dec(v_x_681_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_MessageData_composePreservingKind(v_a_724_, v_x_682_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
default: 
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v_x_681_);
lean_ctor_set(v___x_733_, 1, v_x_682_);
return v___x_733_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = l_Lean_MessageData_ofFormat(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_737_, lean_object* v_ctx_738_){
_start:
{
lean_object* v_env_739_; lean_object* v_mctx_740_; lean_object* v_lctx_741_; lean_object* v_opts_742_; lean_object* v_currNamespace_743_; lean_object* v_openDecls_744_; lean_object* v___x_745_; 
v_env_739_ = lean_ctor_get(v_ctx_738_, 0);
v_mctx_740_ = lean_ctor_get(v_ctx_738_, 1);
v_lctx_741_ = lean_ctor_get(v_ctx_738_, 2);
v_opts_742_ = lean_ctor_get(v_ctx_738_, 3);
v_currNamespace_743_ = lean_ctor_get(v_nCtx_737_, 0);
v_openDecls_744_ = lean_ctor_get(v_nCtx_737_, 1);
lean_inc(v_openDecls_744_);
lean_inc(v_currNamespace_743_);
lean_inc_ref(v_opts_742_);
lean_inc_ref(v_lctx_741_);
lean_inc_ref(v_mctx_740_);
lean_inc_ref(v_env_739_);
v___x_745_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_745_, 0, v_env_739_);
lean_ctor_set(v___x_745_, 1, v_mctx_740_);
lean_ctor_set(v___x_745_, 2, v_lctx_741_);
lean_ctor_set(v___x_745_, 3, v_opts_742_);
lean_ctor_set(v___x_745_, 4, v_currNamespace_743_);
lean_ctor_set(v___x_745_, 5, v_openDecls_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_746_, lean_object* v_ctx_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_MessageData_mkPPContext(v_nCtx_746_, v_ctx_747_);
lean_dec_ref(v_ctx_747_);
lean_dec_ref(v_nCtx_746_);
return v_res_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = 0;
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_751_);
lean_dec_ref(v_x_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_754_, lean_object* v_stx_755_, lean_object* v_ctx_x3f_756_){
_start:
{
lean_object* v_val_759_; 
if (lean_obj_tag(v_ctx_x3f_756_) == 0)
{
lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_box(0);
v___x_763_ = 0;
v___x_764_ = l_Lean_Syntax_formatStx(v_stx_755_, v___x_762_, v___x_763_);
v_val_759_ = v___x_764_;
goto v___jp_758_;
}
else
{
lean_object* v_val_765_; lean_object* v___x_766_; 
v_val_765_ = lean_ctor_get(v_ctx_x3f_756_, 0);
lean_inc(v_val_765_);
lean_dec_ref_known(v_ctx_x3f_756_, 1);
v___x_766_ = l_Lean_ppTerm(v_val_765_, v_stx_755_);
v_val_759_ = v___x_766_;
goto v___jp_758_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = l_Lean_MessageData_ofFormat(v_val_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_754_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_767_, lean_object* v_stx_768_, lean_object* v_ctx_x3f_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_767_, v_stx_768_, v_ctx_x3f_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_773_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_stx_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v___f_774_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_775_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_776_ = lean_box(0);
v_stx_777_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_773_, v___x_776_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_778_, 0, v___x_775_);
lean_closure_set(v___f_778_, 1, v_stx_777_);
v___x_779_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_779_, 0, v___f_778_);
lean_ctor_set(v___x_779_, 1, v___f_774_);
return v___x_779_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_780_, lean_object* v_mctx_781_){
_start:
{
lean_object* v___x_782_; lean_object* v_fst_783_; uint8_t v___x_784_; 
v___x_782_ = l_Lean_instantiateMVarsCore(v_mctx_781_, v_e_780_);
v_fst_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_fst_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Lean_Expr_hasSyntheticSorry(v_fst_783_);
lean_dec(v_fst_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_785_, lean_object* v_mctx_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_MessageData_ofExpr___lam__0(v_e_785_, v_mctx_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_789_, lean_object* v_e_790_, lean_object* v_ctx_x3f_791_){
_start:
{
lean_object* v_val_794_; 
if (lean_obj_tag(v_ctx_x3f_791_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_797_ = lean_expr_dbg_to_string(v_e_790_);
lean_dec_ref(v_e_790_);
v___x_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = lean_box(1);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v_val_794_ = v___x_800_;
goto v___jp_793_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_802_; 
v_val_801_ = lean_ctor_get(v_ctx_x3f_791_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_ctx_x3f_791_, 1);
v___x_802_ = l_Lean_ppExprWithInfos(v_val_801_, v_e_790_);
v_val_794_ = v___x_802_;
goto v___jp_793_;
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_val_794_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_789_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_803_, lean_object* v_e_804_, lean_object* v_ctx_x3f_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_MessageData_ofExpr___lam__1(v___x_803_, v_e_804_, v_ctx_x3f_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_808_){
_start:
{
lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; 
lean_inc_ref(v_e_808_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_809_, 0, v_e_808_);
v___x_810_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_811_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_811_, 0, v___x_810_);
lean_closure_set(v___f_811_, 1, v_e_808_);
v___x_812_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_812_, 0, v___f_811_);
lean_ctor_set(v___x_812_, 1, v___f_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_box(0);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_MessageData_ofLevel___lam__0(v_x_815_);
lean_dec(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_817_, lean_object* v_l_818_, lean_object* v___f_819_, lean_object* v_ctx_x3f_820_){
_start:
{
lean_object* v_val_823_; 
if (lean_obj_tag(v_ctx_x3f_820_) == 0)
{
uint8_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = 1;
v___x_827_ = l_Lean_Level_format(v_l_818_, v___x_826_, v___f_819_);
v_val_823_ = v___x_827_;
goto v___jp_822_;
}
else
{
lean_object* v_val_828_; lean_object* v___x_829_; 
lean_dec_ref(v___f_819_);
v_val_828_ = lean_ctor_get(v_ctx_x3f_820_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v_ctx_x3f_820_, 1);
v___x_829_ = l_Lean_ppLevel(v_val_828_, v_l_818_);
v_val_823_ = v___x_829_;
goto v___jp_822_;
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_Lean_MessageData_ofFormat(v_val_823_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_817_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_830_, lean_object* v_l_831_, lean_object* v___f_832_, lean_object* v_ctx_x3f_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_MessageData_ofLevel___lam__2(v___x_830_, v_l_831_, v___f_832_, v_ctx_x3f_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_837_){
_start:
{
lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___f_841_; lean_object* v___x_842_; 
v___f_838_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_839_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_840_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_841_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_841_, 0, v___x_840_);
lean_closure_set(v___f_841_, 1, v_l_837_);
lean_closure_set(v___f_841_, 2, v___f_838_);
v___x_842_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_842_, 0, v___f_841_);
lean_ctor_set(v___x_842_, 1, v___f_839_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_843_){
_start:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_844_ = 1;
v___x_845_ = l_Lean_Name_toString(v_n_843_, v___x_844_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_851_, lean_object* v_k_852_, uint8_t v_v_853_){
_start:
{
lean_object* v_map_854_; uint8_t v_hasTrace_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_869_; 
v_map_854_ = lean_ctor_get(v_o_851_, 0);
v_hasTrace_855_ = lean_ctor_get_uint8(v_o_851_, sizeof(void*)*1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_o_851_);
if (v_isSharedCheck_869_ == 0)
{
v___x_857_ = v_o_851_;
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_map_854_);
lean_dec(v_o_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_859_, 0, v_v_853_);
lean_inc(v_k_852_);
v___x_860_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_852_, v___x_859_, v_map_854_);
if (v_hasTrace_855_ == 0)
{
lean_object* v___x_861_; uint8_t v___x_862_; lean_object* v___x_864_; 
v___x_861_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_862_ = l_Lean_Name_isPrefixOf(v___x_861_, v_k_852_);
lean_dec(v_k_852_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_864_ = v___x_857_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_860_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*1, v___x_862_);
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; 
lean_dec(v_k_852_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, sizeof(void*)*1, v_hasTrace_855_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_870_, lean_object* v_k_871_, lean_object* v_v_872_){
_start:
{
uint8_t v_v_boxed_873_; lean_object* v_res_874_; 
v_v_boxed_873_ = lean_unbox(v_v_872_);
v_res_874_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_870_, v_k_871_, v_v_boxed_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_880_, lean_object* v_constName_881_, uint8_t v_fullNames_882_, lean_object* v_ctx_x3f_883_){
_start:
{
lean_object* v_val_886_; lean_object* v___y_890_; 
if (lean_obj_tag(v_ctx_x3f_883_) == 0)
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_891_ = 1;
v___x_892_ = l_Lean_Name_toString(v_constName_881_, v___x_891_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = lean_box(1);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v_val_886_ = v___x_895_;
goto v___jp_885_;
}
else
{
if (v_fullNames_882_ == 0)
{
lean_object* v_val_896_; lean_object* v___x_897_; 
v_val_896_ = lean_ctor_get(v_ctx_x3f_883_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v_ctx_x3f_883_, 1);
v___x_897_ = l_Lean_ppConstNameWithInfos(v_val_896_, v_constName_881_);
v___y_890_ = v___x_897_;
goto v___jp_889_;
}
else
{
lean_object* v_val_898_; lean_object* v_env_899_; lean_object* v_mctx_900_; lean_object* v_lctx_901_; lean_object* v_opts_902_; lean_object* v_currNamespace_903_; lean_object* v_openDecls_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_val_898_ = lean_ctor_get(v_ctx_x3f_883_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v_ctx_x3f_883_, 1);
v_env_899_ = lean_ctor_get(v_val_898_, 0);
v_mctx_900_ = lean_ctor_get(v_val_898_, 1);
v_lctx_901_ = lean_ctor_get(v_val_898_, 2);
v_opts_902_ = lean_ctor_get(v_val_898_, 3);
v_currNamespace_903_ = lean_ctor_get(v_val_898_, 4);
v_openDecls_904_ = lean_ctor_get(v_val_898_, 5);
v_isSharedCheck_914_ = !lean_is_exclusive(v_val_898_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v_val_898_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_openDecls_904_);
lean_inc(v_currNamespace_903_);
lean_inc(v_opts_902_);
lean_inc(v_lctx_901_);
lean_inc(v_mctx_900_);
lean_inc(v_env_899_);
lean_dec(v_val_898_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_909_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_902_, v___x_908_, v_fullNames_882_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 3, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_env_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_mctx_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_lctx_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_currNamespace_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_openDecls_904_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_ppConstNameWithInfos(v___x_911_, v_constName_881_);
v___y_890_ = v___x_912_;
goto v___jp_889_;
}
}
}
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_val_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_880_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
v___jp_889_:
{
v_val_886_ = v___y_890_;
goto v___jp_885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_915_, lean_object* v_constName_916_, lean_object* v_fullNames_917_, lean_object* v_ctx_x3f_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_fullNames_boxed_920_; lean_object* v_res_921_; 
v_fullNames_boxed_920_ = lean_unbox(v_fullNames_917_);
v_res_921_ = l_Lean_MessageData_ofConstName___lam__1(v___x_915_, v_constName_916_, v_fullNames_boxed_920_, v_ctx_x3f_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_922_, uint8_t v_fullNames_923_){
_start:
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v___f_924_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_925_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_926_ = lean_box(v_fullNames_923_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_927_, 0, v___x_925_);
lean_closure_set(v___f_927_, 1, v_constName_922_);
lean_closure_set(v___f_927_, 2, v___x_926_);
v___x_928_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_928_, 0, v___f_927_);
lean_ctor_set(v___x_928_, 1, v___f_924_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_929_, lean_object* v_fullNames_930_){
_start:
{
uint8_t v_fullNames_boxed_931_; lean_object* v_res_932_; 
v_fullNames_boxed_931_ = lean_unbox(v_fullNames_930_);
v_res_932_ = l_Lean_MessageData_ofConstName(v_constName_929_, v_fullNames_boxed_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_val_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_MessageData_withExprHover___lam__0(v_val_937_, v___y_938_);
lean_dec_ref(v___y_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_941_, lean_object* v_v_942_, lean_object* v_t_943_){
_start:
{
if (lean_obj_tag(v_t_943_) == 0)
{
lean_object* v_size_944_; lean_object* v_k_945_; lean_object* v_v_946_; lean_object* v_l_947_; lean_object* v_r_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1229_; 
v_size_944_ = lean_ctor_get(v_t_943_, 0);
v_k_945_ = lean_ctor_get(v_t_943_, 1);
v_v_946_ = lean_ctor_get(v_t_943_, 2);
v_l_947_ = lean_ctor_get(v_t_943_, 3);
v_r_948_ = lean_ctor_get(v_t_943_, 4);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_t_943_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_950_ = v_t_943_;
v_isShared_951_ = v_isSharedCheck_1229_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_r_948_);
lean_inc(v_l_947_);
lean_inc(v_v_946_);
lean_inc(v_k_945_);
lean_inc(v_size_944_);
lean_dec(v_t_943_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1229_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_lt(v_k_941_, v_k_945_);
if (v___x_952_ == 0)
{
uint8_t v___x_953_; 
v___x_953_ = lean_nat_dec_eq(v_k_941_, v_k_945_);
if (v___x_953_ == 0)
{
lean_object* v_impl_954_; lean_object* v___x_955_; 
lean_dec(v_size_944_);
v_impl_954_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_941_, v_v_942_, v_r_948_);
v___x_955_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_947_) == 0)
{
lean_object* v_size_956_; lean_object* v_size_957_; lean_object* v_k_958_; lean_object* v_v_959_; lean_object* v_l_960_; lean_object* v_r_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_size_956_ = lean_ctor_get(v_l_947_, 0);
v_size_957_ = lean_ctor_get(v_impl_954_, 0);
lean_inc(v_size_957_);
v_k_958_ = lean_ctor_get(v_impl_954_, 1);
lean_inc(v_k_958_);
v_v_959_ = lean_ctor_get(v_impl_954_, 2);
lean_inc(v_v_959_);
v_l_960_ = lean_ctor_get(v_impl_954_, 3);
lean_inc(v_l_960_);
v_r_961_ = lean_ctor_get(v_impl_954_, 4);
lean_inc(v_r_961_);
v___x_962_ = lean_unsigned_to_nat(3u);
v___x_963_ = lean_nat_mul(v___x_962_, v_size_956_);
v___x_964_ = lean_nat_dec_lt(v___x_963_, v_size_957_);
lean_dec(v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v_r_961_);
lean_dec(v_l_960_);
lean_dec(v_v_959_);
lean_dec(v_k_958_);
v___x_965_ = lean_nat_add(v___x_955_, v_size_956_);
v___x_966_ = lean_nat_add(v___x_965_, v_size_957_);
lean_dec(v_size_957_);
lean_dec(v___x_965_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_impl_954_);
lean_ctor_set(v___x_950_, 0, v___x_966_);
v___x_968_ = v___x_950_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_l_947_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_impl_954_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1033_; 
v_isSharedCheck_1033_ = !lean_is_exclusive(v_impl_954_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; lean_object* v_unused_1037_; lean_object* v_unused_1038_; 
v_unused_1034_ = lean_ctor_get(v_impl_954_, 4);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_954_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_954_, 2);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_impl_954_, 1);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_impl_954_, 0);
lean_dec(v_unused_1038_);
v___x_971_ = v_impl_954_;
v_isShared_972_ = v_isSharedCheck_1033_;
goto v_resetjp_970_;
}
else
{
lean_dec(v_impl_954_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1033_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_size_973_; lean_object* v_k_974_; lean_object* v_v_975_; lean_object* v_l_976_; lean_object* v_r_977_; lean_object* v_size_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_size_973_ = lean_ctor_get(v_l_960_, 0);
v_k_974_ = lean_ctor_get(v_l_960_, 1);
v_v_975_ = lean_ctor_get(v_l_960_, 2);
v_l_976_ = lean_ctor_get(v_l_960_, 3);
v_r_977_ = lean_ctor_get(v_l_960_, 4);
v_size_978_ = lean_ctor_get(v_r_961_, 0);
v___x_979_ = lean_unsigned_to_nat(2u);
v___x_980_ = lean_nat_mul(v___x_979_, v_size_978_);
v___x_981_ = lean_nat_dec_lt(v_size_973_, v___x_980_);
lean_dec(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1009_; 
lean_inc(v_r_977_);
lean_inc(v_l_976_);
lean_inc(v_v_975_);
lean_inc(v_k_974_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_l_960_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; lean_object* v_unused_1014_; 
v_unused_1010_ = lean_ctor_get(v_l_960_, 4);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_l_960_, 3);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_l_960_, 2);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_l_960_, 1);
lean_dec(v_unused_1013_);
v_unused_1014_ = lean_ctor_get(v_l_960_, 0);
lean_dec(v_unused_1014_);
v___x_983_ = v_l_960_;
v_isShared_984_ = v_isSharedCheck_1009_;
goto v_resetjp_982_;
}
else
{
lean_dec(v_l_960_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1009_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_999_; 
v___x_985_ = lean_nat_add(v___x_955_, v_size_956_);
v___x_986_ = lean_nat_add(v___x_985_, v_size_957_);
lean_dec(v_size_957_);
if (lean_obj_tag(v_l_976_) == 0)
{
lean_object* v_size_1007_; 
v_size_1007_ = lean_ctor_get(v_l_976_, 0);
lean_inc(v_size_1007_);
v___y_999_ = v_size_1007_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_unsigned_to_nat(0u);
v___y_999_ = v___x_1008_;
goto v___jp_998_;
}
v___jp_987_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_nat_add(v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 4, v_r_961_);
lean_ctor_set(v___x_983_, 3, v_r_977_);
lean_ctor_set(v___x_983_, 2, v_v_959_);
lean_ctor_set(v___x_983_, 1, v_k_958_);
lean_ctor_set(v___x_983_, 0, v___x_991_);
v___x_993_ = v___x_983_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_k_958_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_v_959_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_r_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_r_961_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v___x_993_);
lean_ctor_set(v___x_971_, 3, v___y_988_);
lean_ctor_set(v___x_971_, 2, v_v_975_);
lean_ctor_set(v___x_971_, 1, v_k_974_);
lean_ctor_set(v___x_971_, 0, v___x_986_);
v___x_995_ = v___x_971_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_974_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_975_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v___y_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
v___jp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_nat_add(v___x_985_, v___y_999_);
lean_dec(v___y_999_);
lean_dec(v___x_985_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_l_976_);
lean_ctor_set(v___x_950_, 0, v___x_1000_);
v___x_1002_ = v___x_950_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_l_947_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_l_976_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_nat_add(v___x_955_, v_size_978_);
if (lean_obj_tag(v_r_977_) == 0)
{
lean_object* v_size_1004_; 
v_size_1004_ = lean_ctor_get(v_r_977_, 0);
lean_inc(v_size_1004_);
v___y_988_ = v___x_1002_;
v___y_989_ = v___x_1003_;
v___y_990_ = v_size_1004_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_unsigned_to_nat(0u);
v___y_988_ = v___x_1002_;
v___y_989_ = v___x_1003_;
v___y_990_ = v___x_1005_;
goto v___jp_987_;
}
}
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_del_object(v___x_950_);
v___x_1015_ = lean_nat_add(v___x_955_, v_size_956_);
v___x_1016_ = lean_nat_add(v___x_1015_, v_size_957_);
lean_dec(v_size_957_);
v___x_1017_ = lean_nat_add(v___x_1015_, v_size_973_);
lean_dec(v___x_1015_);
lean_inc_ref(v_l_947_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v_l_960_);
lean_ctor_set(v___x_971_, 3, v_l_947_);
lean_ctor_set(v___x_971_, 2, v_v_946_);
lean_ctor_set(v___x_971_, 1, v_k_945_);
lean_ctor_set(v___x_971_, 0, v___x_1017_);
v___x_1019_ = v___x_971_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_l_947_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_l_960_);
v___x_1019_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_isSharedCheck_1026_ = !lean_is_exclusive(v_l_947_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1027_ = lean_ctor_get(v_l_947_, 4);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_l_947_, 3);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_l_947_, 2);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_l_947_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_l_947_, 0);
lean_dec(v_unused_1031_);
v___x_1021_ = v_l_947_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v_l_947_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v_r_961_);
lean_ctor_set(v___x_1021_, 3, v___x_1019_);
lean_ctor_set(v___x_1021_, 2, v_v_959_);
lean_ctor_set(v___x_1021_, 1, v_k_958_);
lean_ctor_set(v___x_1021_, 0, v___x_1016_);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_958_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_959_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_r_961_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1039_; 
v_l_1039_ = lean_ctor_get(v_impl_954_, 3);
lean_inc(v_l_1039_);
if (lean_obj_tag(v_l_1039_) == 0)
{
lean_object* v_r_1040_; lean_object* v_k_1041_; lean_object* v_v_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1065_; 
v_r_1040_ = lean_ctor_get(v_impl_954_, 4);
v_k_1041_ = lean_ctor_get(v_impl_954_, 1);
v_v_1042_ = lean_ctor_get(v_impl_954_, 2);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_impl_954_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; 
v_unused_1066_ = lean_ctor_get(v_impl_954_, 3);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_impl_954_, 0);
lean_dec(v_unused_1067_);
v___x_1044_ = v_impl_954_;
v_isShared_1045_ = v_isSharedCheck_1065_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_r_1040_);
lean_inc(v_v_1042_);
lean_inc(v_k_1041_);
lean_dec(v_impl_954_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1065_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_k_1046_; lean_object* v_v_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1061_; 
v_k_1046_ = lean_ctor_get(v_l_1039_, 1);
v_v_1047_ = lean_ctor_get(v_l_1039_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_l_1039_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; lean_object* v_unused_1064_; 
v_unused_1062_ = lean_ctor_get(v_l_1039_, 4);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_l_1039_, 3);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_l_1039_, 0);
lean_dec(v_unused_1064_);
v___x_1049_ = v_l_1039_;
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_v_1047_);
lean_inc(v_k_1046_);
lean_dec(v_l_1039_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1040_, 2);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 4, v_r_1040_);
lean_ctor_set(v___x_1049_, 3, v_r_1040_);
lean_ctor_set(v___x_1049_, 2, v_v_946_);
lean_ctor_set(v___x_1049_, 1, v_k_945_);
lean_ctor_set(v___x_1049_, 0, v___x_955_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_r_1040_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_r_1040_);
v___x_1053_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
lean_inc(v_r_1040_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 3, v_r_1040_);
lean_ctor_set(v___x_1044_, 0, v___x_955_);
v___x_1055_ = v___x_1044_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_1041_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_1042_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_r_1040_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v_r_1040_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___x_1055_);
lean_ctor_set(v___x_950_, 3, v___x_1053_);
lean_ctor_set(v___x_950_, 2, v_v_1047_);
lean_ctor_set(v___x_950_, 1, v_k_1046_);
lean_ctor_set(v___x_950_, 0, v___x_1051_);
v___x_1057_ = v___x_950_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_1047_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
else
{
lean_object* v_r_1068_; 
v_r_1068_ = lean_ctor_get(v_impl_954_, 4);
lean_inc(v_r_1068_);
if (lean_obj_tag(v_r_1068_) == 0)
{
lean_object* v_k_1069_; lean_object* v_v_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1081_; 
v_k_1069_ = lean_ctor_get(v_impl_954_, 1);
v_v_1070_ = lean_ctor_get(v_impl_954_, 2);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_impl_954_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1082_ = lean_ctor_get(v_impl_954_, 4);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_impl_954_, 3);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_impl_954_, 0);
lean_dec(v_unused_1084_);
v___x_1072_ = v_impl_954_;
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_v_1070_);
lean_inc(v_k_1069_);
lean_dec(v_impl_954_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(3u);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_1039_);
lean_ctor_set(v___x_1072_, 2, v_v_946_);
lean_ctor_set(v___x_1072_, 1, v_k_945_);
lean_ctor_set(v___x_1072_, 0, v___x_955_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_l_1039_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_l_1039_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_r_1068_);
lean_ctor_set(v___x_950_, 3, v___x_1076_);
lean_ctor_set(v___x_950_, 2, v_v_1070_);
lean_ctor_set(v___x_950_, 1, v_k_1069_);
lean_ctor_set(v___x_950_, 0, v___x_1074_);
v___x_1078_ = v___x_950_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_1069_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_r_1068_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_unsigned_to_nat(2u);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_impl_954_);
lean_ctor_set(v___x_950_, 3, v_r_1068_);
lean_ctor_set(v___x_950_, 0, v___x_1085_);
v___x_1087_ = v___x_950_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_r_1068_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_impl_954_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v___x_1090_; 
lean_dec(v_v_946_);
lean_dec(v_k_945_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 2, v_v_942_);
lean_ctor_set(v___x_950_, 1, v_k_941_);
v___x_1090_ = v___x_950_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_size_944_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_941_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_942_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_l_947_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_r_948_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_impl_1092_; lean_object* v___x_1093_; 
lean_dec(v_size_944_);
v_impl_1092_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_941_, v_v_942_, v_l_947_);
v___x_1093_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_948_) == 0)
{
lean_object* v_size_1094_; lean_object* v_size_1095_; lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_l_1098_; lean_object* v_r_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_size_1094_ = lean_ctor_get(v_r_948_, 0);
v_size_1095_ = lean_ctor_get(v_impl_1092_, 0);
lean_inc(v_size_1095_);
v_k_1096_ = lean_ctor_get(v_impl_1092_, 1);
lean_inc(v_k_1096_);
v_v_1097_ = lean_ctor_get(v_impl_1092_, 2);
lean_inc(v_v_1097_);
v_l_1098_ = lean_ctor_get(v_impl_1092_, 3);
lean_inc(v_l_1098_);
v_r_1099_ = lean_ctor_get(v_impl_1092_, 4);
lean_inc(v_r_1099_);
v___x_1100_ = lean_unsigned_to_nat(3u);
v___x_1101_ = lean_nat_mul(v___x_1100_, v_size_1094_);
v___x_1102_ = lean_nat_dec_lt(v___x_1101_, v_size_1095_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v_r_1099_);
lean_dec(v_l_1098_);
lean_dec(v_v_1097_);
lean_dec(v_k_1096_);
v___x_1103_ = lean_nat_add(v___x_1093_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1104_ = lean_nat_add(v___x_1103_, v_size_1094_);
lean_dec(v___x_1103_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 3, v_impl_1092_);
lean_ctor_set(v___x_950_, 0, v___x_1104_);
v___x_1106_ = v___x_950_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_r_948_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1173_; 
v_isSharedCheck_1173_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1174_ = lean_ctor_get(v_impl_1092_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1092_, 2);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_impl_1092_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1178_);
v___x_1109_ = v_impl_1092_;
v_isShared_1110_ = v_isSharedCheck_1173_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_impl_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1173_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_size_1111_; lean_object* v_size_1112_; lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_l_1115_; lean_object* v_r_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_size_1111_ = lean_ctor_get(v_l_1098_, 0);
v_size_1112_ = lean_ctor_get(v_r_1099_, 0);
v_k_1113_ = lean_ctor_get(v_r_1099_, 1);
v_v_1114_ = lean_ctor_get(v_r_1099_, 2);
v_l_1115_ = lean_ctor_get(v_r_1099_, 3);
v_r_1116_ = lean_ctor_get(v_r_1099_, 4);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_nat_mul(v___x_1117_, v_size_1111_);
v___x_1119_ = lean_nat_dec_lt(v_size_1112_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1148_; 
lean_inc(v_r_1116_);
lean_inc(v_l_1115_);
lean_inc(v_v_1114_);
lean_inc(v_k_1113_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_r_1099_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1149_ = lean_ctor_get(v_r_1099_, 4);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1099_, 3);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1099_, 2);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1099_, 1);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_r_1099_, 0);
lean_dec(v_unused_1153_);
v___x_1121_ = v_r_1099_;
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v_r_1099_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___x_1136_; lean_object* v___y_1138_; 
v___x_1123_ = lean_nat_add(v___x_1093_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1124_ = lean_nat_add(v___x_1123_, v_size_1094_);
lean_dec(v___x_1123_);
v___x_1136_ = lean_nat_add(v___x_1093_, v_size_1111_);
if (lean_obj_tag(v_l_1115_) == 0)
{
lean_object* v_size_1146_; 
v_size_1146_ = lean_ctor_get(v_l_1115_, 0);
lean_inc(v_size_1146_);
v___y_1138_ = v_size_1146_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___y_1138_ = v___x_1147_;
goto v___jp_1137_;
}
v___jp_1125_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_nat_add(v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec(v___y_1127_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v_r_948_);
lean_ctor_set(v___x_1121_, 3, v_r_1116_);
lean_ctor_set(v___x_1121_, 2, v_v_946_);
lean_ctor_set(v___x_1121_, 1, v_k_945_);
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_r_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_948_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v___x_1131_);
lean_ctor_set(v___x_1109_, 3, v___y_1126_);
lean_ctor_set(v___x_1109_, 2, v_v_1114_);
lean_ctor_set(v___x_1109_, 1, v_k_1113_);
lean_ctor_set(v___x_1109_, 0, v___x_1124_);
v___x_1133_ = v___x_1109_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1113_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___y_1126_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_nat_add(v___x_1136_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec(v___x_1136_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_l_1115_);
lean_ctor_set(v___x_950_, 3, v_l_1098_);
lean_ctor_set(v___x_950_, 2, v_v_1097_);
lean_ctor_set(v___x_950_, 1, v_k_1096_);
lean_ctor_set(v___x_950_, 0, v___x_1139_);
v___x_1141_ = v___x_950_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_l_1115_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_nat_add(v___x_1093_, v_size_1094_);
if (lean_obj_tag(v_r_1116_) == 0)
{
lean_object* v_size_1143_; 
v_size_1143_ = lean_ctor_get(v_r_1116_, 0);
lean_inc(v_size_1143_);
v___y_1126_ = v___x_1141_;
v___y_1127_ = v___x_1142_;
v___y_1128_ = v_size_1143_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___y_1126_ = v___x_1141_;
v___y_1127_ = v___x_1142_;
v___y_1128_ = v___x_1144_;
goto v___jp_1125_;
}
}
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_del_object(v___x_950_);
v___x_1154_ = lean_nat_add(v___x_1093_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1155_ = lean_nat_add(v___x_1154_, v_size_1094_);
lean_dec(v___x_1154_);
v___x_1156_ = lean_nat_add(v___x_1093_, v_size_1094_);
v___x_1157_ = lean_nat_add(v___x_1156_, v_size_1112_);
lean_dec(v___x_1156_);
lean_inc_ref(v_r_948_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v_r_948_);
lean_ctor_set(v___x_1109_, 3, v_r_1099_);
lean_ctor_set(v___x_1109_, 2, v_v_946_);
lean_ctor_set(v___x_1109_, 1, v_k_945_);
lean_ctor_set(v___x_1109_, 0, v___x_1157_);
v___x_1159_ = v___x_1109_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_r_1099_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_r_948_);
v___x_1159_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v_r_948_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1167_ = lean_ctor_get(v_r_948_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_948_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_948_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_r_948_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_948_, 0);
lean_dec(v_unused_1171_);
v___x_1161_ = v_r_948_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_r_948_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 4, v___x_1159_);
lean_ctor_set(v___x_1161_, 3, v_l_1098_);
lean_ctor_set(v___x_1161_, 2, v_v_1097_);
lean_ctor_set(v___x_1161_, 1, v_k_1096_);
lean_ctor_set(v___x_1161_, 0, v___x_1155_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___x_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1179_; 
v_l_1179_ = lean_ctor_get(v_impl_1092_, 3);
lean_inc(v_l_1179_);
if (lean_obj_tag(v_l_1179_) == 0)
{
lean_object* v_r_1180_; lean_object* v_k_1181_; lean_object* v_v_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1193_; 
v_r_1180_ = lean_ctor_get(v_impl_1092_, 4);
v_k_1181_ = lean_ctor_get(v_impl_1092_, 1);
v_v_1182_ = lean_ctor_get(v_impl_1092_, 2);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1194_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1195_);
v___x_1184_ = v_impl_1092_;
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_r_1180_);
lean_inc(v_v_1182_);
lean_inc(v_k_1181_);
lean_dec(v_impl_1092_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 3, v_r_1180_);
lean_ctor_set(v___x_1184_, 2, v_v_946_);
lean_ctor_set(v___x_1184_, 1, v_k_945_);
lean_ctor_set(v___x_1184_, 0, v___x_1093_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_r_1180_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___x_1188_);
lean_ctor_set(v___x_950_, 3, v_l_1179_);
lean_ctor_set(v___x_950_, 2, v_v_1182_);
lean_ctor_set(v___x_950_, 1, v_k_1181_);
lean_ctor_set(v___x_950_, 0, v___x_1186_);
v___x_1190_ = v___x_950_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1182_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_r_1196_; 
v_r_1196_ = lean_ctor_get(v_impl_1092_, 4);
lean_inc(v_r_1196_);
if (lean_obj_tag(v_r_1196_) == 0)
{
lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1221_; 
v_k_1197_ = lean_ctor_get(v_impl_1092_, 1);
v_v_1198_ = lean_ctor_get(v_impl_1092_, 2);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1222_ = lean_ctor_get(v_impl_1092_, 4);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1224_);
v___x_1200_ = v_impl_1092_;
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_v_1198_);
lean_inc(v_k_1197_);
lean_dec(v_impl_1092_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1217_; 
v_k_1202_ = lean_ctor_get(v_r_1196_, 1);
v_v_1203_ = lean_ctor_get(v_r_1196_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_r_1196_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; 
v_unused_1218_ = lean_ctor_get(v_r_1196_, 4);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_r_1196_, 3);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_r_1196_, 0);
lean_dec(v_unused_1220_);
v___x_1205_ = v_r_1196_;
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_dec(v_r_1196_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(3u);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v_l_1179_);
lean_ctor_set(v___x_1205_, 3, v_l_1179_);
lean_ctor_set(v___x_1205_, 2, v_v_1198_);
lean_ctor_set(v___x_1205_, 1, v_k_1197_);
lean_ctor_set(v___x_1205_, 0, v___x_1093_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_l_1179_);
v___x_1209_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_l_1179_);
lean_ctor_set(v___x_1200_, 2, v_v_946_);
lean_ctor_set(v___x_1200_, 1, v_k_945_);
lean_ctor_set(v___x_1200_, 0, v___x_1093_);
v___x_1211_ = v___x_1200_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_l_1179_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___x_1211_);
lean_ctor_set(v___x_950_, 3, v___x_1209_);
lean_ctor_set(v___x_950_, 2, v_v_1203_);
lean_ctor_set(v___x_950_, 1, v_k_1202_);
lean_ctor_set(v___x_950_, 0, v___x_1207_);
v___x_1213_ = v___x_950_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(2u);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v_r_1196_);
lean_ctor_set(v___x_950_, 3, v_impl_1092_);
lean_ctor_set(v___x_950_, 0, v___x_1225_);
v___x_1227_ = v___x_950_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1196_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_k_941_);
lean_ctor_set(v___x_1231_, 2, v_v_942_);
lean_ctor_set(v___x_1231_, 3, v_t_943_);
lean_ctor_set(v___x_1231_, 4, v_t_943_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1232_, lean_object* v_b_1233_){
_start:
{
if (lean_obj_tag(v_as_x27_1232_) == 0)
{
return v_b_1233_;
}
else
{
lean_object* v_head_1234_; lean_object* v_tail_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; lean_object* v_r_1238_; 
v_head_1234_ = lean_ctor_get(v_as_x27_1232_, 0);
v_tail_1235_ = lean_ctor_get(v_as_x27_1232_, 1);
v_fst_1236_ = lean_ctor_get(v_head_1234_, 0);
v_snd_1237_ = lean_ctor_get(v_head_1234_, 1);
lean_inc(v_snd_1237_);
lean_inc(v_fst_1236_);
v_r_1238_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1236_, v_snd_1237_, v_b_1233_);
v_as_x27_1232_ = v_tail_1235_;
v_b_1233_ = v_r_1238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1240_, lean_object* v_b_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1240_, v_b_1241_);
lean_dec(v_as_x27_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1251_, lean_object* v_expr_1252_, lean_object* v_lctx_1253_, lean_object* v_location_x3f_1254_, lean_object* v_docString_x3f_1255_, lean_object* v_mkDocString_x3f_1256_, uint8_t v_explicit_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___y_1265_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_fmt_1251_);
v___x_1260_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1261_ = lean_box(0);
v___x_1262_ = 0;
v___x_1263_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1263_, 0, v___x_1260_);
lean_ctor_set(v___x_1263_, 1, v_lctx_1253_);
lean_ctor_set(v___x_1263_, 2, v___x_1261_);
lean_ctor_set(v___x_1263_, 3, v_expr_1252_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*4, v___x_1262_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*4 + 1, v___x_1262_);
if (lean_obj_tag(v_mkDocString_x3f_1256_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1255_) == 0)
{
v___y_1265_ = v_mkDocString_x3f_1256_;
goto v___jp_1264_;
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_val_1275_ = lean_ctor_get(v_docString_x3f_1255_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_docString_x3f_1255_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1277_ = v_docString_x3f_1255_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v_docString_x3f_1255_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___f_1279_; lean_object* v___x_1281_; 
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1279_, 0, v_val_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___f_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___f_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v___y_1265_ = v___x_1281_;
goto v___jp_1264_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1255_);
v___y_1265_ = v_mkDocString_x3f_1256_;
goto v___jp_1264_;
}
v___jp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_r_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1263_);
lean_ctor_set(v___x_1266_, 1, v_location_x3f_1254_);
lean_ctor_set(v___x_1266_, 2, v___y_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*3, v_explicit_1257_);
v___x_1267_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1258_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v_r_1271_ = lean_box(1);
v___x_1272_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1270_, v_r_1271_);
lean_dec_ref_known(v___x_1270_, 2);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1259_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1284_, lean_object* v_expr_1285_, lean_object* v_lctx_1286_, lean_object* v_location_x3f_1287_, lean_object* v_docString_x3f_1288_, lean_object* v_mkDocString_x3f_1289_, lean_object* v_explicit_1290_){
_start:
{
uint8_t v_explicit_boxed_1291_; lean_object* v_res_1292_; 
v_explicit_boxed_1291_ = lean_unbox(v_explicit_1290_);
v_res_1292_ = l_Lean_MessageData_withExprHover(v_fmt_1284_, v_expr_1285_, v_lctx_1286_, v_location_x3f_1287_, v_docString_x3f_1288_, v_mkDocString_x3f_1289_, v_explicit_boxed_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1293_, lean_object* v_k_1294_, lean_object* v_v_1295_, lean_object* v_t_1296_, lean_object* v_hl_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1294_, v_v_1295_, v_t_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1299_, lean_object* v_as_x27_1300_, lean_object* v_b_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1300_, v_b_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1304_, lean_object* v_as_x27_1305_, lean_object* v_b_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1304_, v_as_x27_1305_, v_b_1306_, v_a_1307_);
lean_dec(v_as_x27_1305_);
lean_dec(v_as_1304_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1309_, lean_object* v_expr_1310_, lean_object* v_location_x3f_1311_, lean_object* v_docString_x3f_1312_, lean_object* v_mkDocString_x3f_1313_, uint8_t v_explicit_1314_, lean_object* v_toPure_1315_, lean_object* v_lctx_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = l_Lean_MessageData_withExprHover(v_fmt_1309_, v_expr_1310_, v_lctx_1316_, v_location_x3f_1311_, v_docString_x3f_1312_, v_mkDocString_x3f_1313_, v_explicit_1314_);
v___x_1318_ = lean_apply_2(v_toPure_1315_, lean_box(0), v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1319_, lean_object* v_expr_1320_, lean_object* v_location_x3f_1321_, lean_object* v_docString_x3f_1322_, lean_object* v_mkDocString_x3f_1323_, lean_object* v_explicit_1324_, lean_object* v_toPure_1325_, lean_object* v_lctx_1326_){
_start:
{
uint8_t v_explicit_boxed_1327_; lean_object* v_res_1328_; 
v_explicit_boxed_1327_ = lean_unbox(v_explicit_1324_);
v_res_1328_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1319_, v_expr_1320_, v_location_x3f_1321_, v_docString_x3f_1322_, v_mkDocString_x3f_1323_, v_explicit_boxed_1327_, v_toPure_1325_, v_lctx_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_fmt_1331_, lean_object* v_expr_1332_, lean_object* v_lctx_x3f_1333_, lean_object* v_location_x3f_1334_, lean_object* v_docString_x3f_1335_, lean_object* v_mkDocString_x3f_1336_, uint8_t v_explicit_1337_){
_start:
{
lean_object* v_toApplicative_1338_; lean_object* v_toBind_1339_; lean_object* v_toPure_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; 
v_toApplicative_1338_ = lean_ctor_get(v_inst_1329_, 0);
lean_inc_ref(v_toApplicative_1338_);
v_toBind_1339_ = lean_ctor_get(v_inst_1329_, 1);
lean_inc(v_toBind_1339_);
lean_dec_ref(v_inst_1329_);
v_toPure_1340_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_inc_n(v_toPure_1340_, 2);
lean_dec_ref(v_toApplicative_1338_);
v___x_1341_ = lean_box(v_explicit_1337_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1342_, 0, v_fmt_1331_);
lean_closure_set(v___f_1342_, 1, v_expr_1332_);
lean_closure_set(v___f_1342_, 2, v_location_x3f_1334_);
lean_closure_set(v___f_1342_, 3, v_docString_x3f_1335_);
lean_closure_set(v___f_1342_, 4, v_mkDocString_x3f_1336_);
lean_closure_set(v___f_1342_, 5, v___x_1341_);
lean_closure_set(v___f_1342_, 6, v_toPure_1340_);
if (lean_obj_tag(v_lctx_x3f_1333_) == 0)
{
lean_object* v___x_1343_; 
lean_dec(v_toPure_1340_);
v___x_1343_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v_inst_1330_, v___f_1342_);
return v___x_1343_;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_inst_1330_);
v_val_1344_ = lean_ctor_get(v_lctx_x3f_1333_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v_lctx_x3f_1333_, 1);
v___x_1345_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_val_1344_);
v___x_1346_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1345_, v___f_1342_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_fmt_1349_, lean_object* v_expr_1350_, lean_object* v_lctx_x3f_1351_, lean_object* v_location_x3f_1352_, lean_object* v_docString_x3f_1353_, lean_object* v_mkDocString_x3f_1354_, lean_object* v_explicit_1355_){
_start:
{
uint8_t v_explicit_boxed_1356_; lean_object* v_res_1357_; 
v_explicit_boxed_1356_ = lean_unbox(v_explicit_1355_);
v_res_1357_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1347_, v_inst_1348_, v_fmt_1349_, v_expr_1350_, v_lctx_x3f_1351_, v_location_x3f_1352_, v_docString_x3f_1353_, v_mkDocString_x3f_1354_, v_explicit_boxed_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_fmt_1361_, lean_object* v_expr_1362_, lean_object* v_lctx_x3f_1363_, lean_object* v_location_x3f_1364_, lean_object* v_docString_x3f_1365_, lean_object* v_mkDocString_x3f_1366_, uint8_t v_explicit_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1359_, v_inst_1360_, v_fmt_1361_, v_expr_1362_, v_lctx_x3f_1363_, v_location_x3f_1364_, v_docString_x3f_1365_, v_mkDocString_x3f_1366_, v_explicit_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1369_, lean_object* v_inst_1370_, lean_object* v_inst_1371_, lean_object* v_fmt_1372_, lean_object* v_expr_1373_, lean_object* v_lctx_x3f_1374_, lean_object* v_location_x3f_1375_, lean_object* v_docString_x3f_1376_, lean_object* v_mkDocString_x3f_1377_, lean_object* v_explicit_1378_){
_start:
{
uint8_t v_explicit_boxed_1379_; lean_object* v_res_1380_; 
v_explicit_boxed_1379_ = lean_unbox(v_explicit_1378_);
v_res_1380_ = l_Lean_MessageData_withExprHoverM(v_m_1369_, v_inst_1370_, v_inst_1371_, v_fmt_1372_, v_expr_1373_, v_lctx_x3f_1374_, v_location_x3f_1375_, v_docString_x3f_1376_, v_mkDocString_x3f_1377_, v_explicit_boxed_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1381_, lean_object* v_display_1382_, lean_object* v_toPure_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_____do__lift_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1386_, v_userName_1381_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_inst_1385_);
lean_dec_ref(v_inst_1384_);
v___x_1388_ = l_Lean_MessageData_ofName(v_display_1382_);
v___x_1389_ = lean_apply_2(v_toPure_1383_, lean_box(0), v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_toPure_1383_);
v_val_1390_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1392_ = v___x_1387_;
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v___x_1387_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Name_toString(v_display_1382_, v___x_1394_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 3);
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = l_Lean_LocalDecl_fvarId(v_val_1390_);
lean_dec(v_val_1390_);
v___x_1399_ = l_Lean_Expr_fvar___override(v___x_1398_);
v___x_1400_ = lean_box(0);
v___x_1401_ = 0;
v___x_1402_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1384_, v_inst_1385_, v___x_1397_, v___x_1399_, v___x_1400_, v___x_1400_, v___x_1400_, v___x_1400_, v___x_1401_);
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1405_, lean_object* v_display_1406_, lean_object* v_toPure_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_____do__lift_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1405_, v_display_1406_, v_toPure_1407_, v_inst_1408_, v_inst_1409_, v_____do__lift_1410_);
lean_dec_ref(v_____do__lift_1410_);
lean_dec(v_userName_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_userName_1414_){
_start:
{
lean_object* v_toApplicative_1415_; lean_object* v_toBind_1416_; lean_object* v_toPure_1417_; lean_object* v_display_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; 
v_toApplicative_1415_ = lean_ctor_get(v_inst_1412_, 0);
v_toBind_1416_ = lean_ctor_get(v_inst_1412_, 1);
lean_inc(v_toBind_1416_);
v_toPure_1417_ = lean_ctor_get(v_toApplicative_1415_, 1);
lean_inc(v_toPure_1417_);
lean_inc(v_userName_1414_);
v_display_1418_ = l_Lean_Name_simpMacroScopes(v_userName_1414_);
lean_inc(v_inst_1413_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1419_, 0, v_userName_1414_);
lean_closure_set(v___f_1419_, 1, v_display_1418_);
lean_closure_set(v___f_1419_, 2, v_toPure_1417_);
lean_closure_set(v___f_1419_, 3, v_inst_1412_);
lean_closure_set(v___f_1419_, 4, v_inst_1413_);
v___x_1420_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v_inst_1413_, v___f_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_userName_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1422_, v_inst_1423_, v_userName_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1426_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_ctor_set(v___x_1431_, 2, v___x_1430_);
lean_ctor_set(v___x_1431_, 3, v___x_1430_);
lean_ctor_set(v___x_1431_, 4, v___x_1429_);
lean_ctor_set(v___x_1431_, 5, v___x_1429_);
lean_ctor_set(v___x_1431_, 6, v___x_1429_);
lean_ctor_set(v___x_1431_, 7, v___x_1429_);
lean_ctor_set(v___x_1431_, 8, v___x_1429_);
lean_ctor_set(v___x_1431_, 9, v___x_1429_);
lean_ctor_set(v___x_1431_, 10, v___x_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1432_, lean_object* v_a_1433_){
_start:
{
switch(lean_obj_tag(v_a_1433_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1432_) == 0)
{
lean_object* v_hasSyntheticSorry_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_hasSyntheticSorry_1434_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_hasSyntheticSorry_1434_);
lean_dec_ref_known(v_a_1433_, 2);
v___x_1435_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1436_ = lean_apply_1(v_hasSyntheticSorry_1434_, v___x_1435_);
v___x_1437_ = lean_unbox(v___x_1436_);
return v___x_1437_;
}
else
{
lean_object* v_hasSyntheticSorry_1438_; lean_object* v_val_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_hasSyntheticSorry_1438_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_hasSyntheticSorry_1438_);
lean_dec_ref_known(v_a_1433_, 2);
v_val_1439_ = lean_ctor_get(v_mctx_x3f_1432_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v_mctx_x3f_1432_, 1);
v___x_1440_ = lean_apply_1(v_hasSyntheticSorry_1438_, v_val_1439_);
v___x_1441_ = lean_unbox(v___x_1440_);
return v___x_1441_;
}
}
case 3:
{
lean_object* v_a_1442_; lean_object* v_a_1443_; lean_object* v_mctx_1444_; lean_object* v___x_1445_; 
lean_dec(v_mctx_x3f_1432_);
v_a_1442_ = lean_ctor_get(v_a_1433_, 0);
lean_inc_ref(v_a_1442_);
v_a_1443_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1443_);
lean_dec_ref_known(v_a_1433_, 2);
v_mctx_1444_ = lean_ctor_get(v_a_1442_, 1);
lean_inc_ref(v_mctx_1444_);
lean_dec_ref(v_a_1442_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_mctx_1444_);
v_mctx_x3f_1432_ = v___x_1445_;
v_a_1433_ = v_a_1443_;
goto _start;
}
case 4:
{
lean_object* v_a_1447_; 
v_a_1447_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1447_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_a_1447_;
goto _start;
}
case 5:
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1449_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_a_1449_;
goto _start;
}
case 6:
{
lean_object* v_a_1451_; 
v_a_1451_ = lean_ctor_get(v_a_1433_, 0);
lean_inc_ref(v_a_1451_);
lean_dec_ref_known(v_a_1433_, 1);
v_a_1433_ = v_a_1451_;
goto _start;
}
case 7:
{
lean_object* v_a_1453_; lean_object* v_a_1454_; uint8_t v___x_1455_; 
v_a_1453_ = lean_ctor_get(v_a_1433_, 0);
lean_inc_ref(v_a_1453_);
v_a_1454_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1454_);
lean_dec_ref_known(v_a_1433_, 2);
lean_inc(v_mctx_x3f_1432_);
v___x_1455_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1432_, v_a_1453_);
if (v___x_1455_ == 0)
{
v_a_1433_ = v_a_1454_;
goto _start;
}
else
{
lean_dec_ref(v_a_1454_);
lean_dec(v_mctx_x3f_1432_);
return v___x_1455_;
}
}
case 8:
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1457_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_a_1457_;
goto _start;
}
case 11:
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1459_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_a_1459_;
goto _start;
}
case 12:
{
lean_object* v_a_1461_; 
v_a_1461_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_a_1461_);
lean_dec_ref_known(v_a_1433_, 2);
v_a_1433_ = v_a_1461_;
goto _start;
}
case 9:
{
lean_object* v_msg_1463_; lean_object* v_children_1464_; uint8_t v___x_1465_; 
v_msg_1463_ = lean_ctor_get(v_a_1433_, 1);
lean_inc_ref(v_msg_1463_);
v_children_1464_ = lean_ctor_get(v_a_1433_, 2);
lean_inc_ref(v_children_1464_);
lean_dec_ref_known(v_a_1433_, 3);
lean_inc(v_mctx_x3f_1432_);
v___x_1465_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1432_, v_msg_1463_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_array_get_size(v_children_1464_);
v___x_1468_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v_children_1464_);
lean_dec(v_mctx_x3f_1432_);
return v___x_1468_;
}
else
{
if (v___x_1468_ == 0)
{
lean_dec_ref(v_children_1464_);
lean_dec(v_mctx_x3f_1432_);
return v___x_1468_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1467_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1432_, v_children_1464_, v___x_1469_, v___x_1470_);
lean_dec_ref(v_children_1464_);
return v___x_1471_;
}
}
}
else
{
lean_dec_ref(v_children_1464_);
lean_dec(v_mctx_x3f_1432_);
return v___x_1465_;
}
}
default: 
{
uint8_t v___x_1472_; 
lean_dec_ref(v_a_1433_);
lean_dec(v_mctx_x3f_1432_);
v___x_1472_ = 0;
return v___x_1472_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1473_, lean_object* v_as_1474_, size_t v_i_1475_, size_t v_stop_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_usize_dec_eq(v_i_1475_, v_stop_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_array_uget_borrowed(v_as_1474_, v_i_1475_);
lean_inc(v___x_1478_);
lean_inc(v_mctx_x3f_1473_);
v___x_1479_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1473_, v___x_1478_);
if (v___x_1479_ == 0)
{
size_t v___x_1480_; size_t v___x_1481_; 
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_add(v_i_1475_, v___x_1480_);
v_i_1475_ = v___x_1481_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1473_);
return v___x_1479_;
}
}
else
{
uint8_t v___x_1483_; 
lean_dec(v_mctx_x3f_1473_);
v___x_1483_ = 0;
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1484_, lean_object* v_as_1485_, lean_object* v_i_1486_, lean_object* v_stop_1487_){
_start:
{
size_t v_i_boxed_1488_; size_t v_stop_boxed_1489_; uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_i_boxed_1488_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_stop_boxed_1489_ = lean_unbox_usize(v_stop_1487_);
lean_dec(v_stop_1487_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1484_, v_as_1485_, v_i_boxed_1488_, v_stop_boxed_1489_);
lean_dec_ref(v_as_1485_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1492_, lean_object* v_a_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1492_, v_a_1493_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1496_){
_start:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1497_, v_msg_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1499_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_1502_, lean_object* v_decl_1503_, lean_object* v_ref_1504_){
_start:
{
lean_object* v_defValue_1506_; lean_object* v_descr_1507_; lean_object* v_deprecation_x3f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_defValue_1506_ = lean_ctor_get(v_decl_1503_, 0);
v_descr_1507_ = lean_ctor_get(v_decl_1503_, 1);
v_deprecation_x3f_1508_ = lean_ctor_get(v_decl_1503_, 2);
lean_inc(v_defValue_1506_);
v___x_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_defValue_1506_);
lean_inc(v_deprecation_x3f_1508_);
lean_inc_ref(v_descr_1507_);
lean_inc_n(v_name_1502_, 2);
v___x_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1510_, 0, v_name_1502_);
lean_ctor_set(v___x_1510_, 1, v_ref_1504_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
lean_ctor_set(v___x_1510_, 3, v_descr_1507_);
lean_ctor_set(v___x_1510_, 4, v_deprecation_x3f_1508_);
v___x_1511_ = lean_register_option(v_name_1502_, v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1511_, 0);
lean_dec(v_unused_1520_);
v___x_1513_ = v___x_1511_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v___x_1511_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_inc(v_defValue_1506_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_name_1502_);
lean_ctor_set(v___x_1515_, 1, v_defValue_1506_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1515_);
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_name_1502_);
v_a_1521_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1511_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1511_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1529_, lean_object* v_decl_1530_, lean_object* v_ref_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_1529_, v_decl_1530_, v_ref_1531_);
lean_dec_ref(v_decl_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1548_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1549_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1550_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_1547_, v___x_1548_, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_nat_to_int(v_a_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_box(0);
v___x_1556_ = l_instMonadBaseIO;
v___x_1557_ = l_instInhabitedOfMonad___redArg(v___x_1556_, v___x_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1843__overap_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1843__overap_1561_ = lean_panic_fn_borrowed(v___x_1560_, v_msg_1558_);
v___x_1562_ = lean_apply_1(v___x_1843__overap_1561_, lean_box(0));
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1568_) == 0)
{
lean_dec(v_x_1566_);
return v_x_1567_;
}
else
{
lean_object* v_head_1569_; lean_object* v_tail_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
v_head_1569_ = lean_ctor_get(v_x_1568_, 0);
v_tail_1570_ = lean_ctor_get(v_x_1568_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1572_ = v_x_1568_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_tail_1570_);
lean_inc(v_head_1569_);
lean_dec(v_x_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
lean_inc(v_x_1566_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 5);
lean_ctor_set(v___x_1572_, 1, v_x_1566_);
lean_ctor_set(v___x_1572_, 0, v_x_1567_);
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_x_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_x_1566_);
v___x_1575_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v_head_1569_);
v_x_1567_ = v___x_1576_;
v_x_1568_ = v_tail_1570_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v___x_1582_; 
lean_dec(v_x_1581_);
v___x_1582_ = lean_box(0);
return v___x_1582_;
}
else
{
lean_object* v_tail_1583_; 
v_tail_1583_ = lean_ctor_get(v_x_1580_, 1);
if (lean_obj_tag(v_tail_1583_) == 0)
{
lean_object* v_head_1584_; 
lean_dec(v_x_1581_);
v_head_1584_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_head_1584_);
lean_dec_ref_known(v_x_1580_, 2);
return v_head_1584_;
}
else
{
lean_object* v_head_1585_; lean_object* v___x_1586_; 
lean_inc(v_tail_1583_);
v_head_1585_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_head_1585_);
lean_dec_ref_known(v_x_1580_, 2);
v___x_1586_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1581_, v_head_1585_, v_tail_1583_);
return v___x_1586_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1601_; double v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_float_of_nat(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
switch(lean_obj_tag(v_x_1608_))
{
case 0:
{
lean_object* v_a_1610_; lean_object* v_fmt_1611_; 
lean_dec(v_x_1607_);
lean_dec_ref(v_x_1606_);
v_a_1610_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_a_1610_);
lean_dec_ref_known(v_x_1608_, 1);
v_fmt_1611_ = lean_ctor_get(v_a_1610_, 0);
lean_inc(v_fmt_1611_);
lean_dec_ref(v_a_1610_);
return v_fmt_1611_;
}
case 1:
{
if (lean_obj_tag(v_x_1607_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v_x_1606_);
v_a_1612_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v_x_1608_, 1);
v___x_1613_ = l_Lean_formatRawGoal(v_a_1612_);
return v___x_1613_;
}
else
{
lean_object* v_a_1614_; lean_object* v_val_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_a_1614_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v_x_1608_, 1);
v_val_1615_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v_x_1607_, 1);
v___x_1616_ = l_Lean_MessageData_mkPPContext(v_x_1606_, v_val_1615_);
lean_dec(v_val_1615_);
lean_dec_ref(v_x_1606_);
v___x_1617_ = l_Lean_ppGoal(v___x_1616_, v_a_1614_);
return v___x_1617_;
}
}
case 3:
{
lean_object* v_a_1618_; lean_object* v_a_1619_; lean_object* v___x_1620_; 
lean_dec(v_x_1607_);
v_a_1618_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_a_1618_);
v_a_1619_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_ref(v_a_1619_);
lean_dec_ref_known(v_x_1608_, 2);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_a_1618_);
v_x_1607_ = v___x_1620_;
v_x_1608_ = v_a_1619_;
goto _start;
}
case 4:
{
lean_object* v_a_1622_; lean_object* v_a_1623_; 
lean_dec_ref(v_x_1606_);
v_a_1622_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_a_1622_);
v_a_1623_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_ref(v_a_1623_);
lean_dec_ref_known(v_x_1608_, 2);
v_x_1606_ = v_a_1622_;
v_x_1608_ = v_a_1623_;
goto _start;
}
case 5:
{
lean_object* v_a_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1635_; 
v_a_1625_ = lean_ctor_get(v_x_1608_, 0);
v_a_1626_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1628_ = v_x_1608_;
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_inc(v_a_1625_);
lean_dec(v_x_1608_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1635_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = l_Lean_MessageData_formatAux(v_x_1606_, v_x_1607_, v_a_1626_);
v___x_1631_ = lean_nat_to_int(v_a_1625_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 4);
lean_ctor_set(v___x_1628_, 1, v___x_1630_);
lean_ctor_set(v___x_1628_, 0, v___x_1631_);
v___x_1633_ = v___x_1628_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1630_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
case 6:
{
lean_object* v_a_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_a_1636_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_a_1636_);
lean_dec_ref_known(v_x_1608_, 1);
v___x_1637_ = l_Lean_MessageData_formatAux(v_x_1606_, v_x_1607_, v_a_1636_);
v___x_1638_ = 0;
v___x_1639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*1, v___x_1638_);
return v___x_1639_;
}
case 7:
{
lean_object* v_a_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
v_a_1640_ = lean_ctor_get(v_x_1608_, 0);
v_a_1641_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1643_ = v_x_1608_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_inc(v_a_1640_);
lean_dec(v_x_1608_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_inc(v_x_1607_);
lean_inc_ref(v_x_1606_);
v___x_1645_ = l_Lean_MessageData_formatAux(v_x_1606_, v_x_1607_, v_a_1640_);
v___x_1646_ = l_Lean_MessageData_formatAux(v_x_1606_, v_x_1607_, v_a_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 5);
lean_ctor_set(v___x_1643_, 1, v___x_1646_);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
case 9:
{
lean_object* v_data_1651_; lean_object* v_msg_1652_; lean_object* v_children_1653_; size_t v_sz_1654_; size_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v_cls_1670_; lean_object* v_result_x3f_1671_; double v_startTime_1672_; double v_stopTime_1673_; lean_object* v_msg_1675_; uint8_t v___x_1690_; 
v_data_1651_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_data_1651_);
v_msg_1652_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_ref(v_msg_1652_);
v_children_1653_ = lean_ctor_get(v_x_1608_, 2);
lean_inc_ref(v_children_1653_);
lean_dec_ref_known(v_x_1608_, 3);
v_sz_1654_ = lean_array_size(v_children_1653_);
v___x_1655_ = ((size_t)0ULL);
lean_inc(v_x_1607_);
lean_inc_ref(v_x_1606_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1606_, v_x_1607_, v_sz_1654_, v___x_1655_, v_children_1653_);
v_cls_1670_ = lean_ctor_get(v_data_1651_, 0);
lean_inc(v_cls_1670_);
v_result_x3f_1671_ = lean_ctor_get(v_data_1651_, 1);
lean_inc(v_result_x3f_1671_);
v_startTime_1672_ = lean_ctor_get_float(v_data_1651_, sizeof(void*)*3);
v_stopTime_1673_ = lean_ctor_get_float(v_data_1651_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1651_);
v___x_1690_ = l_Lean_Name_isAnonymous(v_cls_1670_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; double v___x_1706_; uint8_t v___x_1707_; 
v___x_1691_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1692_ = 1;
v___x_1693_ = l_Lean_Name_toString(v_cls_1670_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1691_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1706_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1707_ = lean_float_beq(v_startTime_1672_, v___x_1706_);
if (v___x_1707_ == 0)
{
goto v___jp_1698_;
}
else
{
if (v___x_1690_ == 0)
{
v_msg_1675_ = v___x_1697_;
goto v___jp_1674_;
}
else
{
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; double v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1699_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1697_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_float_sub(v_stopTime_1673_, v_startTime_1672_);
v___x_1702_ = lean_float_to_string(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1700_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1696_);
v_msg_1675_ = v___x_1705_;
goto v___jp_1674_;
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_result_x3f_1671_);
lean_dec(v_cls_1670_);
lean_dec_ref(v_msg_1652_);
lean_dec(v_x_1607_);
lean_dec_ref(v_x_1606_);
v___x_1708_ = lean_array_to_list(v___x_1656_);
v___x_1709_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1710_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1708_, v___x_1709_);
return v___x_1710_;
}
v___jp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1660_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1658_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___y_1659_);
v___x_1664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1661_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_array_to_list(v___x_1656_);
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1668_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1666_, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1662_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
return v___x_1669_;
}
v___jp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_MessageData_formatAux(v_x_1606_, v_x_1607_, v_msg_1652_);
if (lean_obj_tag(v_result_x3f_1671_) == 0)
{
v___y_1658_ = v_msg_1675_;
v___y_1659_ = v___x_1676_;
goto v___jp_1657_;
}
else
{
lean_object* v_val_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1689_; 
v_val_1677_ = lean_ctor_get(v_result_x3f_1671_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_result_x3f_1671_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1679_ = v_result_x3f_1671_;
v_isShared_1680_ = v_isSharedCheck_1689_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_val_1677_);
lean_dec(v_result_x3f_1671_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1689_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1681_ = lean_unbox(v_val_1677_);
lean_dec(v_val_1677_);
v___x_1682_ = l_Lean_TraceResult_toEmoji(v___x_1681_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 3);
lean_ctor_set(v___x_1679_, 0, v___x_1682_);
v___x_1684_ = v___x_1679_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1676_);
v___y_1658_ = v_msg_1675_;
v___y_1659_ = v___x_1687_;
goto v___jp_1657_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1711_; lean_object* v___x_1712_; lean_object* v___y_1714_; 
v_f_1711_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_f_1711_);
lean_dec_ref_known(v_x_1608_, 2);
v___x_1712_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
if (lean_obj_tag(v_x_1607_) == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_box(0);
v___y_1714_ = v___x_1730_;
goto v___jp_1713_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1731_ = lean_ctor_get(v_x_1607_, 0);
v___x_1732_ = l_Lean_MessageData_mkPPContext(v_x_1606_, v_val_1731_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___y_1714_ = v___x_1733_;
goto v___jp_1713_;
}
v___jp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_apply_2(v_f_1711_, v___y_1714_, lean_box(0));
v___x_1716_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1715_, v___x_1712_);
if (lean_obj_tag(v___x_1716_) == 1)
{
lean_object* v_val_1717_; 
lean_dec(v___x_1715_);
v_val_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v_x_1608_ = v_val_1717_;
goto _start;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v___x_1716_);
lean_dec(v_x_1607_);
lean_dec_ref(v_x_1606_);
v___x_1719_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1720_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1721_ = lean_unsigned_to_nat(434u);
v___x_1722_ = lean_unsigned_to_nat(8u);
v___x_1723_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1724_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1715_);
lean_dec(v___x_1715_);
v___x_1725_ = 1;
v___x_1726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1724_, v___x_1725_);
v___x_1727_ = lean_string_append(v___x_1723_, v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = l_mkPanicMessageWithDecl(v___x_1719_, v___x_1720_, v___x_1721_, v___x_1722_, v___x_1727_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1728_);
return v___x_1729_;
}
}
}
default: 
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_ref(v_a_1734_);
lean_dec_ref(v_x_1608_);
v_x_1608_ = v_a_1734_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1736_, lean_object* v_x_1737_, size_t v_sz_1738_, size_t v_i_1739_, lean_object* v_bs_1740_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
if (v___x_1742_ == 0)
{
lean_dec(v_x_1737_);
lean_dec_ref(v_x_1736_);
return v_bs_1740_;
}
else
{
lean_object* v_v_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_bs_x27_1746_; size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v_v_1743_ = lean_array_uget_borrowed(v_bs_1740_, v_i_1739_);
lean_inc(v_v_1743_);
lean_inc(v_x_1737_);
lean_inc_ref(v_x_1736_);
v___x_1744_ = l_Lean_MessageData_formatAux(v_x_1736_, v_x_1737_, v_v_1743_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v_bs_x27_1746_ = lean_array_uset(v_bs_1740_, v_i_1739_, v___x_1745_);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1739_, v___x_1747_);
v___x_1749_ = lean_array_uset(v_bs_x27_1746_, v_i_1739_, v___x_1744_);
v_i_1739_ = v___x_1748_;
v_bs_1740_ = v___x_1749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_, lean_object* v___y_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1751_, v_x_1752_, v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1755_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_MessageData_formatAux(v_x_1760_, v_x_1761_, v_x_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1768_, lean_object* v_ctx_x3f_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1772_ = l_Lean_MessageData_formatAux(v___x_1771_, v_ctx_x3f_1769_, v_msgData_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1773_, lean_object* v_ctx_x3f_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_MessageData_format(v_msgData_1773_, v_ctx_x3f_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1779_ = lean_box(0);
v___x_1780_ = l_Lean_MessageData_format(v_msgData_1777_, v___x_1779_);
v___x_1781_ = l_Std_Format_defWidth;
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = l_Std_Format_pretty(v___x_1780_, v___x_1781_, v___x_1782_, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_MessageData_toString(v_msgData_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1787_);
lean_ctor_set(v___x_1789_, 1, v_a_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_s_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1817_ = l_Lean_MessageData_ofFormat(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1818_){
_start:
{
if (lean_obj_tag(v_o_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1821_; 
v_val_1820_ = lean_ctor_get(v_o_1818_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_o_1818_, 1);
v___x_1821_ = l_Lean_MessageData_ofExpr(v_val_1820_);
return v___x_1821_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1825_ = l_Lean_MessageData_ofFormat(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1831_, lean_object* v_i_1832_, lean_object* v_acc_1833_){
_start:
{
lean_object* v___y_1835_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_array_get_size(v_es_1831_);
v___x_1840_ = lean_nat_dec_lt(v_i_1832_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v_i_1832_);
v___x_1841_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_acc_1833_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
return v___x_1842_;
}
else
{
lean_object* v_e_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_e_1843_ = lean_array_fget_borrowed(v_es_1831_, v_i_1832_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_nat_dec_eq(v_i_1832_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_acc_1833_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_inc(v_e_1843_);
v___x_1848_ = l_Lean_MessageData_ofExpr(v_e_1843_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___y_1835_ = v___x_1849_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_inc(v_e_1843_);
v___x_1850_ = l_Lean_MessageData_ofExpr(v_e_1843_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_acc_1833_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___y_1835_ = v___x_1851_;
goto v___jp_1834_;
}
}
v___jp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_nat_add(v_i_1832_, v___x_1836_);
lean_dec(v_i_1832_);
v_i_1832_ = v___x_1837_;
v_acc_1833_ = v___y_1835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1852_, lean_object* v_i_1853_, lean_object* v_acc_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1852_, v_i_1853_, v_acc_1854_);
lean_dec_ref(v_es_1852_);
return v_res_1855_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1861_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1864_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1861_, v___x_1862_, v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1865_);
lean_dec_ref(v_es_1865_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1869_, lean_object* v_f_1870_, lean_object* v_r_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1872_ = lean_string_length(v_l_1869_);
v___x_1873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_l_1869_);
v___x_1874_ = l_Lean_MessageData_ofFormat(v___x_1873_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_f_1870_);
v___x_1876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_r_1871_);
v___x_1877_ = l_Lean_MessageData_ofFormat(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1875_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1872_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1883_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1884_ = l_Lean_MessageData_bracket(v___x_1882_, v_f_1881_, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1885_){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1887_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1888_ = l_Lean_MessageData_bracket(v___x_1886_, v_f_1885_, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
if (lean_obj_tag(v_x_1889_) == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_x_1890_);
v___x_1891_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1891_;
}
else
{
lean_object* v_tail_1892_; 
v_tail_1892_ = lean_ctor_get(v_x_1889_, 1);
if (lean_obj_tag(v_tail_1892_) == 0)
{
lean_object* v_head_1893_; 
lean_dec_ref(v_x_1890_);
v_head_1893_ = lean_ctor_get(v_x_1889_, 0);
lean_inc(v_head_1893_);
lean_dec_ref_known(v_x_1889_, 2);
return v_head_1893_;
}
else
{
lean_object* v_head_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1903_; 
lean_inc(v_tail_1892_);
v_head_1894_ = lean_ctor_get(v_x_1889_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_x_1889_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v_x_1889_, 1);
lean_dec(v_unused_1904_);
v___x_1896_ = v_x_1889_;
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_head_1894_);
lean_dec(v_x_1889_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
lean_inc_ref(v_x_1890_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 7);
lean_ctor_set(v___x_1896_, 1, v_x_1890_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_head_1894_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_x_1890_);
v___x_1899_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = l_Lean_MessageData_joinSep(v_tail_1892_, v_x_1890_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
return v___x_1901_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1909_ = l_Lean_MessageData_ofFormat(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1914_ = l_Lean_MessageData_ofFormat(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_box(1);
v___x_1916_ = l_Lean_MessageData_ofFormat(v___x_1915_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1918_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1923_ = l_Lean_MessageData_joinSep(v_x_1920_, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_sbracket(v___x_1923_);
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_array_to_list(v_msgs_1925_);
v___x_1927_ = l_Lean_MessageData_ofList(v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1932_ = l_Lean_MessageData_ofFormat(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1937_ = l_Lean_MessageData_ofFormat(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1942_ = l_Lean_MessageData_ofFormat(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1943_){
_start:
{
if (lean_obj_tag(v_xs_1943_) == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1944_;
}
else
{
lean_object* v_tail_1945_; 
v_tail_1945_ = lean_ctor_get(v_xs_1943_, 1);
lean_inc(v_tail_1945_);
if (lean_obj_tag(v_tail_1945_) == 0)
{
lean_object* v_head_1946_; 
v_head_1946_ = lean_ctor_get(v_xs_1943_, 0);
lean_inc(v_head_1946_);
lean_dec_ref_known(v_xs_1943_, 2);
return v_head_1946_;
}
else
{
lean_object* v_tail_1947_; 
v_tail_1947_ = lean_ctor_get(v_tail_1945_, 1);
if (lean_obj_tag(v_tail_1947_) == 0)
{
lean_object* v_head_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1965_; 
v_head_1948_ = lean_ctor_get(v_xs_1943_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_xs_1943_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_xs_1943_, 1);
lean_dec(v_unused_1966_);
v___x_1950_ = v_xs_1943_;
v_isShared_1951_ = v_isSharedCheck_1965_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_head_1948_);
lean_dec(v_xs_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1965_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_head_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1963_; 
v_head_1952_ = lean_ctor_get(v_tail_1945_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_tail_1945_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_tail_1945_, 1);
lean_dec(v_unused_1964_);
v___x_1954_ = v_tail_1945_;
v_isShared_1955_ = v_isSharedCheck_1963_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_head_1952_);
lean_dec(v_tail_1945_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1963_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 7);
lean_ctor_set(v___x_1954_, 1, v___x_1956_);
lean_ctor_set(v___x_1954_, 0, v_head_1948_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_head_1948_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set_tag(v___x_1950_, 7);
lean_ctor_set(v___x_1950_, 1, v_head_1952_);
lean_ctor_set(v___x_1950_, 0, v___x_1958_);
v___x_1960_ = v___x_1950_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_head_1952_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
else
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1990_; 
v_isSharedCheck_1990_ = !lean_is_exclusive(v_tail_1945_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1991_ = lean_ctor_get(v_tail_1945_, 1);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_tail_1945_, 0);
lean_dec(v_unused_1992_);
v___x_1968_ = v_tail_1945_;
v_isShared_1969_ = v_isSharedCheck_1990_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_tail_1945_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1990_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1970_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1943_);
v___x_1971_ = lean_array_mk(v_xs_1943_);
v___x_1972_ = lean_array_pop(v___x_1971_);
v___x_1973_ = lean_array_to_list(v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1975_ = l_Lean_MessageData_joinSep(v___x_1973_, v___x_1974_);
v___x_1976_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 7);
lean_ctor_set(v___x_1968_, 1, v___x_1976_);
lean_ctor_set(v___x_1968_, 0, v___x_1975_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v___x_1979_ = l_List_getLast_x21___redArg(v___x_1970_, v_xs_1943_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_xs_1943_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_xs_1943_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_xs_1943_, 0);
lean_dec(v_unused_1988_);
v___x_1981_ = v_xs_1943_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_dec(v_xs_1943_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 7);
lean_ctor_set(v___x_1981_, 1, v___x_1979_);
lean_ctor_set(v___x_1981_, 0, v___x_1978_);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
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
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1997_ = l_Lean_MessageData_ofFormat(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_2002_ = l_Lean_MessageData_ofFormat(v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_2003_){
_start:
{
if (lean_obj_tag(v_xs_2003_) == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_2004_;
}
else
{
lean_object* v_tail_2005_; 
v_tail_2005_ = lean_ctor_get(v_xs_2003_, 1);
lean_inc(v_tail_2005_);
if (lean_obj_tag(v_tail_2005_) == 0)
{
lean_object* v_head_2006_; 
v_head_2006_ = lean_ctor_get(v_xs_2003_, 0);
lean_inc(v_head_2006_);
lean_dec_ref_known(v_xs_2003_, 2);
return v_head_2006_;
}
else
{
lean_object* v_tail_2007_; 
v_tail_2007_ = lean_ctor_get(v_tail_2005_, 1);
if (lean_obj_tag(v_tail_2007_) == 0)
{
lean_object* v_head_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2025_; 
v_head_2008_ = lean_ctor_get(v_xs_2003_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_xs_2003_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_xs_2003_, 1);
lean_dec(v_unused_2026_);
v___x_2010_ = v_xs_2003_;
v_isShared_2011_ = v_isSharedCheck_2025_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_head_2008_);
lean_dec(v_xs_2003_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2025_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_head_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2023_; 
v_head_2012_ = lean_ctor_get(v_tail_2005_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_tail_2005_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_tail_2005_, 1);
lean_dec(v_unused_2024_);
v___x_2014_ = v_tail_2005_;
v_isShared_2015_ = v_isSharedCheck_2023_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_head_2012_);
lean_dec(v_tail_2005_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2023_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 7);
lean_ctor_set(v___x_2014_, 1, v___x_2016_);
lean_ctor_set(v___x_2014_, 0, v_head_2008_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_head_2008_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 7);
lean_ctor_set(v___x_2010_, 1, v_head_2012_);
lean_ctor_set(v___x_2010_, 0, v___x_2018_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_head_2012_);
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
else
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v_tail_2005_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_tail_2005_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_tail_2005_, 0);
lean_dec(v_unused_2052_);
v___x_2028_ = v_tail_2005_;
v_isShared_2029_ = v_isSharedCheck_2050_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v_tail_2005_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2050_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2030_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_2003_);
v___x_2031_ = lean_array_mk(v_xs_2003_);
v___x_2032_ = lean_array_pop(v___x_2031_);
v___x_2033_ = lean_array_to_list(v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_2035_ = l_Lean_MessageData_joinSep(v___x_2033_, v___x_2034_);
v___x_2036_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 7);
lean_ctor_set(v___x_2028_, 1, v___x_2036_);
lean_ctor_set(v___x_2028_, 0, v___x_2035_);
v___x_2038_ = v___x_2028_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v___x_2039_ = l_List_getLast_x21___redArg(v___x_2030_, v_xs_2003_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_xs_2003_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2047_ = lean_ctor_get(v_xs_2003_, 1);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_xs_2003_, 0);
lean_dec(v_unused_2048_);
v___x_2041_ = v_xs_2003_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v_xs_2003_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 7);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
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
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2059_ = l_Lean_MessageData_ofFormat(v___x_2058_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2061_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v_note_2063_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2070_ = l_Lean_MessageData_ofFormat(v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2072_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_hint_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2081_ = lean_box(0);
v___x_2082_ = l_List_mapTR_loop___redArg(v___x_2080_, v_es_2079_, v___x_2081_);
v___x_2083_ = l_Lean_MessageData_ofList(v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; 
v___x_2087_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2088_ = l_Lean_instInhabitedPosition_default;
v___x_2089_ = lean_box(0);
v___x_2090_ = 0;
v___x_2091_ = 2;
v___x_2092_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2092_, 0, v___x_2087_);
lean_ctor_set(v___x_2092_, 1, v___x_2088_);
lean_ctor_set(v___x_2092_, 2, v___x_2089_);
lean_ctor_set(v___x_2092_, 3, v___x_2087_);
lean_ctor_set(v___x_2092_, 4, v_inst_2086_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*5, v___x_2090_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*5 + 1, v___x_2091_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*5 + 2, v___x_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2093_, lean_object* v_inst_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2098_, lean_object* v_inst_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2113_, lean_object* v_x_2114_){
_start:
{
lean_object* v_fileName_2115_; lean_object* v_pos_2116_; lean_object* v_endPos_2117_; uint8_t v_keepFullRange_2118_; uint8_t v_severity_2119_; uint8_t v_isSilent_2120_; lean_object* v_caption_2121_; lean_object* v_data_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_fileName_2115_ = lean_ctor_get(v_x_2114_, 0);
lean_inc_ref(v_fileName_2115_);
v_pos_2116_ = lean_ctor_get(v_x_2114_, 1);
lean_inc_ref(v_pos_2116_);
v_endPos_2117_ = lean_ctor_get(v_x_2114_, 2);
lean_inc(v_endPos_2117_);
v_keepFullRange_2118_ = lean_ctor_get_uint8(v_x_2114_, sizeof(void*)*5);
v_severity_2119_ = lean_ctor_get_uint8(v_x_2114_, sizeof(void*)*5 + 1);
v_isSilent_2120_ = lean_ctor_get_uint8(v_x_2114_, sizeof(void*)*5 + 2);
v_caption_2121_ = lean_ctor_get(v_x_2114_, 3);
lean_inc_ref(v_caption_2121_);
v_data_2122_ = lean_ctor_get(v_x_2114_, 4);
lean_inc(v_data_2122_);
lean_dec_ref(v_x_2114_);
v___x_2123_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2124_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_fileName_2115_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2130_ = l_Lean_instToJsonPosition_toJson(v_pos_2116_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2127_);
v___x_2133_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2134_ = l_Lean_Option_toJson___redArg(v___x_2123_, v_endPos_2117_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2127_);
v___x_2137_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2138_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2138_, 0, v_keepFullRange_2118_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2127_);
v___x_2141_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2142_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2119_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v___x_2127_);
v___x_2145_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2146_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2146_, 0, v_isSilent_2120_);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v___x_2127_);
v___x_2149_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_caption_2121_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2127_);
v___x_2153_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2154_ = lean_apply_1(v_inst_2113_, v_data_2122_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v___x_2127_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_2127_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2152_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2148_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2144_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2140_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2136_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2132_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2128_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2166_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2167_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2165_, v___x_2164_, v___x_2166_);
v___x_2168_ = l_Lean_Json_mkObj(v___x_2167_);
lean_dec(v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2169_, lean_object* v_inst_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2170_, v_x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2174_, 0, lean_box(0));
lean_closure_set(v___x_2174_, 1, v_inst_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2175_, lean_object* v_inst_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2177_, 0, lean_box(0));
lean_closure_set(v___x_2177_, 1, v_inst_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = 1;
v___x_2184_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2188_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2189_ = lean_string_append(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = 1;
v___x_2193_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2194_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2196_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2197_ = lean_string_append(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2200_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2201_ = lean_string_append(v___x_2200_, v___x_2199_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = 1;
v___x_2208_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2209_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2211_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2212_ = lean_string_append(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2214_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2215_ = lean_string_append(v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = 1;
v___x_2219_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2222_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2223_ = lean_string_append(v___x_2222_, v___x_2221_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2225_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2226_ = lean_string_append(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = 1;
v___x_2231_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2234_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2235_ = lean_string_append(v___x_2234_, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2237_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2238_ = lean_string_append(v___x_2237_, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = 1;
v___x_2242_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2242_, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2245_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2246_ = lean_string_append(v___x_2245_, v___x_2244_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2248_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2249_ = lean_string_append(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = 1;
v___x_2253_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2254_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2253_, v___x_2252_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2256_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2257_ = lean_string_append(v___x_2256_, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2259_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2260_ = lean_string_append(v___x_2259_, v___x_2258_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = 1;
v___x_2264_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2265_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2264_, v___x_2263_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2267_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2268_ = lean_string_append(v___x_2267_, v___x_2266_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2270_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2271_ = lean_string_append(v___x_2270_, v___x_2269_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = 1;
v___x_2275_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2278_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2279_ = lean_string_append(v___x_2278_, v___x_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2281_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2282_ = lean_string_append(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2283_, lean_object* v_json_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2286_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2284_);
v___x_2287_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2285_, v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2292_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2293_ = lean_string_append(v___x_2292_, v_a_2288_);
lean_dec(v_a_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2293_);
v___x_2295_ = v___x_2290_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2298_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2287_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2287_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2306_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2307_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2308_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2309_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2284_);
v___x_2310_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2307_, v___x_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
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
v___x_2315_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
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
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
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
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2329_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2330_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2284_);
v___x_2331_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2308_, v___x_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
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
v___x_2336_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
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
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2342_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2331_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2331_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 0);
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2351_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2352_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2284_);
v___x_2353_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2351_, v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
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
v___x_2358_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
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
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
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
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_a_2372_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2373_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2374_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2284_);
v___x_2375_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2373_, v___x_2374_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2385_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2385_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2381_ = lean_string_append(v___x_2380_, v_a_2376_);
lean_dec(v_a_2376_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2381_);
v___x_2383_ = v___x_2378_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
else
{
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2386_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2375_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2375_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 0);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2394_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2395_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2284_);
v___x_2396_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2351_, v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2402_ = lean_string_append(v___x_2401_, v_a_2397_);
lean_dec(v_a_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2407_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2396_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2396_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 0);
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_a_2415_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2416_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2284_);
v___x_2417_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v___x_2285_, v___x_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_a_2415_);
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2427_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2427_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2422_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2423_ = lean_string_append(v___x_2422_, v_a_2418_);
lean_dec(v_a_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2423_);
v___x_2425_ = v___x_2420_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_a_2415_);
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
lean_dec(v_json_2284_);
lean_dec_ref(v_inst_2283_);
v_a_2428_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2417_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2417_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 0);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2436_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2437_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2438_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2284_, v_inst_2283_, v___x_2437_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_a_2436_);
lean_dec(v_a_2415_);
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2448_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2448_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2443_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2444_ = lean_string_append(v___x_2443_, v_a_2439_);
lean_dec(v_a_2439_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2444_);
v___x_2446_ = v___x_2441_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
else
{
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2436_);
lean_dec(v_a_2415_);
lean_dec(v_a_2394_);
lean_dec(v_a_2372_);
lean_dec(v_a_2350_);
lean_dec(v_a_2329_);
lean_dec(v_a_2306_);
v_a_2449_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2438_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2438_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 0);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2468_; 
v_a_2457_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2459_ = v___x_2438_;
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2438_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; uint8_t v___x_2463_; uint8_t v___x_2464_; lean_object* v___x_2466_; 
v___x_2461_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2461_, 0, v_a_2306_);
lean_ctor_set(v___x_2461_, 1, v_a_2329_);
lean_ctor_set(v___x_2461_, 2, v_a_2350_);
lean_ctor_set(v___x_2461_, 3, v_a_2436_);
lean_ctor_set(v___x_2461_, 4, v_a_2457_);
v___x_2462_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*5, v___x_2462_);
v___x_2463_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*5 + 1, v___x_2463_);
v___x_2464_ = lean_unbox(v_a_2415_);
lean_dec(v_a_2415_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*5 + 2, v___x_2464_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2466_ = v___x_2459_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2469_, lean_object* v_inst_2470_, lean_object* v_json_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2470_, v_json_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2474_, 0, lean_box(0));
lean_closure_set(v___x_2474_, 1, v_inst_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2475_, lean_object* v_inst_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2477_, 0, lean_box(0));
lean_closure_set(v___x_2477_, 1, v_inst_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2478_){
_start:
{
if (lean_obj_tag(v_x_2478_) == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_box(0);
return v___x_2479_;
}
else
{
lean_object* v_val_2480_; lean_object* v___x_2481_; 
v_val_2480_ = lean_ctor_get(v_x_2478_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v_x_2478_, 1);
v___x_2481_ = l_Lean_instToJsonPosition_toJson(v_val_2480_);
return v___x_2481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
if (lean_obj_tag(v_a_2482_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_array_to_list(v_a_2483_);
return v___x_2484_;
}
else
{
lean_object* v_head_2485_; lean_object* v_tail_2486_; lean_object* v___x_2487_; 
v_head_2485_ = lean_ctor_get(v_a_2482_, 0);
lean_inc(v_head_2485_);
v_tail_2486_ = lean_ctor_get(v_a_2482_, 1);
lean_inc(v_tail_2486_);
lean_dec_ref_known(v_a_2482_, 2);
v___x_2487_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2483_, v_head_2485_);
v_a_2482_ = v_tail_2486_;
v_a_2483_ = v___x_2487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2490_){
_start:
{
lean_object* v_toBaseMessage_2491_; lean_object* v_kind_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2557_; 
v_toBaseMessage_2491_ = lean_ctor_get(v_x_2490_, 0);
v_kind_2492_ = lean_ctor_get(v_x_2490_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_x_2490_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2494_ = v_x_2490_;
v_isShared_2495_ = v_isSharedCheck_2557_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_kind_2492_);
lean_inc(v_toBaseMessage_2491_);
lean_dec(v_x_2490_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2557_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_fileName_2496_; lean_object* v_pos_2497_; lean_object* v_endPos_2498_; uint8_t v_keepFullRange_2499_; uint8_t v_severity_2500_; uint8_t v_isSilent_2501_; lean_object* v_caption_2502_; lean_object* v_data_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; 
v_fileName_2496_ = lean_ctor_get(v_toBaseMessage_2491_, 0);
lean_inc_ref(v_fileName_2496_);
v_pos_2497_ = lean_ctor_get(v_toBaseMessage_2491_, 1);
lean_inc_ref(v_pos_2497_);
v_endPos_2498_ = lean_ctor_get(v_toBaseMessage_2491_, 2);
lean_inc(v_endPos_2498_);
v_keepFullRange_2499_ = lean_ctor_get_uint8(v_toBaseMessage_2491_, sizeof(void*)*5);
v_severity_2500_ = lean_ctor_get_uint8(v_toBaseMessage_2491_, sizeof(void*)*5 + 1);
v_isSilent_2501_ = lean_ctor_get_uint8(v_toBaseMessage_2491_, sizeof(void*)*5 + 2);
v_caption_2502_ = lean_ctor_get(v_toBaseMessage_2491_, 3);
lean_inc_ref(v_caption_2502_);
v_data_2503_ = lean_ctor_get(v_toBaseMessage_2491_, 4);
lean_inc(v_data_2503_);
lean_dec_ref(v_toBaseMessage_2491_);
v___x_2504_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_fileName_2496_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 1, v___x_2505_);
lean_ctor_set(v___x_2494_, 0, v___x_2504_);
v___x_2507_ = v___x_2494_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2511_ = l_Lean_instToJsonPosition_toJson(v_pos_2497_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2508_);
v___x_2514_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2515_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2498_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v___x_2508_);
v___x_2518_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2519_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2519_, 0, v_keepFullRange_2499_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2508_);
v___x_2522_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2523_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2500_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v___x_2508_);
v___x_2526_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2527_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2527_, 0, v_isSilent_2501_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___x_2508_);
v___x_2530_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_caption_2502_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2508_);
v___x_2534_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_data_2503_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2508_);
v___x_2538_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2539_ = 1;
v___x_2540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2492_, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2538_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2508_);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2508_);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2537_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2533_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2529_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2525_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2521_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2517_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2513_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2509_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2554_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2552_, v___x_2553_);
v___x_2555_ = l_Lean_Json_mkObj(v___x_2554_);
lean_dec(v___x_2554_);
return v___x_2555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2560_, lean_object* v_k_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = l_Lean_Json_getObjValD(v_j_2560_, v_k_2561_);
v___x_2563_ = l_Lean_Json_getStr_x3f(v___x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2564_, lean_object* v_k_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2564_, v_k_2565_);
lean_dec_ref(v_k_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2567_, lean_object* v_k_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = l_Lean_Json_getObjValD(v_j_2567_, v_k_2568_);
v___x_2570_ = l_Lean_instFromJsonPosition_fromJson(v___x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2571_, lean_object* v_k_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2571_, v_k_2572_);
lean_dec_ref(v_k_2572_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2574_, lean_object* v_k_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = l_Lean_Json_getObjValD(v_j_2574_, v_k_2575_);
v___x_2577_ = l_Lean_Json_getBool_x3f(v___x_2576_);
lean_dec(v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2578_, lean_object* v_k_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2578_, v_k_2579_);
lean_dec_ref(v_k_2579_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2581_, lean_object* v_k_2582_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = l_Lean_Json_getObjValD(v_j_2581_, v_k_2582_);
v___x_2584_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2585_, lean_object* v_k_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2585_, v_k_2586_);
lean_dec_ref(v_k_2586_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2588_, lean_object* v_k_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = l_Lean_Json_getObjValD(v_j_2588_, v_k_2589_);
v___x_2591_ = l_Lean_Name_fromJson_x3f(v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2592_, lean_object* v_k_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2592_, v_k_2593_);
lean_dec_ref(v_k_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2597_){
_start:
{
if (lean_obj_tag(v_x_2597_) == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_instFromJsonPosition_fromJson(v_x_2597_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2616_; 
v_a_2608_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2610_ = v___x_2599_;
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2599_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_a_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2617_, lean_object* v_k_2618_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = l_Lean_Json_getObjValD(v_j_2617_, v_k_2618_);
v___x_2620_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2621_, lean_object* v_k_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2621_, v_k_2622_);
lean_dec_ref(v_k_2622_);
return v_res_2623_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = 1;
v___x_2629_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2630_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2629_, v___x_2628_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2632_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2633_ = lean_string_append(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2635_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2636_ = lean_string_append(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2639_ = lean_string_append(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2641_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2642_ = lean_string_append(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2644_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2645_ = lean_string_append(v___x_2644_, v___x_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2647_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2648_ = lean_string_append(v___x_2647_, v___x_2646_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2650_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2651_ = lean_string_append(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2653_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2654_ = lean_string_append(v___x_2653_, v___x_2652_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2656_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2657_ = lean_string_append(v___x_2656_, v___x_2655_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2659_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2660_ = lean_string_append(v___x_2659_, v___x_2658_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2662_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2663_ = lean_string_append(v___x_2662_, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2665_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2666_ = lean_string_append(v___x_2665_, v___x_2664_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2668_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2669_ = lean_string_append(v___x_2668_, v___x_2667_);
return v___x_2669_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2671_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2672_ = lean_string_append(v___x_2671_, v___x_2670_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2674_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2675_ = lean_string_append(v___x_2674_, v___x_2673_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2677_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2678_ = lean_string_append(v___x_2677_, v___x_2676_);
return v___x_2678_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2680_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2681_ = lean_string_append(v___x_2680_, v___x_2679_);
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = 1;
v___x_2685_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2685_, v___x_2684_);
return v___x_2686_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2688_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2689_ = lean_string_append(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2691_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2692_ = lean_string_append(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2693_){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2693_);
v___x_2695_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2693_, v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_json_2693_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2705_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2705_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2700_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2701_ = lean_string_append(v___x_2700_, v_a_2696_);
lean_dec(v_a_2696_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2701_);
v___x_2703_ = v___x_2698_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
else
{
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_json_2693_);
v_a_2706_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2695_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2695_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 0);
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_a_2714_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2715_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2693_);
v___x_2716_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2693_, v___x_2715_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2726_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2726_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2722_ = lean_string_append(v___x_2721_, v_a_2717_);
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2722_);
v___x_2724_ = v___x_2719_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2727_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2716_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2716_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 0);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2736_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2693_);
v___x_2737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2693_, v___x_2736_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2742_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2743_ = lean_string_append(v___x_2742_, v_a_2738_);
lean_dec(v_a_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2748_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2737_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2737_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 0);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2756_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2757_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2693_);
v___x_2758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2693_, v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2768_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2768_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2763_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2764_ = lean_string_append(v___x_2763_, v_a_2759_);
lean_dec(v_a_2759_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2764_);
v___x_2766_ = v___x_2761_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2769_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2758_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2758_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set_tag(v___x_2771_, 0);
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_a_2777_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2778_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2693_);
v___x_2779_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2693_, v___x_2778_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2784_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2785_ = lean_string_append(v___x_2784_, v_a_2780_);
lean_dec(v_a_2780_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2785_);
v___x_2787_ = v___x_2782_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2790_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2779_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2779_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 0);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2799_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2693_);
v___x_2800_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2693_, v___x_2799_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2810_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2810_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2805_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2806_ = lean_string_append(v___x_2805_, v_a_2801_);
lean_dec(v_a_2801_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2806_);
v___x_2808_ = v___x_2803_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2811_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2800_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2800_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 0);
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_a_2819_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2820_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2693_);
v___x_2821_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2693_, v___x_2820_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2826_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2827_ = lean_string_append(v___x_2826_, v_a_2822_);
lean_dec(v_a_2822_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2827_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
else
{
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2832_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2821_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2821_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 0);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2841_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2693_);
v___x_2842_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2693_, v___x_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_a_2840_);
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2852_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2852_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2847_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2848_ = lean_string_append(v___x_2847_, v_a_2843_);
lean_dec(v_a_2843_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2848_);
v___x_2850_ = v___x_2845_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_a_2840_);
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
lean_dec(v_json_2693_);
v_a_2853_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2842_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2842_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 0);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2862_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2863_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2693_, v___x_2862_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2840_);
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2868_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2869_ = lean_string_append(v___x_2868_, v_a_2864_);
lean_dec(v_a_2864_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2869_);
v___x_2871_ = v___x_2866_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2840_);
lean_dec(v_a_2819_);
lean_dec(v_a_2798_);
lean_dec(v_a_2777_);
lean_dec(v_a_2756_);
lean_dec(v_a_2735_);
lean_dec(v_a_2714_);
v_a_2874_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2863_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2863_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set_tag(v___x_2876_, 0);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2894_; 
v_a_2882_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2884_ = v___x_2863_;
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2863_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; uint8_t v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2886_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2886_, 0, v_a_2714_);
lean_ctor_set(v___x_2886_, 1, v_a_2735_);
lean_ctor_set(v___x_2886_, 2, v_a_2756_);
lean_ctor_set(v___x_2886_, 3, v_a_2840_);
lean_ctor_set(v___x_2886_, 4, v_a_2861_);
v___x_2887_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*5, v___x_2887_);
v___x_2888_ = lean_unbox(v_a_2798_);
lean_dec(v_a_2798_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*5 + 1, v___x_2888_);
v___x_2889_ = lean_unbox(v_a_2819_);
lean_dec(v_a_2819_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*5 + 2, v___x_2889_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2886_);
lean_ctor_set(v___x_2890_, 1, v_a_2882_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2890_);
v___x_2892_ = v___x_2884_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2899_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2901_ = l_Lean_Name_str___override(v_errorName_2899_, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2902_, lean_object* v_name_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = l_Lean_kindOfErrorName(v_name_2903_);
v___x_2905_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v_msg_2902_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2907_){
_start:
{
switch(lean_obj_tag(v_a_2907_))
{
case 0:
{
return v_a_2907_;
}
case 1:
{
lean_object* v_pre_2908_; lean_object* v_str_2909_; lean_object* v_p_x27_2910_; uint8_t v___y_2912_; uint8_t v___x_2915_; 
v_pre_2908_ = lean_ctor_get(v_a_2907_, 0);
lean_inc(v_pre_2908_);
v_str_2909_ = lean_ctor_get(v_a_2907_, 1);
lean_inc_ref(v_str_2909_);
lean_dec_ref_known(v_a_2907_, 2);
v_p_x27_2910_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2908_);
v___x_2915_ = l_Lean_Name_isAnonymous(v_p_x27_2910_);
if (v___x_2915_ == 0)
{
v___y_2912_ = v___x_2915_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2917_ = lean_string_dec_eq(v_str_2909_, v___x_2916_);
v___y_2912_ = v___x_2917_;
goto v___jp_2911_;
}
v___jp_2911_:
{
if (v___y_2912_ == 0)
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Name_str___override(v_p_x27_2910_, v_str_2909_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_p_x27_2910_);
lean_dec_ref(v_str_2909_);
v___x_2914_ = lean_box(0);
return v___x_2914_;
}
}
}
default: 
{
lean_object* v_pre_2918_; lean_object* v_i_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_pre_2918_ = lean_ctor_get(v_a_2907_, 0);
lean_inc(v_pre_2918_);
v_i_2919_ = lean_ctor_get(v_a_2907_, 1);
lean_inc(v_i_2919_);
lean_dec_ref_known(v_a_2907_, 2);
v___x_2920_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2918_);
v___x_2921_ = l_Lean_Name_num___override(v___x_2920_, v_i_2919_);
return v___x_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2922_){
_start:
{
switch(lean_obj_tag(v_x_2922_))
{
case 3:
{
lean_object* v_a_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_a_2923_ = lean_ctor_get(v_x_2922_, 0);
v_a_2924_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v_x_2922_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_inc(v_a_2923_);
lean_dec(v_x_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_Lean_MessageData_stripNestedTags(v_a_2924_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2923_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
case 4:
{
lean_object* v_a_2933_; lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2942_; 
v_a_2933_ = lean_ctor_get(v_x_2922_, 0);
v_a_2934_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2936_ = v_x_2922_;
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_inc(v_a_2933_);
lean_dec(v_x_2922_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_MessageData_stripNestedTags(v_a_2934_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2933_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
case 8:
{
lean_object* v_a_2943_; lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
v_a_2943_ = lean_ctor_get(v_x_2922_, 0);
v_a_2944_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2946_ = v_x_2922_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_inc(v_a_2943_);
lean_dec(v_x_2922_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2943_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_a_2944_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
case 11:
{
lean_object* v_a_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
v_a_2953_ = lean_ctor_get(v_x_2922_, 0);
v_a_2954_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2956_ = v_x_2922_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_inc(v_a_2953_);
lean_dec(v_x_2922_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = l_Lean_MessageData_stripNestedTags(v_a_2954_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
case 12:
{
lean_object* v_a_2963_; lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2972_; 
v_a_2963_ = lean_ctor_get(v_x_2922_, 0);
v_a_2964_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2966_ = v_x_2922_;
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_inc(v_a_2963_);
lean_dec(v_x_2922_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = l_Lean_MessageData_stripNestedTags(v_a_2964_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2968_);
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2963_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
default: 
{
return v_x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2973_){
_start:
{
if (lean_obj_tag(v_x_2973_) == 1)
{
lean_object* v_pre_2974_; lean_object* v_str_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_pre_2974_ = lean_ctor_get(v_x_2973_, 0);
v_str_2975_ = lean_ctor_get(v_x_2973_, 1);
v___x_2976_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2977_ = lean_string_dec_eq(v_str_2975_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_box(0);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; 
lean_inc(v_pre_2974_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_pre_2974_);
return v___x_2979_;
}
}
else
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_box(0);
return v___x_2980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_errorNameOfKind_x3f(v_x_2981_);
lean_dec(v_x_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_MessageData_kind(v_msg_2983_);
v___x_2985_ = l_Lean_errorNameOfKind_x3f(v___x_2984_);
lean_dec(v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_MessageData_errorName_x3f(v_msg_2986_);
lean_dec_ref(v_msg_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2988_){
_start:
{
lean_object* v_data_2989_; lean_object* v___x_2990_; 
v_data_2989_ = lean_ctor_get(v_msg_2988_, 4);
v___x_2990_ = l_Lean_MessageData_errorName_x3f(v_data_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Message_errorName_x3f(v_msg_2991_);
lean_dec_ref(v_msg_2991_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2993_){
_start:
{
lean_object* v_toBaseMessage_2994_; lean_object* v_fileName_2995_; lean_object* v_pos_2996_; lean_object* v_endPos_2997_; uint8_t v_keepFullRange_2998_; uint8_t v_severity_2999_; uint8_t v_isSilent_3000_; lean_object* v_caption_3001_; lean_object* v_data_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3011_; 
v_toBaseMessage_2994_ = lean_ctor_get(v_msg_2993_, 0);
lean_inc_ref(v_toBaseMessage_2994_);
lean_dec_ref(v_msg_2993_);
v_fileName_2995_ = lean_ctor_get(v_toBaseMessage_2994_, 0);
v_pos_2996_ = lean_ctor_get(v_toBaseMessage_2994_, 1);
v_endPos_2997_ = lean_ctor_get(v_toBaseMessage_2994_, 2);
v_keepFullRange_2998_ = lean_ctor_get_uint8(v_toBaseMessage_2994_, sizeof(void*)*5);
v_severity_2999_ = lean_ctor_get_uint8(v_toBaseMessage_2994_, sizeof(void*)*5 + 1);
v_isSilent_3000_ = lean_ctor_get_uint8(v_toBaseMessage_2994_, sizeof(void*)*5 + 2);
v_caption_3001_ = lean_ctor_get(v_toBaseMessage_2994_, 3);
v_data_3002_ = lean_ctor_get(v_toBaseMessage_2994_, 4);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_toBaseMessage_2994_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3004_ = v_toBaseMessage_2994_;
v_isShared_3005_ = v_isSharedCheck_3011_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_data_3002_);
lean_inc(v_caption_3001_);
lean_inc(v_endPos_2997_);
lean_inc(v_pos_2996_);
lean_inc(v_fileName_2995_);
lean_dec(v_toBaseMessage_2994_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3011_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_data_3002_);
v___x_3007_ = l_Lean_MessageData_ofFormat(v___x_3006_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 4, v___x_3007_);
v___x_3009_ = v___x_3004_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fileName_2995_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_pos_2996_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v_endPos_2997_);
lean_ctor_set(v_reuseFailAlloc_3010_, 3, v_caption_3001_);
lean_ctor_set(v_reuseFailAlloc_3010_, 4, v___x_3007_);
lean_ctor_set_uint8(v_reuseFailAlloc_3010_, sizeof(void*)*5, v_keepFullRange_2998_);
lean_ctor_set_uint8(v_reuseFailAlloc_3010_, sizeof(void*)*5 + 1, v_severity_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3010_, sizeof(void*)*5 + 2, v_isSilent_3000_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_3017_, uint8_t v_includeEndPos_3018_){
_start:
{
lean_object* v___y_3020_; lean_object* v___y_3024_; uint32_t v___y_3025_; lean_object* v_str_3029_; lean_object* v_toBaseMessage_3041_; lean_object* v_kind_3042_; lean_object* v_fileName_3043_; lean_object* v_pos_3044_; lean_object* v_endPos_3045_; uint8_t v_severity_3046_; lean_object* v_caption_3047_; lean_object* v_data_3048_; lean_object* v___y_3050_; lean_object* v_str_3051_; lean_object* v___y_3059_; 
v_toBaseMessage_3041_ = lean_ctor_get(v_msg_3017_, 0);
lean_inc_ref(v_toBaseMessage_3041_);
v_kind_3042_ = lean_ctor_get(v_msg_3017_, 1);
lean_inc(v_kind_3042_);
lean_dec_ref(v_msg_3017_);
v_fileName_3043_ = lean_ctor_get(v_toBaseMessage_3041_, 0);
lean_inc_ref(v_fileName_3043_);
v_pos_3044_ = lean_ctor_get(v_toBaseMessage_3041_, 1);
lean_inc_ref(v_pos_3044_);
v_endPos_3045_ = lean_ctor_get(v_toBaseMessage_3041_, 2);
lean_inc(v_endPos_3045_);
v_severity_3046_ = lean_ctor_get_uint8(v_toBaseMessage_3041_, sizeof(void*)*5 + 1);
v_caption_3047_ = lean_ctor_get(v_toBaseMessage_3041_, 3);
lean_inc_ref(v_caption_3047_);
v_data_3048_ = lean_ctor_get(v_toBaseMessage_3041_, 4);
lean_inc(v_data_3048_);
lean_dec_ref(v_toBaseMessage_3041_);
if (v_includeEndPos_3018_ == 0)
{
lean_object* v___x_3065_; 
lean_dec(v_endPos_3045_);
v___x_3065_ = lean_box(0);
v___y_3059_ = v___x_3065_;
goto v___jp_3058_;
}
else
{
v___y_3059_ = v_endPos_3045_;
goto v___jp_3058_;
}
v___jp_3019_:
{
lean_object* v___x_3021_; lean_object* v_str_3022_; 
v___x_3021_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3022_ = lean_string_append(v___y_3020_, v___x_3021_);
return v_str_3022_;
}
v___jp_3023_:
{
uint32_t v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = 10;
v___x_3027_ = lean_uint32_dec_eq(v___y_3025_, v___x_3026_);
if (v___x_3027_ == 0)
{
v___y_3020_ = v___y_3024_;
goto v___jp_3019_;
}
else
{
return v___y_3024_;
}
}
v___jp_3028_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3030_ = lean_string_utf8_byte_size(v_str_3029_);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_nat_dec_eq(v___x_3030_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_inc_ref(v_str_3029_);
v___x_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3033_, 0, v_str_3029_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
lean_ctor_set(v___x_3033_, 2, v___x_3030_);
v___x_3034_ = l_String_Slice_Pos_prev_x3f(v___x_3033_, v___x_3030_);
if (lean_obj_tag(v___x_3034_) == 0)
{
uint32_t v___x_3035_; 
lean_dec_ref_known(v___x_3033_, 3);
v___x_3035_ = 65;
v___y_3024_ = v_str_3029_;
v___y_3025_ = v___x_3035_;
goto v___jp_3023_;
}
else
{
lean_object* v_val_3036_; lean_object* v___x_3037_; 
v_val_3036_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_val_3036_);
lean_dec_ref_known(v___x_3034_, 1);
v___x_3037_ = l_String_Slice_Pos_get_x3f(v___x_3033_, v_val_3036_);
lean_dec(v_val_3036_);
lean_dec_ref_known(v___x_3033_, 3);
if (lean_obj_tag(v___x_3037_) == 0)
{
uint32_t v___x_3038_; 
v___x_3038_ = 65;
v___y_3024_ = v_str_3029_;
v___y_3025_ = v___x_3038_;
goto v___jp_3023_;
}
else
{
lean_object* v_val_3039_; uint32_t v___x_3040_; 
v_val_3039_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_val_3039_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3040_ = lean_unbox_uint32(v_val_3039_);
lean_dec(v_val_3039_);
v___y_3024_ = v_str_3029_;
v___y_3025_ = v___x_3040_;
goto v___jp_3023_;
}
}
}
else
{
v___y_3020_ = v_str_3029_;
goto v___jp_3019_;
}
}
v___jp_3049_:
{
switch(v_severity_3046_)
{
case 0:
{
lean_dec(v___y_3050_);
lean_dec_ref(v_pos_3044_);
lean_dec_ref(v_fileName_3043_);
lean_dec(v_kind_3042_);
v_str_3029_ = v_str_3051_;
goto v___jp_3028_;
}
case 1:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_str_3054_; 
v___x_3052_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3053_ = l_Lean_errorNameOfKind_x3f(v_kind_3042_);
lean_dec(v_kind_3042_);
v_str_3054_ = l_Lean_mkErrorStringWithPos(v_fileName_3043_, v_pos_3044_, v_str_3051_, v___y_3050_, v___x_3052_, v___x_3053_);
lean_dec_ref(v_str_3051_);
v_str_3029_ = v_str_3054_;
goto v___jp_3028_;
}
default: 
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_str_3057_; 
v___x_3055_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3056_ = l_Lean_errorNameOfKind_x3f(v_kind_3042_);
lean_dec(v_kind_3042_);
v_str_3057_ = l_Lean_mkErrorStringWithPos(v_fileName_3043_, v_pos_3044_, v_str_3051_, v___y_3050_, v___x_3055_, v___x_3056_);
lean_dec_ref(v_str_3051_);
v_str_3029_ = v_str_3057_;
goto v___jp_3028_;
}
}
}
v___jp_3058_:
{
lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3061_ = lean_string_dec_eq(v_caption_3047_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_str_3064_; 
v___x_3062_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3063_ = lean_string_append(v_caption_3047_, v___x_3062_);
v_str_3064_ = lean_string_append(v___x_3063_, v_data_3048_);
lean_dec(v_data_3048_);
v___y_3050_ = v___y_3059_;
v_str_3051_ = v_str_3064_;
goto v___jp_3049_;
}
else
{
lean_dec_ref(v_caption_3047_);
v___y_3050_ = v___y_3059_;
v_str_3051_ = v_data_3048_;
goto v___jp_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3066_, lean_object* v_includeEndPos_3067_){
_start:
{
uint8_t v_includeEndPos_boxed_3068_; lean_object* v_res_3069_; 
v_includeEndPos_boxed_3068_ = lean_unbox(v_includeEndPos_3067_);
v_res_3069_ = l_Lean_SerialMessage_toString(v_msg_3066_, v_includeEndPos_boxed_3068_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3070_){
_start:
{
uint8_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = 0;
v___x_3072_ = l_Lean_SerialMessage_toString(v_msg_3070_, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3075_){
_start:
{
lean_object* v_data_3076_; lean_object* v___x_3077_; 
v_data_3076_ = lean_ctor_get(v_msg_3075_, 4);
v___x_3077_ = l_Lean_MessageData_kind(v_data_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Message_kind(v_msg_3078_);
lean_dec_ref(v_msg_3078_);
return v_res_3079_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3080_){
_start:
{
lean_object* v_data_3081_; uint8_t v___x_3082_; 
v_data_3081_ = lean_ctor_get(v_msg_3080_, 4);
v___x_3082_ = l_Lean_MessageData_isTrace(v_data_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3083_){
_start:
{
uint8_t v_res_3084_; lean_object* v_r_3085_; 
v_res_3084_ = l_Lean_Message_isTrace(v_msg_3083_);
lean_dec_ref(v_msg_3083_);
v_r_3085_ = lean_box(v_res_3084_);
return v_r_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3086_){
_start:
{
lean_object* v_fileName_3088_; lean_object* v_pos_3089_; lean_object* v_endPos_3090_; uint8_t v_keepFullRange_3091_; uint8_t v_severity_3092_; uint8_t v_isSilent_3093_; lean_object* v_caption_3094_; lean_object* v_data_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3105_; 
v_fileName_3088_ = lean_ctor_get(v_msg_3086_, 0);
v_pos_3089_ = lean_ctor_get(v_msg_3086_, 1);
v_endPos_3090_ = lean_ctor_get(v_msg_3086_, 2);
v_keepFullRange_3091_ = lean_ctor_get_uint8(v_msg_3086_, sizeof(void*)*5);
v_severity_3092_ = lean_ctor_get_uint8(v_msg_3086_, sizeof(void*)*5 + 1);
v_isSilent_3093_ = lean_ctor_get_uint8(v_msg_3086_, sizeof(void*)*5 + 2);
v_caption_3094_ = lean_ctor_get(v_msg_3086_, 3);
v_data_3095_ = lean_ctor_get(v_msg_3086_, 4);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_msg_3086_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3097_ = v_msg_3086_;
v_isShared_3098_ = v_isSharedCheck_3105_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_data_3095_);
lean_inc(v_caption_3094_);
lean_inc(v_endPos_3090_);
lean_inc(v_pos_3089_);
lean_inc(v_fileName_3088_);
lean_dec(v_msg_3086_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3105_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_inc(v_data_3095_);
v___x_3099_ = l_Lean_MessageData_toString(v_data_3095_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 4, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_fileName_3088_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_pos_3089_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_endPos_3090_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_caption_3094_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v___x_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*5, v_keepFullRange_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*5 + 1, v_severity_3092_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*5 + 2, v_isSilent_3093_);
v___x_3101_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = l_Lean_MessageData_kind(v_data_3095_);
lean_dec(v_data_3095_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
return v___x_3103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Message_serialize(v_msg_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3109_, uint8_t v_includeEndPos_3110_){
_start:
{
lean_object* v_fileName_3112_; lean_object* v_pos_3113_; lean_object* v_endPos_3114_; uint8_t v_severity_3115_; lean_object* v_caption_3116_; lean_object* v_data_3117_; lean_object* v___x_3118_; lean_object* v___y_3120_; lean_object* v___y_3124_; uint32_t v___y_3125_; lean_object* v_str_3129_; lean_object* v___x_3141_; lean_object* v___y_3143_; lean_object* v_str_3144_; lean_object* v___y_3152_; 
v_fileName_3112_ = lean_ctor_get(v_msg_3109_, 0);
lean_inc_ref(v_fileName_3112_);
v_pos_3113_ = lean_ctor_get(v_msg_3109_, 1);
lean_inc_ref(v_pos_3113_);
v_endPos_3114_ = lean_ctor_get(v_msg_3109_, 2);
lean_inc(v_endPos_3114_);
v_severity_3115_ = lean_ctor_get_uint8(v_msg_3109_, sizeof(void*)*5 + 1);
v_caption_3116_ = lean_ctor_get(v_msg_3109_, 3);
lean_inc_ref(v_caption_3116_);
v_data_3117_ = lean_ctor_get(v_msg_3109_, 4);
lean_inc_n(v_data_3117_, 2);
lean_dec_ref(v_msg_3109_);
v___x_3118_ = l_Lean_MessageData_toString(v_data_3117_);
v___x_3141_ = l_Lean_MessageData_kind(v_data_3117_);
lean_dec(v_data_3117_);
if (v_includeEndPos_3110_ == 0)
{
lean_object* v___x_3158_; 
lean_dec(v_endPos_3114_);
v___x_3158_ = lean_box(0);
v___y_3152_ = v___x_3158_;
goto v___jp_3151_;
}
else
{
v___y_3152_ = v_endPos_3114_;
goto v___jp_3151_;
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v_str_3122_; 
v___x_3121_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3122_ = lean_string_append(v___y_3120_, v___x_3121_);
return v_str_3122_;
}
v___jp_3123_:
{
uint32_t v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = 10;
v___x_3127_ = lean_uint32_dec_eq(v___y_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
v___y_3120_ = v___y_3124_;
goto v___jp_3119_;
}
else
{
return v___y_3124_;
}
}
v___jp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3130_ = lean_string_utf8_byte_size(v_str_3129_);
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_nat_dec_eq(v___x_3130_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_inc_ref(v_str_3129_);
v___x_3133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3133_, 0, v_str_3129_);
lean_ctor_set(v___x_3133_, 1, v___x_3131_);
lean_ctor_set(v___x_3133_, 2, v___x_3130_);
v___x_3134_ = l_String_Slice_Pos_prev_x3f(v___x_3133_, v___x_3130_);
if (lean_obj_tag(v___x_3134_) == 0)
{
uint32_t v___x_3135_; 
lean_dec_ref_known(v___x_3133_, 3);
v___x_3135_ = 65;
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3135_;
goto v___jp_3123_;
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3137_; 
v_val_3136_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_val_3136_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3137_ = l_String_Slice_Pos_get_x3f(v___x_3133_, v_val_3136_);
lean_dec(v_val_3136_);
lean_dec_ref_known(v___x_3133_, 3);
if (lean_obj_tag(v___x_3137_) == 0)
{
uint32_t v___x_3138_; 
v___x_3138_ = 65;
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3138_;
goto v___jp_3123_;
}
else
{
lean_object* v_val_3139_; uint32_t v___x_3140_; 
v_val_3139_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3140_ = lean_unbox_uint32(v_val_3139_);
lean_dec(v_val_3139_);
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3140_;
goto v___jp_3123_;
}
}
}
else
{
v___y_3120_ = v_str_3129_;
goto v___jp_3119_;
}
}
v___jp_3142_:
{
switch(v_severity_3115_)
{
case 0:
{
lean_dec(v___y_3143_);
lean_dec(v___x_3141_);
lean_dec_ref(v_pos_3113_);
lean_dec_ref(v_fileName_3112_);
v_str_3129_ = v_str_3144_;
goto v___jp_3128_;
}
case 1:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_str_3147_; 
v___x_3145_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3146_ = l_Lean_errorNameOfKind_x3f(v___x_3141_);
lean_dec(v___x_3141_);
v_str_3147_ = l_Lean_mkErrorStringWithPos(v_fileName_3112_, v_pos_3113_, v_str_3144_, v___y_3143_, v___x_3145_, v___x_3146_);
lean_dec_ref(v_str_3144_);
v_str_3129_ = v_str_3147_;
goto v___jp_3128_;
}
default: 
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v_str_3150_; 
v___x_3148_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3149_ = l_Lean_errorNameOfKind_x3f(v___x_3141_);
lean_dec(v___x_3141_);
v_str_3150_ = l_Lean_mkErrorStringWithPos(v_fileName_3112_, v_pos_3113_, v_str_3144_, v___y_3143_, v___x_3148_, v___x_3149_);
lean_dec_ref(v_str_3144_);
v_str_3129_ = v_str_3150_;
goto v___jp_3128_;
}
}
}
v___jp_3151_:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3154_ = lean_string_dec_eq(v_caption_3116_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v_str_3157_; 
v___x_3155_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3156_ = lean_string_append(v_caption_3116_, v___x_3155_);
v_str_3157_ = lean_string_append(v___x_3156_, v___x_3118_);
lean_dec_ref(v___x_3118_);
v___y_3143_ = v___y_3152_;
v_str_3144_ = v_str_3157_;
goto v___jp_3142_;
}
else
{
lean_dec_ref(v_caption_3116_);
v___y_3143_ = v___y_3152_;
v_str_3144_ = v___x_3118_;
goto v___jp_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3159_, lean_object* v_includeEndPos_3160_, lean_object* v_a_3161_){
_start:
{
uint8_t v_includeEndPos_boxed_3162_; lean_object* v_res_3163_; 
v_includeEndPos_boxed_3162_ = lean_unbox(v_includeEndPos_3160_);
v_res_3163_ = l_Lean_Message_toString(v_msg_3159_, v_includeEndPos_boxed_3162_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_3164_){
_start:
{
lean_object* v_fileName_3166_; lean_object* v_pos_3167_; lean_object* v_endPos_3168_; uint8_t v_keepFullRange_3169_; uint8_t v_severity_3170_; uint8_t v_isSilent_3171_; lean_object* v_caption_3172_; lean_object* v_data_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_fileName_3166_ = lean_ctor_get(v_msg_3164_, 0);
lean_inc_ref(v_fileName_3166_);
v_pos_3167_ = lean_ctor_get(v_msg_3164_, 1);
lean_inc_ref(v_pos_3167_);
v_endPos_3168_ = lean_ctor_get(v_msg_3164_, 2);
lean_inc(v_endPos_3168_);
v_keepFullRange_3169_ = lean_ctor_get_uint8(v_msg_3164_, sizeof(void*)*5);
v_severity_3170_ = lean_ctor_get_uint8(v_msg_3164_, sizeof(void*)*5 + 1);
v_isSilent_3171_ = lean_ctor_get_uint8(v_msg_3164_, sizeof(void*)*5 + 2);
v_caption_3172_ = lean_ctor_get(v_msg_3164_, 3);
lean_inc_ref(v_caption_3172_);
v_data_3173_ = lean_ctor_get(v_msg_3164_, 4);
lean_inc_n(v_data_3173_, 2);
lean_dec_ref(v_msg_3164_);
v___x_3174_ = l_Lean_MessageData_toString(v_data_3173_);
v___x_3175_ = l_Lean_MessageData_kind(v_data_3173_);
lean_dec(v_data_3173_);
v___x_3176_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_fileName_3166_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3182_ = l_Lean_instToJsonPosition_toJson(v_pos_3167_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3179_);
v___x_3185_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3186_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3168_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v___x_3179_);
v___x_3189_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3190_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3190_, 0, v_keepFullRange_3169_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___x_3179_);
v___x_3193_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3194_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3170_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v___x_3179_);
v___x_3197_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3198_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3198_, 0, v_isSilent_3171_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3179_);
v___x_3201_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_caption_3172_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3201_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3179_);
v___x_3205_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3174_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v___x_3179_);
v___x_3209_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3210_ = 1;
v___x_3211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3175_, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3209_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3179_);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3179_);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3208_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3204_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3200_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3196_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3192_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3188_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3184_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3180_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3225_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3223_, v___x_3224_);
v___x_3226_ = l_Lean_Json_mkObj(v___x_3225_);
lean_dec(v___x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Message_toJson(v_msg_3227_);
return v_res_3229_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_unsigned_to_nat(32u);
v___x_3231_ = lean_mk_empty_array_with_capacity(v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3233_ = ((size_t)5ULL);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = lean_unsigned_to_nat(32u);
v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
v___x_3237_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3238_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v___x_3236_);
lean_ctor_set(v___x_3238_, 2, v___x_3234_);
lean_ctor_set(v___x_3238_, 3, v___x_3234_);
lean_ctor_set_usize(v___x_3238_, 4, v___x_3233_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = l_Lean_NameSet_empty;
v___x_3240_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
lean_ctor_set(v___x_3241_, 2, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = lean_unsigned_to_nat(32u);
v___x_3245_ = lean_mk_empty_array_with_capacity(v___x_3244_);
lean_dec_ref(v___x_3245_);
v___x_3246_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3247_){
_start:
{
lean_object* v_unreported_3248_; 
v_unreported_3248_ = lean_ctor_get(v_self_3247_, 1);
lean_inc_ref(v_unreported_3248_);
return v_unreported_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_MessageLog_msgs(v_self_3249_);
lean_dec_ref(v_self_3249_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3251_){
_start:
{
lean_object* v_reported_3252_; lean_object* v_unreported_3253_; lean_object* v___x_3254_; 
v_reported_3252_ = lean_ctor_get(v_x_3251_, 0);
lean_inc_ref(v_reported_3252_);
v_unreported_3253_ = lean_ctor_get(v_x_3251_, 1);
lean_inc_ref(v_unreported_3253_);
lean_dec_ref(v_x_3251_);
v___x_3254_ = l_Lean_PersistentArray_append___redArg(v_reported_3252_, v_unreported_3253_);
lean_dec_ref(v_unreported_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3255_){
_start:
{
lean_object* v_unreported_3256_; uint8_t v___x_3257_; 
v_unreported_3256_ = lean_ctor_get(v_log_3255_, 1);
v___x_3257_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3256_);
if (v___x_3257_ == 0)
{
uint8_t v___x_3258_; 
v___x_3258_ = 1;
return v___x_3258_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = 0;
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Lean_MessageLog_hasUnreported(v_log_3260_);
lean_dec_ref(v_log_3260_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3263_, lean_object* v_log_3264_){
_start:
{
lean_object* v_reported_3265_; lean_object* v_unreported_3266_; lean_object* v_loggedKinds_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3275_; 
v_reported_3265_ = lean_ctor_get(v_log_3264_, 0);
v_unreported_3266_ = lean_ctor_get(v_log_3264_, 1);
v_loggedKinds_3267_ = lean_ctor_get(v_log_3264_, 2);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_log_3264_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3269_ = v_log_3264_;
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_loggedKinds_3267_);
lean_inc(v_unreported_3266_);
lean_inc(v_reported_3265_);
lean_dec(v_log_3264_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = l_Lean_PersistentArray_push___redArg(v_unreported_3266_, v_msg_3263_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v___x_3271_);
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_reported_3265_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_loggedKinds_3267_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_b_u2082_3278_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3282_, v_x_3283_);
lean_dec(v_x_3283_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3285_, lean_object* v_k_3286_, lean_object* v_t_3287_){
_start:
{
if (lean_obj_tag(v_t_3287_) == 0)
{
lean_object* v_size_3288_; lean_object* v_k_3289_; lean_object* v_v_3290_; lean_object* v_l_3291_; lean_object* v_r_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3307_; 
v_size_3288_ = lean_ctor_get(v_t_3287_, 0);
v_k_3289_ = lean_ctor_get(v_t_3287_, 1);
v_v_3290_ = lean_ctor_get(v_t_3287_, 2);
v_l_3291_ = lean_ctor_get(v_t_3287_, 3);
v_r_3292_ = lean_ctor_get(v_t_3287_, 4);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_t_3287_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3294_ = v_t_3287_;
v_isShared_3295_ = v_isSharedCheck_3307_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_r_3292_);
lean_inc(v_l_3291_);
lean_inc(v_v_3290_);
lean_inc(v_k_3289_);
lean_inc(v_size_3288_);
lean_dec(v_t_3287_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3307_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
uint8_t v___x_3296_; 
v___x_3296_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3286_, v_k_3289_);
switch(v___x_3296_)
{
case 0:
{
lean_object* v_impl_3297_; lean_object* v___x_3298_; 
lean_del_object(v___x_3294_);
lean_dec(v_size_3288_);
v_impl_3297_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3285_, v_k_3286_, v_l_3291_);
v___x_3298_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3289_, v_v_3290_, v_impl_3297_, v_r_3292_);
return v___x_3298_;
}
case 1:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_val_3301_; lean_object* v___x_3303_; 
lean_dec(v_k_3289_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_v_3290_);
v___x_3300_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3285_, v___x_3299_);
lean_dec_ref_known(v___x_3299_, 1);
v_val_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_val_3301_);
lean_dec(v___x_3300_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 2, v_val_3301_);
lean_ctor_set(v___x_3294_, 1, v_k_3286_);
v___x_3303_ = v___x_3294_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_size_3288_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_k_3286_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_val_3301_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_l_3291_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_r_3292_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
default: 
{
lean_object* v_impl_3305_; lean_object* v___x_3306_; 
lean_del_object(v___x_3294_);
lean_dec(v_size_3288_);
v_impl_3305_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3285_, v_k_3286_, v_r_3292_);
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3289_, v_v_3290_, v_l_3291_, v_impl_3305_);
return v___x_3306_;
}
}
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_val_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3285_, v___x_3308_);
v_val_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_val_3310_);
lean_dec(v___x_3309_);
v___x_3311_ = lean_unsigned_to_nat(1u);
v___x_3312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v_k_3286_);
lean_ctor_set(v___x_3312_, 2, v_val_3310_);
lean_ctor_set(v___x_3312_, 3, v_t_3287_);
lean_ctor_set(v___x_3312_, 4, v_t_3287_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 0)
{
lean_object* v_k_3315_; lean_object* v_v_3316_; lean_object* v_l_3317_; lean_object* v_r_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_k_3315_ = lean_ctor_get(v_x_3314_, 1);
lean_inc(v_k_3315_);
v_v_3316_ = lean_ctor_get(v_x_3314_, 2);
lean_inc(v_v_3316_);
v_l_3317_ = lean_ctor_get(v_x_3314_, 3);
lean_inc(v_l_3317_);
v_r_3318_ = lean_ctor_get(v_x_3314_, 4);
lean_inc(v_r_3318_);
lean_dec_ref_known(v_x_3314_, 5);
v___x_3319_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3313_, v_l_3317_);
v___x_3320_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3316_, v_k_3315_, v___x_3319_);
v_init_3313_ = v___x_3320_;
v_x_3314_ = v_r_3318_;
goto _start;
}
else
{
return v_init_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3322_, lean_object* v_l_u2082_3323_){
_start:
{
lean_object* v_reported_3324_; lean_object* v_unreported_3325_; lean_object* v_loggedKinds_3326_; lean_object* v_reported_3327_; lean_object* v_unreported_3328_; lean_object* v_loggedKinds_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3339_; 
v_reported_3324_ = lean_ctor_get(v_l_u2081_3322_, 0);
lean_inc_ref(v_reported_3324_);
v_unreported_3325_ = lean_ctor_get(v_l_u2081_3322_, 1);
lean_inc_ref(v_unreported_3325_);
v_loggedKinds_3326_ = lean_ctor_get(v_l_u2081_3322_, 2);
lean_inc(v_loggedKinds_3326_);
lean_dec_ref(v_l_u2081_3322_);
v_reported_3327_ = lean_ctor_get(v_l_u2082_3323_, 0);
v_unreported_3328_ = lean_ctor_get(v_l_u2082_3323_, 1);
v_loggedKinds_3329_ = lean_ctor_get(v_l_u2082_3323_, 2);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_l_u2082_3323_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3331_ = v_l_u2082_3323_;
v_isShared_3332_ = v_isSharedCheck_3339_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_loggedKinds_3329_);
lean_inc(v_unreported_3328_);
lean_inc(v_reported_3327_);
lean_dec(v_l_u2082_3323_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3339_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3333_ = l_Lean_PersistentArray_append___redArg(v_reported_3324_, v_reported_3327_);
lean_dec_ref(v_reported_3327_);
v___x_3334_ = l_Lean_PersistentArray_append___redArg(v_unreported_3325_, v_unreported_3328_);
lean_dec_ref(v_unreported_3328_);
v___x_3335_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3326_, v_loggedKinds_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 2, v___x_3335_);
lean_ctor_set(v___x_3331_, 1, v___x_3334_);
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3337_ = v___x_3331_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3340_, lean_object* v_k_3341_, lean_object* v_t_3342_, lean_object* v_hl_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3340_, v_k_3341_, v_t_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3345_, lean_object* v_t_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3345_, v_t_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3350_, size_t v_i_3351_, size_t v_stop_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_eq(v_i_3351_, v_stop_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; uint8_t v_severity_3355_; 
v___x_3354_ = lean_array_uget_borrowed(v_as_3350_, v_i_3351_);
v_severity_3355_ = lean_ctor_get_uint8(v___x_3354_, sizeof(void*)*5 + 1);
if (v_severity_3355_ == 2)
{
uint8_t v___x_3356_; 
v___x_3356_ = 1;
return v___x_3356_;
}
else
{
size_t v___x_3357_; size_t v___x_3358_; 
v___x_3357_ = ((size_t)1ULL);
v___x_3358_ = lean_usize_add(v_i_3351_, v___x_3357_);
v_i_3351_ = v___x_3358_;
goto _start;
}
}
else
{
uint8_t v___x_3360_; 
v___x_3360_ = 0;
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3361_, lean_object* v_i_3362_, lean_object* v_stop_3363_){
_start:
{
size_t v_i_boxed_3364_; size_t v_stop_boxed_3365_; uint8_t v_res_3366_; lean_object* v_r_3367_; 
v_i_boxed_3364_ = lean_unbox_usize(v_i_3362_);
lean_dec(v_i_3362_);
v_stop_boxed_3365_ = lean_unbox_usize(v_stop_3363_);
lean_dec(v_stop_3363_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3361_, v_i_boxed_3364_, v_stop_boxed_3365_);
lean_dec_ref(v_as_3361_);
v_r_3367_ = lean_box(v_res_3366_);
return v_r_3367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3368_){
_start:
{
if (lean_obj_tag(v_x_3368_) == 0)
{
lean_object* v_cs_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_cs_3369_ = lean_ctor_get(v_x_3368_, 0);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_array_get_size(v_cs_3369_);
v___x_3372_ = lean_nat_dec_lt(v___x_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
return v___x_3372_;
}
else
{
if (v___x_3372_ == 0)
{
return v___x_3372_;
}
else
{
size_t v___x_3373_; size_t v___x_3374_; uint8_t v___x_3375_; 
v___x_3373_ = ((size_t)0ULL);
v___x_3374_ = lean_usize_of_nat(v___x_3371_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3369_, v___x_3373_, v___x_3374_);
return v___x_3375_;
}
}
}
else
{
lean_object* v_vs_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_vs_3376_ = lean_ctor_get(v_x_3368_, 0);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = lean_array_get_size(v_vs_3376_);
v___x_3379_ = lean_nat_dec_lt(v___x_3377_, v___x_3378_);
if (v___x_3379_ == 0)
{
return v___x_3379_;
}
else
{
if (v___x_3379_ == 0)
{
return v___x_3379_;
}
else
{
size_t v___x_3380_; size_t v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = lean_usize_of_nat(v___x_3378_);
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3376_, v___x_3380_, v___x_3381_);
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3383_, size_t v_i_3384_, size_t v_stop_3385_){
_start:
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_usize_dec_eq(v_i_3384_, v_stop_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_array_uget_borrowed(v_as_3383_, v_i_3384_);
v___x_3388_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3387_);
if (v___x_3388_ == 0)
{
size_t v___x_3389_; size_t v___x_3390_; 
v___x_3389_ = ((size_t)1ULL);
v___x_3390_ = lean_usize_add(v_i_3384_, v___x_3389_);
v_i_3384_ = v___x_3390_;
goto _start;
}
else
{
return v___x_3388_;
}
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = 0;
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3393_, lean_object* v_i_3394_, lean_object* v_stop_3395_){
_start:
{
size_t v_i_boxed_3396_; size_t v_stop_boxed_3397_; uint8_t v_res_3398_; lean_object* v_r_3399_; 
v_i_boxed_3396_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_stop_boxed_3397_ = lean_unbox_usize(v_stop_3395_);
lean_dec(v_stop_3395_);
v_res_3398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3393_, v_i_boxed_3396_, v_stop_boxed_3397_);
lean_dec_ref(v_as_3393_);
v_r_3399_ = lean_box(v_res_3398_);
return v_r_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3400_);
lean_dec_ref(v_x_3400_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3403_){
_start:
{
lean_object* v_root_3404_; lean_object* v_tail_3405_; uint8_t v___x_3406_; 
v_root_3404_ = lean_ctor_get(v_t_3403_, 0);
v_tail_3405_ = lean_ctor_get(v_t_3403_, 1);
v___x_3406_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3404_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = lean_array_get_size(v_tail_3405_);
v___x_3409_ = lean_nat_dec_lt(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
return v___x_3409_;
}
else
{
if (v___x_3409_ == 0)
{
return v___x_3409_;
}
else
{
size_t v___x_3410_; size_t v___x_3411_; uint8_t v___x_3412_; 
v___x_3410_ = ((size_t)0ULL);
v___x_3411_ = lean_usize_of_nat(v___x_3408_);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3405_, v___x_3410_, v___x_3411_);
return v___x_3412_;
}
}
}
else
{
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3413_){
_start:
{
uint8_t v_res_3414_; lean_object* v_r_3415_; 
v_res_3414_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3413_);
lean_dec_ref(v_t_3413_);
v_r_3415_ = lean_box(v_res_3414_);
return v_r_3415_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3416_, lean_object* v_as_3417_, size_t v_i_3418_, size_t v_stop_3419_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_eq(v_i_3418_, v_stop_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; uint8_t v_severity_3422_; uint8_t v___x_3423_; 
v___x_3421_ = lean_array_uget_borrowed(v_as_3417_, v_i_3418_);
v_severity_3422_ = lean_ctor_get_uint8(v___x_3421_, sizeof(void*)*5 + 1);
v___x_3423_ = 1;
if (v_severity_3422_ == 2)
{
return v___x_3423_;
}
else
{
if (v___x_3416_ == 0)
{
size_t v___x_3424_; size_t v___x_3425_; 
v___x_3424_ = ((size_t)1ULL);
v___x_3425_ = lean_usize_add(v_i_3418_, v___x_3424_);
v_i_3418_ = v___x_3425_;
goto _start;
}
else
{
return v___x_3423_;
}
}
}
else
{
uint8_t v___x_3427_; 
v___x_3427_ = 0;
return v___x_3427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3428_, lean_object* v_as_3429_, lean_object* v_i_3430_, lean_object* v_stop_3431_){
_start:
{
uint8_t v___x_1809__boxed_3432_; size_t v_i_boxed_3433_; size_t v_stop_boxed_3434_; uint8_t v_res_3435_; lean_object* v_r_3436_; 
v___x_1809__boxed_3432_ = lean_unbox(v___x_3428_);
v_i_boxed_3433_ = lean_unbox_usize(v_i_3430_);
lean_dec(v_i_3430_);
v_stop_boxed_3434_ = lean_unbox_usize(v_stop_3431_);
lean_dec(v_stop_3431_);
v_res_3435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3432_, v_as_3429_, v_i_boxed_3433_, v_stop_boxed_3434_);
lean_dec_ref(v_as_3429_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3437_, lean_object* v_x_3438_){
_start:
{
if (lean_obj_tag(v_x_3438_) == 0)
{
lean_object* v_cs_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v_cs_3439_ = lean_ctor_get(v_x_3438_, 0);
v___x_3440_ = lean_unsigned_to_nat(0u);
v___x_3441_ = lean_array_get_size(v_cs_3439_);
v___x_3442_ = lean_nat_dec_lt(v___x_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
return v___x_3442_;
}
else
{
if (v___x_3442_ == 0)
{
return v___x_3442_;
}
else
{
size_t v___x_3443_; size_t v___x_3444_; uint8_t v___x_3445_; 
v___x_3443_ = ((size_t)0ULL);
v___x_3444_ = lean_usize_of_nat(v___x_3441_);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3437_, v_cs_3439_, v___x_3443_, v___x_3444_);
return v___x_3445_;
}
}
}
else
{
lean_object* v_vs_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_vs_3446_ = lean_ctor_get(v_x_3438_, 0);
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_array_get_size(v_vs_3446_);
v___x_3449_ = lean_nat_dec_lt(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
return v___x_3449_;
}
else
{
if (v___x_3449_ == 0)
{
return v___x_3449_;
}
else
{
size_t v___x_3450_; size_t v___x_3451_; uint8_t v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___x_3448_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3437_, v_vs_3446_, v___x_3450_, v___x_3451_);
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3453_, lean_object* v_as_3454_, size_t v_i_3455_, size_t v_stop_3456_){
_start:
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_usize_dec_eq(v_i_3455_, v_stop_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = lean_array_uget_borrowed(v_as_3454_, v_i_3455_);
v___x_3459_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3453_, v___x_3458_);
if (v___x_3459_ == 0)
{
size_t v___x_3460_; size_t v___x_3461_; 
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3455_, v___x_3460_);
v_i_3455_ = v___x_3461_;
goto _start;
}
else
{
return v___x_3459_;
}
}
else
{
uint8_t v___x_3463_; 
v___x_3463_ = 0;
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3464_, lean_object* v_as_3465_, lean_object* v_i_3466_, lean_object* v_stop_3467_){
_start:
{
uint8_t v___x_1826__boxed_3468_; size_t v_i_boxed_3469_; size_t v_stop_boxed_3470_; uint8_t v_res_3471_; lean_object* v_r_3472_; 
v___x_1826__boxed_3468_ = lean_unbox(v___x_3464_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_stop_boxed_3470_ = lean_unbox_usize(v_stop_3467_);
lean_dec(v_stop_3467_);
v_res_3471_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3468_, v_as_3465_, v_i_boxed_3469_, v_stop_boxed_3470_);
lean_dec_ref(v_as_3465_);
v_r_3472_ = lean_box(v_res_3471_);
return v_r_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3473_, lean_object* v_x_3474_){
_start:
{
uint8_t v___x_1834__boxed_3475_; uint8_t v_res_3476_; lean_object* v_r_3477_; 
v___x_1834__boxed_3475_ = lean_unbox(v___x_3473_);
v_res_3476_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3475_, v_x_3474_);
lean_dec_ref(v_x_3474_);
v_r_3477_ = lean_box(v_res_3476_);
return v_r_3477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3478_, lean_object* v_t_3479_){
_start:
{
lean_object* v_root_3480_; lean_object* v_tail_3481_; uint8_t v___x_3482_; 
v_root_3480_ = lean_ctor_get(v_t_3479_, 0);
v_tail_3481_ = lean_ctor_get(v_t_3479_, 1);
v___x_3482_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3478_, v_root_3480_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_array_get_size(v_tail_3481_);
v___x_3485_ = lean_nat_dec_lt(v___x_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
return v___x_3485_;
}
else
{
if (v___x_3485_ == 0)
{
return v___x_3485_;
}
else
{
size_t v___x_3486_; size_t v___x_3487_; uint8_t v___x_3488_; 
v___x_3486_ = ((size_t)0ULL);
v___x_3487_ = lean_usize_of_nat(v___x_3484_);
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3478_, v_tail_3481_, v___x_3486_, v___x_3487_);
return v___x_3488_;
}
}
}
else
{
return v___x_3482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3489_, lean_object* v_t_3490_){
_start:
{
uint8_t v___x_1877__boxed_3491_; uint8_t v_res_3492_; lean_object* v_r_3493_; 
v___x_1877__boxed_3491_ = lean_unbox(v___x_3489_);
v_res_3492_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3491_, v_t_3490_);
lean_dec_ref(v_t_3490_);
v_r_3493_ = lean_box(v_res_3492_);
return v_r_3493_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3494_){
_start:
{
lean_object* v_reported_3495_; lean_object* v_unreported_3496_; uint8_t v___x_3497_; 
v_reported_3495_ = lean_ctor_get(v_log_3494_, 0);
v_unreported_3496_ = lean_ctor_get(v_log_3494_, 1);
v___x_3497_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3495_);
if (v___x_3497_ == 0)
{
uint8_t v___x_3498_; 
v___x_3498_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3497_, v_unreported_3496_);
return v___x_3498_;
}
else
{
return v___x_3497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3499_){
_start:
{
uint8_t v_res_3500_; lean_object* v_r_3501_; 
v_res_3500_ = l_Lean_MessageLog_hasErrors(v_log_3499_);
lean_dec_ref(v_log_3499_);
v_r_3501_ = lean_box(v_res_3500_);
return v_r_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3502_){
_start:
{
lean_object* v_reported_3503_; lean_object* v_unreported_3504_; lean_object* v_loggedKinds_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3516_; 
v_reported_3503_ = lean_ctor_get(v_log_3502_, 0);
v_unreported_3504_ = lean_ctor_get(v_log_3502_, 1);
v_loggedKinds_3505_ = lean_ctor_get(v_log_3502_, 2);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_log_3502_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3507_ = v_log_3502_;
v_isShared_3508_ = v_isSharedCheck_3516_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_loggedKinds_3505_);
lean_inc(v_unreported_3504_);
lean_inc(v_reported_3503_);
lean_dec(v_log_3502_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3516_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3509_ = l_Lean_PersistentArray_append___redArg(v_reported_3503_, v_unreported_3504_);
lean_dec_ref(v_unreported_3504_);
v___x_3510_ = lean_unsigned_to_nat(32u);
v___x_3511_ = lean_mk_empty_array_with_capacity(v___x_3510_);
lean_dec_ref(v___x_3511_);
v___x_3512_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3512_);
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3514_ = v___x_3507_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_loggedKinds_3505_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3517_, size_t v_i_3518_, lean_object* v_bs_3519_){
_start:
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_usize_dec_lt(v_i_3518_, v_sz_3517_);
if (v___x_3520_ == 0)
{
return v_bs_3519_;
}
else
{
lean_object* v_v_3521_; lean_object* v_fileName_3522_; lean_object* v_pos_3523_; lean_object* v_endPos_3524_; uint8_t v_keepFullRange_3525_; uint8_t v_severity_3526_; uint8_t v_isSilent_3527_; lean_object* v_caption_3528_; lean_object* v_data_3529_; lean_object* v___x_3530_; lean_object* v_bs_x27_3531_; lean_object* v___y_3533_; 
v_v_3521_ = lean_array_uget(v_bs_3519_, v_i_3518_);
v_fileName_3522_ = lean_ctor_get(v_v_3521_, 0);
v_pos_3523_ = lean_ctor_get(v_v_3521_, 1);
v_endPos_3524_ = lean_ctor_get(v_v_3521_, 2);
v_keepFullRange_3525_ = lean_ctor_get_uint8(v_v_3521_, sizeof(void*)*5);
v_severity_3526_ = lean_ctor_get_uint8(v_v_3521_, sizeof(void*)*5 + 1);
v_isSilent_3527_ = lean_ctor_get_uint8(v_v_3521_, sizeof(void*)*5 + 2);
v_caption_3528_ = lean_ctor_get(v_v_3521_, 3);
v_data_3529_ = lean_ctor_get(v_v_3521_, 4);
v___x_3530_ = lean_unsigned_to_nat(0u);
v_bs_x27_3531_ = lean_array_uset(v_bs_3519_, v_i_3518_, v___x_3530_);
if (v_severity_3526_ == 2)
{
lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3545_; 
lean_inc(v_data_3529_);
lean_inc_ref(v_caption_3528_);
lean_inc(v_endPos_3524_);
lean_inc_ref(v_pos_3523_);
lean_inc_ref(v_fileName_3522_);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_v_3521_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; 
v_unused_3546_ = lean_ctor_get(v_v_3521_, 4);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_v_3521_, 3);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_v_3521_, 2);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_v_3521_, 1);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_v_3521_, 0);
lean_dec(v_unused_3550_);
v___x_3539_ = v_v_3521_;
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
else
{
lean_dec(v_v_3521_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
uint8_t v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = 1;
if (v_isShared_3540_ == 0)
{
v___x_3543_ = v___x_3539_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_fileName_3522_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_pos_3523_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_endPos_3524_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_caption_3528_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_data_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3544_, sizeof(void*)*5, v_keepFullRange_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3544_, sizeof(void*)*5 + 2, v_isSilent_3527_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_ctor_set_uint8(v___x_3543_, sizeof(void*)*5 + 1, v___x_3541_);
v___y_3533_ = v___x_3543_;
goto v___jp_3532_;
}
}
}
else
{
v___y_3533_ = v_v_3521_;
goto v___jp_3532_;
}
v___jp_3532_:
{
size_t v___x_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_add(v_i_3518_, v___x_3534_);
v___x_3536_ = lean_array_uset(v_bs_x27_3531_, v_i_3518_, v___y_3533_);
v_i_3518_ = v___x_3535_;
v_bs_3519_ = v___x_3536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3551_, lean_object* v_i_3552_, lean_object* v_bs_3553_){
_start:
{
size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3551_);
lean_dec(v_sz_3551_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3554_, v_i_boxed_3555_, v_bs_3553_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3560_ == 0)
{
return v_bs_3559_;
}
else
{
lean_object* v_v_3561_; lean_object* v___x_3562_; lean_object* v_bs_x27_3563_; lean_object* v___x_3564_; size_t v___x_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
v_v_3561_ = lean_array_uget(v_bs_3559_, v_i_3558_);
v___x_3562_ = lean_unsigned_to_nat(0u);
v_bs_x27_3563_ = lean_array_uset(v_bs_3559_, v_i_3558_, v___x_3562_);
v___x_3564_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3561_);
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_add(v_i_3558_, v___x_3565_);
v___x_3567_ = lean_array_uset(v_bs_x27_3563_, v_i_3558_, v___x_3564_);
v_i_3558_ = v___x_3566_;
v_bs_3559_ = v___x_3567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3569_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_object* v_cs_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3580_; 
v_cs_3570_ = lean_ctor_get(v_x_3569_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_x_3569_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3572_ = v_x_3569_;
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_cs_3570_);
lean_dec(v_x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
size_t v_sz_3574_; size_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v_sz_3574_ = lean_array_size(v_cs_3570_);
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3574_, v___x_3575_, v_cs_3570_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3576_);
v___x_3578_ = v___x_3572_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_vs_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3591_; 
v_vs_3581_ = lean_ctor_get(v_x_3569_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_x_3569_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3583_ = v_x_3569_;
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_vs_3581_);
lean_dec(v_x_3569_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3591_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
size_t v_sz_3585_; size_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v_sz_3585_ = lean_array_size(v_vs_3581_);
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3585_, v___x_3586_, v_vs_3581_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3592_, lean_object* v_i_3593_, lean_object* v_bs_3594_){
_start:
{
size_t v_sz_boxed_3595_; size_t v_i_boxed_3596_; lean_object* v_res_3597_; 
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3592_);
lean_dec(v_sz_3592_);
v_i_boxed_3596_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_res_3597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3595_, v_i_boxed_3596_, v_bs_3594_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3598_){
_start:
{
lean_object* v_root_3599_; lean_object* v_tail_3600_; lean_object* v_size_3601_; size_t v_shift_3602_; lean_object* v_tailOff_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3614_; 
v_root_3599_ = lean_ctor_get(v_t_3598_, 0);
v_tail_3600_ = lean_ctor_get(v_t_3598_, 1);
v_size_3601_ = lean_ctor_get(v_t_3598_, 2);
v_shift_3602_ = lean_ctor_get_usize(v_t_3598_, 4);
v_tailOff_3603_ = lean_ctor_get(v_t_3598_, 3);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_t_3598_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3605_ = v_t_3598_;
v_isShared_3606_ = v_isSharedCheck_3614_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_tailOff_3603_);
lean_inc(v_size_3601_);
lean_inc(v_tail_3600_);
lean_inc(v_root_3599_);
lean_dec(v_t_3598_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3614_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; size_t v_sz_3608_; size_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3607_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3599_);
v_sz_3608_ = lean_array_size(v_tail_3600_);
v___x_3609_ = ((size_t)0ULL);
v___x_3610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3608_, v___x_3609_, v_tail_3600_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v___x_3610_);
lean_ctor_set(v___x_3605_, 0, v___x_3607_);
v___x_3612_ = v___x_3605_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_size_3601_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_tailOff_3603_);
lean_ctor_set_usize(v_reuseFailAlloc_3613_, 4, v_shift_3602_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3615_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v_unreported_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3628_; 
v___x_3616_ = lean_unsigned_to_nat(32u);
v___x_3617_ = lean_mk_empty_array_with_capacity(v___x_3616_);
lean_dec_ref(v___x_3617_);
v___x_3618_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3619_ = lean_ctor_get(v_log_3615_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_log_3615_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3629_ = lean_ctor_get(v_log_3615_, 2);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_log_3615_, 0);
lean_dec(v_unused_3630_);
v___x_3621_ = v_log_3615_;
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_unreported_3619_);
lean_dec(v_log_3615_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3623_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3619_);
v___x_3624_ = l_Lean_NameSet_empty;
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 2, v___x_3624_);
lean_ctor_set(v___x_3621_, 1, v___x_3623_);
lean_ctor_set(v___x_3621_, 0, v___x_3618_);
v___x_3626_ = v___x_3621_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3631_, size_t v_i_3632_, lean_object* v_bs_3633_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_lt(v_i_3632_, v_sz_3631_);
if (v___x_3634_ == 0)
{
return v_bs_3633_;
}
else
{
lean_object* v_v_3635_; lean_object* v_fileName_3636_; lean_object* v_pos_3637_; lean_object* v_endPos_3638_; uint8_t v_keepFullRange_3639_; uint8_t v_severity_3640_; uint8_t v_isSilent_3641_; lean_object* v_caption_3642_; lean_object* v_data_3643_; lean_object* v___x_3644_; lean_object* v_bs_x27_3645_; lean_object* v___y_3647_; 
v_v_3635_ = lean_array_uget(v_bs_3633_, v_i_3632_);
v_fileName_3636_ = lean_ctor_get(v_v_3635_, 0);
v_pos_3637_ = lean_ctor_get(v_v_3635_, 1);
v_endPos_3638_ = lean_ctor_get(v_v_3635_, 2);
v_keepFullRange_3639_ = lean_ctor_get_uint8(v_v_3635_, sizeof(void*)*5);
v_severity_3640_ = lean_ctor_get_uint8(v_v_3635_, sizeof(void*)*5 + 1);
v_isSilent_3641_ = lean_ctor_get_uint8(v_v_3635_, sizeof(void*)*5 + 2);
v_caption_3642_ = lean_ctor_get(v_v_3635_, 3);
v_data_3643_ = lean_ctor_get(v_v_3635_, 4);
v___x_3644_ = lean_unsigned_to_nat(0u);
v_bs_x27_3645_ = lean_array_uset(v_bs_3633_, v_i_3632_, v___x_3644_);
if (v_severity_3640_ == 2)
{
lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3659_; 
lean_inc(v_data_3643_);
lean_inc_ref(v_caption_3642_);
lean_inc(v_endPos_3638_);
lean_inc_ref(v_pos_3637_);
lean_inc_ref(v_fileName_3636_);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_v_3635_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; lean_object* v_unused_3661_; lean_object* v_unused_3662_; lean_object* v_unused_3663_; lean_object* v_unused_3664_; 
v_unused_3660_ = lean_ctor_get(v_v_3635_, 4);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v_v_3635_, 3);
lean_dec(v_unused_3661_);
v_unused_3662_ = lean_ctor_get(v_v_3635_, 2);
lean_dec(v_unused_3662_);
v_unused_3663_ = lean_ctor_get(v_v_3635_, 1);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_v_3635_, 0);
lean_dec(v_unused_3664_);
v___x_3653_ = v_v_3635_;
v_isShared_3654_ = v_isSharedCheck_3659_;
goto v_resetjp_3652_;
}
else
{
lean_dec(v_v_3635_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3659_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
uint8_t v___x_3655_; lean_object* v___x_3657_; 
v___x_3655_ = 0;
if (v_isShared_3654_ == 0)
{
v___x_3657_ = v___x_3653_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_fileName_3636_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_pos_3637_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_endPos_3638_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v_caption_3642_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v_data_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*5, v_keepFullRange_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*5 + 2, v_isSilent_3641_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_ctor_set_uint8(v___x_3657_, sizeof(void*)*5 + 1, v___x_3655_);
v___y_3647_ = v___x_3657_;
goto v___jp_3646_;
}
}
}
else
{
v___y_3647_ = v_v_3635_;
goto v___jp_3646_;
}
v___jp_3646_:
{
size_t v___x_3648_; size_t v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3632_, v___x_3648_);
v___x_3650_ = lean_array_uset(v_bs_x27_3645_, v_i_3632_, v___y_3647_);
v_i_3632_ = v___x_3649_;
v_bs_3633_ = v___x_3650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_bs_3667_){
_start:
{
size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3668_, v_i_boxed_3669_, v_bs_3667_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3671_, size_t v_i_3672_, lean_object* v_bs_3673_){
_start:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_usize_dec_lt(v_i_3672_, v_sz_3671_);
if (v___x_3674_ == 0)
{
return v_bs_3673_;
}
else
{
lean_object* v_v_3675_; lean_object* v___x_3676_; lean_object* v_bs_x27_3677_; lean_object* v___x_3678_; size_t v___x_3679_; size_t v___x_3680_; lean_object* v___x_3681_; 
v_v_3675_ = lean_array_uget(v_bs_3673_, v_i_3672_);
v___x_3676_ = lean_unsigned_to_nat(0u);
v_bs_x27_3677_ = lean_array_uset(v_bs_3673_, v_i_3672_, v___x_3676_);
v___x_3678_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3675_);
v___x_3679_ = ((size_t)1ULL);
v___x_3680_ = lean_usize_add(v_i_3672_, v___x_3679_);
v___x_3681_ = lean_array_uset(v_bs_x27_3677_, v_i_3672_, v___x_3678_);
v_i_3672_ = v___x_3680_;
v_bs_3673_ = v___x_3681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3683_){
_start:
{
if (lean_obj_tag(v_x_3683_) == 0)
{
lean_object* v_cs_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3694_; 
v_cs_3684_ = lean_ctor_get(v_x_3683_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_x_3683_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3686_ = v_x_3683_;
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_cs_3684_);
lean_dec(v_x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
size_t v_sz_3688_; size_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v_sz_3688_ = lean_array_size(v_cs_3684_);
v___x_3689_ = ((size_t)0ULL);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3688_, v___x_3689_, v_cs_3684_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3690_);
v___x_3692_ = v___x_3686_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
else
{
lean_object* v_vs_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3705_; 
v_vs_3695_ = lean_ctor_get(v_x_3683_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_x_3683_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3697_ = v_x_3683_;
v_isShared_3698_ = v_isSharedCheck_3705_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_vs_3695_);
lean_dec(v_x_3683_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3705_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
size_t v_sz_3699_; size_t v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v_sz_3699_ = lean_array_size(v_vs_3695_);
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3699_, v___x_3700_, v_vs_3695_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3701_);
v___x_3703_ = v___x_3697_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3706_, lean_object* v_i_3707_, lean_object* v_bs_3708_){
_start:
{
size_t v_sz_boxed_3709_; size_t v_i_boxed_3710_; lean_object* v_res_3711_; 
v_sz_boxed_3709_ = lean_unbox_usize(v_sz_3706_);
lean_dec(v_sz_3706_);
v_i_boxed_3710_ = lean_unbox_usize(v_i_3707_);
lean_dec(v_i_3707_);
v_res_3711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3709_, v_i_boxed_3710_, v_bs_3708_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3712_){
_start:
{
lean_object* v_root_3713_; lean_object* v_tail_3714_; lean_object* v_size_3715_; size_t v_shift_3716_; lean_object* v_tailOff_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3728_; 
v_root_3713_ = lean_ctor_get(v_t_3712_, 0);
v_tail_3714_ = lean_ctor_get(v_t_3712_, 1);
v_size_3715_ = lean_ctor_get(v_t_3712_, 2);
v_shift_3716_ = lean_ctor_get_usize(v_t_3712_, 4);
v_tailOff_3717_ = lean_ctor_get(v_t_3712_, 3);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_t_3712_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3719_ = v_t_3712_;
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_tailOff_3717_);
lean_inc(v_size_3715_);
lean_inc(v_tail_3714_);
lean_inc(v_root_3713_);
lean_dec(v_t_3712_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3728_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; size_t v_sz_3722_; size_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3721_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3713_);
v_sz_3722_ = lean_array_size(v_tail_3714_);
v___x_3723_ = ((size_t)0ULL);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3722_, v___x_3723_, v_tail_3714_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 1, v___x_3724_);
lean_ctor_set(v___x_3719_, 0, v___x_3721_);
v___x_3726_ = v___x_3719_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_size_3715_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_tailOff_3717_);
lean_ctor_set_usize(v_reuseFailAlloc_3727_, 4, v_shift_3716_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3729_){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_unreported_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3742_; 
v___x_3730_ = lean_unsigned_to_nat(32u);
v___x_3731_ = lean_mk_empty_array_with_capacity(v___x_3730_);
lean_dec_ref(v___x_3731_);
v___x_3732_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3733_ = lean_ctor_get(v_log_3729_, 1);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_log_3729_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; 
v_unused_3743_ = lean_ctor_get(v_log_3729_, 2);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_log_3729_, 0);
lean_dec(v_unused_3744_);
v___x_3735_ = v_log_3729_;
v_isShared_3736_ = v_isSharedCheck_3742_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_unreported_3733_);
lean_dec(v_log_3729_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3742_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v___x_3737_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3733_);
v___x_3738_ = l_Lean_NameSet_empty;
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 2, v___x_3738_);
lean_ctor_set(v___x_3735_, 1, v___x_3737_);
lean_ctor_set(v___x_3735_, 0, v___x_3732_);
v___x_3740_ = v___x_3735_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3745_, size_t v_i_3746_, size_t v_stop_3747_, lean_object* v_b_3748_){
_start:
{
lean_object* v___y_3750_; uint8_t v___x_3754_; 
v___x_3754_ = lean_usize_dec_eq(v_i_3746_, v_stop_3747_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; uint8_t v_severity_3756_; 
v___x_3755_ = lean_array_uget_borrowed(v_as_3745_, v_i_3746_);
v_severity_3756_ = lean_ctor_get_uint8(v___x_3755_, sizeof(void*)*5 + 1);
if (v_severity_3756_ == 0)
{
lean_object* v___x_3757_; 
lean_inc(v___x_3755_);
v___x_3757_ = l_Lean_PersistentArray_push___redArg(v_b_3748_, v___x_3755_);
v___y_3750_ = v___x_3757_;
goto v___jp_3749_;
}
else
{
v___y_3750_ = v_b_3748_;
goto v___jp_3749_;
}
}
else
{
return v_b_3748_;
}
v___jp_3749_:
{
size_t v___x_3751_; size_t v___x_3752_; 
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3746_, v___x_3751_);
v_i_3746_ = v___x_3752_;
v_b_3748_ = v___y_3750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3758_, lean_object* v_i_3759_, lean_object* v_stop_3760_, lean_object* v_b_3761_){
_start:
{
size_t v_i_boxed_3762_; size_t v_stop_boxed_3763_; lean_object* v_res_3764_; 
v_i_boxed_3762_ = lean_unbox_usize(v_i_3759_);
lean_dec(v_i_3759_);
v_stop_boxed_3763_ = lean_unbox_usize(v_stop_3760_);
lean_dec(v_stop_3760_);
v_res_3764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3758_, v_i_boxed_3762_, v_stop_boxed_3763_, v_b_3761_);
lean_dec_ref(v_as_3758_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 0)
{
lean_object* v_cs_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_cs_3767_ = lean_ctor_get(v_x_3765_, 0);
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = lean_array_get_size(v_cs_3767_);
v___x_3770_ = lean_nat_dec_lt(v___x_3768_, v___x_3769_);
if (v___x_3770_ == 0)
{
return v_x_3766_;
}
else
{
size_t v___x_3771_; size_t v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = lean_usize_of_nat(v___x_3769_);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3767_, v___x_3771_, v___x_3772_, v_x_3766_);
return v___x_3773_;
}
}
else
{
lean_object* v_vs_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_vs_3774_ = lean_ctor_get(v_x_3765_, 0);
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = lean_array_get_size(v_vs_3774_);
v___x_3777_ = lean_nat_dec_lt(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
return v_x_3766_;
}
else
{
size_t v___x_3778_; size_t v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = ((size_t)0ULL);
v___x_3779_ = lean_usize_of_nat(v___x_3776_);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3774_, v___x_3778_, v___x_3779_, v_x_3766_);
return v___x_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3781_, size_t v_i_3782_, size_t v_stop_3783_, lean_object* v_b_3784_){
_start:
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_usize_dec_eq(v_i_3782_, v_stop_3783_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; size_t v___x_3788_; size_t v___x_3789_; 
v___x_3786_ = lean_array_uget_borrowed(v_as_3781_, v_i_3782_);
v___x_3787_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3786_, v_b_3784_);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3782_, v___x_3788_);
v_i_3782_ = v___x_3789_;
v_b_3784_ = v___x_3787_;
goto _start;
}
else
{
return v_b_3784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3791_, lean_object* v_i_3792_, lean_object* v_stop_3793_, lean_object* v_b_3794_){
_start:
{
size_t v_i_boxed_3795_; size_t v_stop_boxed_3796_; lean_object* v_res_3797_; 
v_i_boxed_3795_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_stop_boxed_3796_ = lean_unbox_usize(v_stop_3793_);
lean_dec(v_stop_3793_);
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3791_, v_i_boxed_3795_, v_stop_boxed_3796_, v_b_3794_);
lean_dec_ref(v_as_3791_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3798_, lean_object* v_x_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3798_, v_x_3799_);
lean_dec_ref(v_x_3798_);
return v_res_3800_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3802_, size_t v_x_3803_, size_t v_x_3804_, lean_object* v_x_3805_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 0)
{
lean_object* v_cs_3806_; lean_object* v___x_3807_; size_t v___x_3808_; lean_object* v_j_3809_; lean_object* v___x_3810_; size_t v___x_3811_; size_t v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_cs_3806_ = lean_ctor_get(v_x_3802_, 0);
v___x_3807_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3808_ = lean_usize_shift_right(v_x_3803_, v_x_3804_);
v_j_3809_ = lean_usize_to_nat(v___x_3808_);
v___x_3810_ = lean_array_get_borrowed(v___x_3807_, v_cs_3806_, v_j_3809_);
v___x_3811_ = ((size_t)1ULL);
v___x_3812_ = lean_usize_shift_left(v___x_3811_, v_x_3804_);
v___x_3813_ = lean_usize_sub(v___x_3812_, v___x_3811_);
v___x_3814_ = lean_usize_land(v_x_3803_, v___x_3813_);
v___x_3815_ = ((size_t)5ULL);
v___x_3816_ = lean_usize_sub(v_x_3804_, v___x_3815_);
v___x_3817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3810_, v___x_3814_, v___x_3816_, v_x_3805_);
v___x_3818_ = lean_unsigned_to_nat(1u);
v___x_3819_ = lean_nat_add(v_j_3809_, v___x_3818_);
lean_dec(v_j_3809_);
v___x_3820_ = lean_array_get_size(v_cs_3806_);
v___x_3821_ = lean_nat_dec_lt(v___x_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_dec(v___x_3819_);
return v___x_3817_;
}
else
{
size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_usize_of_nat(v___x_3819_);
lean_dec(v___x_3819_);
v___x_3823_ = lean_usize_of_nat(v___x_3820_);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3806_, v___x_3822_, v___x_3823_, v___x_3817_);
return v___x_3824_;
}
}
else
{
lean_object* v_vs_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_vs_3825_ = lean_ctor_get(v_x_3802_, 0);
v___x_3826_ = lean_usize_to_nat(v_x_3803_);
v___x_3827_ = lean_array_get_size(v_vs_3825_);
v___x_3828_ = lean_nat_dec_lt(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_dec(v___x_3826_);
return v_x_3805_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_usize_of_nat(v___x_3826_);
lean_dec(v___x_3826_);
v___x_3830_ = lean_usize_of_nat(v___x_3827_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3825_, v___x_3829_, v___x_3830_, v_x_3805_);
return v___x_3831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3832_, lean_object* v_x_3833_, lean_object* v_x_3834_, lean_object* v_x_3835_){
_start:
{
size_t v_x_1152__boxed_3836_; size_t v_x_1153__boxed_3837_; lean_object* v_res_3838_; 
v_x_1152__boxed_3836_ = lean_unbox_usize(v_x_3833_);
lean_dec(v_x_3833_);
v_x_1153__boxed_3837_ = lean_unbox_usize(v_x_3834_);
lean_dec(v_x_3834_);
v_res_3838_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3832_, v_x_1152__boxed_3836_, v_x_1153__boxed_3837_, v_x_3835_);
lean_dec_ref(v_x_3832_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3839_, lean_object* v_init_3840_, lean_object* v_start_3841_){
_start:
{
lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_nat_dec_eq(v_start_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v_root_3844_; lean_object* v_tail_3845_; size_t v_shift_3846_; lean_object* v_tailOff_3847_; uint8_t v___x_3848_; 
v_root_3844_ = lean_ctor_get(v_t_3839_, 0);
v_tail_3845_ = lean_ctor_get(v_t_3839_, 1);
v_shift_3846_ = lean_ctor_get_usize(v_t_3839_, 4);
v_tailOff_3847_ = lean_ctor_get(v_t_3839_, 3);
v___x_3848_ = lean_nat_dec_le(v_tailOff_3847_, v_start_3841_);
if (v___x_3848_ == 0)
{
size_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3849_ = lean_usize_of_nat(v_start_3841_);
v___x_3850_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3844_, v___x_3849_, v_shift_3846_, v_init_3840_);
v___x_3851_ = lean_array_get_size(v_tail_3845_);
v___x_3852_ = lean_nat_dec_lt(v___x_3842_, v___x_3851_);
if (v___x_3852_ == 0)
{
return v___x_3850_;
}
else
{
size_t v___x_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = ((size_t)0ULL);
v___x_3854_ = lean_usize_of_nat(v___x_3851_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3845_, v___x_3853_, v___x_3854_, v___x_3850_);
return v___x_3855_;
}
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = lean_nat_sub(v_start_3841_, v_tailOff_3847_);
v___x_3857_ = lean_array_get_size(v_tail_3845_);
v___x_3858_ = lean_nat_dec_lt(v___x_3856_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_dec(v___x_3856_);
return v_init_3840_;
}
else
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_usize_of_nat(v___x_3856_);
lean_dec(v___x_3856_);
v___x_3860_ = lean_usize_of_nat(v___x_3857_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3845_, v___x_3859_, v___x_3860_, v_init_3840_);
return v___x_3861_;
}
}
}
else
{
lean_object* v_root_3862_; lean_object* v_tail_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_root_3862_ = lean_ctor_get(v_t_3839_, 0);
v_tail_3863_ = lean_ctor_get(v_t_3839_, 1);
v___x_3864_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3862_, v_init_3840_);
v___x_3865_ = lean_array_get_size(v_tail_3863_);
v___x_3866_ = lean_nat_dec_lt(v___x_3842_, v___x_3865_);
if (v___x_3866_ == 0)
{
return v___x_3864_;
}
else
{
size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = ((size_t)0ULL);
v___x_3868_ = lean_usize_of_nat(v___x_3865_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3863_, v___x_3867_, v___x_3868_, v___x_3864_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3870_, lean_object* v_init_3871_, lean_object* v_start_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3870_, v_init_3871_, v_start_3872_);
lean_dec(v_start_3872_);
lean_dec_ref(v_t_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v_unreported_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3888_; 
v___x_3875_ = lean_unsigned_to_nat(32u);
v___x_3876_ = lean_mk_empty_array_with_capacity(v___x_3875_);
lean_dec_ref(v___x_3876_);
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3879_ = lean_ctor_get(v_log_3874_, 1);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_log_3874_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; lean_object* v_unused_3890_; 
v_unused_3889_ = lean_ctor_get(v_log_3874_, 2);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_log_3874_, 0);
lean_dec(v_unused_3890_);
v___x_3881_ = v_log_3874_;
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_unreported_3879_);
lean_dec(v_log_3874_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3883_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3879_, v___x_3878_, v___x_3877_);
lean_dec_ref(v_unreported_3879_);
v___x_3884_ = l_Lean_NameSet_empty;
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 2, v___x_3884_);
lean_ctor_set(v___x_3881_, 1, v___x_3883_);
lean_ctor_set(v___x_3881_, 0, v___x_3878_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3891_, size_t v_i_3892_, size_t v_stop_3893_, lean_object* v_b_3894_){
_start:
{
lean_object* v___y_3896_; uint8_t v___x_3900_; 
v___x_3900_ = lean_usize_dec_eq(v_i_3892_, v_stop_3893_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; uint8_t v_severity_3902_; 
v___x_3901_ = lean_array_uget_borrowed(v_as_3891_, v_i_3892_);
v_severity_3902_ = lean_ctor_get_uint8(v___x_3901_, sizeof(void*)*5 + 1);
if (v_severity_3902_ == 1)
{
lean_object* v___x_3903_; 
lean_inc(v___x_3901_);
v___x_3903_ = l_Lean_PersistentArray_push___redArg(v_b_3894_, v___x_3901_);
v___y_3896_ = v___x_3903_;
goto v___jp_3895_;
}
else
{
v___y_3896_ = v_b_3894_;
goto v___jp_3895_;
}
}
else
{
return v_b_3894_;
}
v___jp_3895_:
{
size_t v___x_3897_; size_t v___x_3898_; 
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_add(v_i_3892_, v___x_3897_);
v_i_3892_ = v___x_3898_;
v_b_3894_ = v___y_3896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3904_, lean_object* v_i_3905_, lean_object* v_stop_3906_, lean_object* v_b_3907_){
_start:
{
size_t v_i_boxed_3908_; size_t v_stop_boxed_3909_; lean_object* v_res_3910_; 
v_i_boxed_3908_ = lean_unbox_usize(v_i_3905_);
lean_dec(v_i_3905_);
v_stop_boxed_3909_ = lean_unbox_usize(v_stop_3906_);
lean_dec(v_stop_3906_);
v_res_3910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3904_, v_i_boxed_3908_, v_stop_boxed_3909_, v_b_3907_);
lean_dec_ref(v_as_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3911_, lean_object* v_x_3912_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_object* v_cs_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_cs_3913_ = lean_ctor_get(v_x_3911_, 0);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_array_get_size(v_cs_3913_);
v___x_3916_ = lean_nat_dec_lt(v___x_3914_, v___x_3915_);
if (v___x_3916_ == 0)
{
return v_x_3912_;
}
else
{
size_t v___x_3917_; size_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = lean_usize_of_nat(v___x_3915_);
v___x_3919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3913_, v___x_3917_, v___x_3918_, v_x_3912_);
return v___x_3919_;
}
}
else
{
lean_object* v_vs_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_vs_3920_ = lean_ctor_get(v_x_3911_, 0);
v___x_3921_ = lean_unsigned_to_nat(0u);
v___x_3922_ = lean_array_get_size(v_vs_3920_);
v___x_3923_ = lean_nat_dec_lt(v___x_3921_, v___x_3922_);
if (v___x_3923_ == 0)
{
return v_x_3912_;
}
else
{
size_t v___x_3924_; size_t v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = ((size_t)0ULL);
v___x_3925_ = lean_usize_of_nat(v___x_3922_);
v___x_3926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3920_, v___x_3924_, v___x_3925_, v_x_3912_);
return v___x_3926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3927_, size_t v_i_3928_, size_t v_stop_3929_, lean_object* v_b_3930_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_usize_dec_eq(v_i_3928_, v_stop_3929_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; size_t v___x_3934_; size_t v___x_3935_; 
v___x_3932_ = lean_array_uget_borrowed(v_as_3927_, v_i_3928_);
v___x_3933_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3932_, v_b_3930_);
v___x_3934_ = ((size_t)1ULL);
v___x_3935_ = lean_usize_add(v_i_3928_, v___x_3934_);
v_i_3928_ = v___x_3935_;
v_b_3930_ = v___x_3933_;
goto _start;
}
else
{
return v_b_3930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3937_, lean_object* v_i_3938_, lean_object* v_stop_3939_, lean_object* v_b_3940_){
_start:
{
size_t v_i_boxed_3941_; size_t v_stop_boxed_3942_; lean_object* v_res_3943_; 
v_i_boxed_3941_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_stop_boxed_3942_ = lean_unbox_usize(v_stop_3939_);
lean_dec(v_stop_3939_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3937_, v_i_boxed_3941_, v_stop_boxed_3942_, v_b_3940_);
lean_dec_ref(v_as_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3944_, lean_object* v_x_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3944_, v_x_3945_);
lean_dec_ref(v_x_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3947_, size_t v_x_3948_, size_t v_x_3949_, lean_object* v_x_3950_){
_start:
{
if (lean_obj_tag(v_x_3947_) == 0)
{
lean_object* v_cs_3951_; lean_object* v___x_3952_; size_t v___x_3953_; lean_object* v_j_3954_; lean_object* v___x_3955_; size_t v___x_3956_; size_t v___x_3957_; size_t v___x_3958_; size_t v___x_3959_; size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v_cs_3951_ = lean_ctor_get(v_x_3947_, 0);
v___x_3952_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3953_ = lean_usize_shift_right(v_x_3948_, v_x_3949_);
v_j_3954_ = lean_usize_to_nat(v___x_3953_);
v___x_3955_ = lean_array_get_borrowed(v___x_3952_, v_cs_3951_, v_j_3954_);
v___x_3956_ = ((size_t)1ULL);
v___x_3957_ = lean_usize_shift_left(v___x_3956_, v_x_3949_);
v___x_3958_ = lean_usize_sub(v___x_3957_, v___x_3956_);
v___x_3959_ = lean_usize_land(v_x_3948_, v___x_3958_);
v___x_3960_ = ((size_t)5ULL);
v___x_3961_ = lean_usize_sub(v_x_3949_, v___x_3960_);
v___x_3962_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3955_, v___x_3959_, v___x_3961_, v_x_3950_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_3964_ = lean_nat_add(v_j_3954_, v___x_3963_);
lean_dec(v_j_3954_);
v___x_3965_ = lean_array_get_size(v_cs_3951_);
v___x_3966_ = lean_nat_dec_lt(v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_dec(v___x_3964_);
return v___x_3962_;
}
else
{
size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_usize_of_nat(v___x_3964_);
lean_dec(v___x_3964_);
v___x_3968_ = lean_usize_of_nat(v___x_3965_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3951_, v___x_3967_, v___x_3968_, v___x_3962_);
return v___x_3969_;
}
}
else
{
lean_object* v_vs_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_vs_3970_ = lean_ctor_get(v_x_3947_, 0);
v___x_3971_ = lean_usize_to_nat(v_x_3948_);
v___x_3972_ = lean_array_get_size(v_vs_3970_);
v___x_3973_ = lean_nat_dec_lt(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_dec(v___x_3971_);
return v_x_3950_;
}
else
{
size_t v___x_3974_; size_t v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = lean_usize_of_nat(v___x_3971_);
lean_dec(v___x_3971_);
v___x_3975_ = lean_usize_of_nat(v___x_3972_);
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3970_, v___x_3974_, v___x_3975_, v_x_3950_);
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
size_t v_x_1151__boxed_3981_; size_t v_x_1152__boxed_3982_; lean_object* v_res_3983_; 
v_x_1151__boxed_3981_ = lean_unbox_usize(v_x_3978_);
lean_dec(v_x_3978_);
v_x_1152__boxed_3982_ = lean_unbox_usize(v_x_3979_);
lean_dec(v_x_3979_);
v_res_3983_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3977_, v_x_1151__boxed_3981_, v_x_1152__boxed_3982_, v_x_3980_);
lean_dec_ref(v_x_3977_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3984_, lean_object* v_init_3985_, lean_object* v_start_3986_){
_start:
{
lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = lean_nat_dec_eq(v_start_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v_root_3989_; lean_object* v_tail_3990_; size_t v_shift_3991_; lean_object* v_tailOff_3992_; uint8_t v___x_3993_; 
v_root_3989_ = lean_ctor_get(v_t_3984_, 0);
v_tail_3990_ = lean_ctor_get(v_t_3984_, 1);
v_shift_3991_ = lean_ctor_get_usize(v_t_3984_, 4);
v_tailOff_3992_ = lean_ctor_get(v_t_3984_, 3);
v___x_3993_ = lean_nat_dec_le(v_tailOff_3992_, v_start_3986_);
if (v___x_3993_ == 0)
{
size_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3994_ = lean_usize_of_nat(v_start_3986_);
v___x_3995_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3989_, v___x_3994_, v_shift_3991_, v_init_3985_);
v___x_3996_ = lean_array_get_size(v_tail_3990_);
v___x_3997_ = lean_nat_dec_lt(v___x_3987_, v___x_3996_);
if (v___x_3997_ == 0)
{
return v___x_3995_;
}
else
{
size_t v___x_3998_; size_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = ((size_t)0ULL);
v___x_3999_ = lean_usize_of_nat(v___x_3996_);
v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3990_, v___x_3998_, v___x_3999_, v___x_3995_);
return v___x_4000_;
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4001_ = lean_nat_sub(v_start_3986_, v_tailOff_3992_);
v___x_4002_ = lean_array_get_size(v_tail_3990_);
v___x_4003_ = lean_nat_dec_lt(v___x_4001_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_dec(v___x_4001_);
return v_init_3985_;
}
else
{
size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_usize_of_nat(v___x_4001_);
lean_dec(v___x_4001_);
v___x_4005_ = lean_usize_of_nat(v___x_4002_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3990_, v___x_4004_, v___x_4005_, v_init_3985_);
return v___x_4006_;
}
}
}
else
{
lean_object* v_root_4007_; lean_object* v_tail_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v_root_4007_ = lean_ctor_get(v_t_3984_, 0);
v_tail_4008_ = lean_ctor_get(v_t_3984_, 1);
v___x_4009_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_4007_, v_init_3985_);
v___x_4010_ = lean_array_get_size(v_tail_4008_);
v___x_4011_ = lean_nat_dec_lt(v___x_3987_, v___x_4010_);
if (v___x_4011_ == 0)
{
return v___x_4009_;
}
else
{
size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = ((size_t)0ULL);
v___x_4013_ = lean_usize_of_nat(v___x_4010_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4008_, v___x_4012_, v___x_4013_, v___x_4009_);
return v___x_4014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_4015_, lean_object* v_init_4016_, lean_object* v_start_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_4015_, v_init_4016_, v_start_4017_);
lean_dec(v_start_4017_);
lean_dec_ref(v_t_4015_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_4019_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v_unreported_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4033_; 
v___x_4020_ = lean_unsigned_to_nat(32u);
v___x_4021_ = lean_mk_empty_array_with_capacity(v___x_4020_);
lean_dec_ref(v___x_4021_);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_4024_ = lean_ctor_get(v_log_4019_, 1);
v_isSharedCheck_4033_ = !lean_is_exclusive(v_log_4019_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; lean_object* v_unused_4035_; 
v_unused_4034_ = lean_ctor_get(v_log_4019_, 2);
lean_dec(v_unused_4034_);
v_unused_4035_ = lean_ctor_get(v_log_4019_, 0);
lean_dec(v_unused_4035_);
v___x_4026_ = v_log_4019_;
v_isShared_4027_ = v_isSharedCheck_4033_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_unreported_4024_);
lean_dec(v_log_4019_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4033_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4028_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_4024_, v___x_4023_, v___x_4022_);
lean_dec_ref(v_unreported_4024_);
v___x_4029_ = l_Lean_NameSet_empty;
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 2, v___x_4029_);
lean_ctor_set(v___x_4026_, 1, v___x_4028_);
lean_ctor_set(v___x_4026_, 0, v___x_4023_);
v___x_4031_ = v___x_4026_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4032_, 2, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_4036_, lean_object* v_log_4037_, lean_object* v_f_4038_){
_start:
{
lean_object* v_unreported_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_unreported_4039_ = lean_ctor_get(v_log_4037_, 1);
lean_inc_ref(v_unreported_4039_);
lean_dec_ref(v_log_4037_);
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l_Lean_PersistentArray_forM___redArg(v_inst_4036_, v_unreported_4039_, v_f_4038_, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_4042_, lean_object* v_inst_4043_, lean_object* v_log_4044_, lean_object* v_f_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_MessageLog_forM___redArg(v_inst_4043_, v_log_4044_, v_f_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_4047_){
_start:
{
lean_object* v_unreported_4048_; lean_object* v___x_4049_; 
v_unreported_4048_ = lean_ctor_get(v_log_4047_, 1);
v___x_4049_ = l_Lean_PersistentArray_toList___redArg(v_unreported_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_MessageLog_toList(v_log_4050_);
lean_dec_ref(v_log_4050_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4052_){
_start:
{
lean_object* v_unreported_4053_; lean_object* v___x_4054_; 
v_unreported_4053_ = lean_ctor_get(v_log_4052_, 1);
v___x_4054_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_MessageLog_toArray(v_log_4055_);
lean_dec_ref(v_log_4055_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4057_){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = lean_unsigned_to_nat(2u);
v___x_4059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v_msg_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4060_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v_msg_4060_);
v___x_4063_ = l_Lean_MessageData_nestD(v___x_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4064_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = l_Lean_MessageData_ofExpr(v_e_4064_);
v___x_4066_ = l_Lean_indentD(v___x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4067_, lean_object* v_msg_4068_){
_start:
{
lean_object* v_env_4070_; lean_object* v_mctx_4071_; lean_object* v_lctx_4072_; lean_object* v_opts_4073_; lean_object* v_currNamespace_4074_; lean_object* v_openDecls_4075_; lean_object* v___x_4076_; lean_object* v_msg_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_env_4070_ = lean_ctor_get(v_ctx_4067_, 0);
v_mctx_4071_ = lean_ctor_get(v_ctx_4067_, 1);
v_lctx_4072_ = lean_ctor_get(v_ctx_4067_, 2);
v_opts_4073_ = lean_ctor_get(v_ctx_4067_, 3);
v_currNamespace_4074_ = lean_ctor_get(v_ctx_4067_, 4);
v_openDecls_4075_ = lean_ctor_get(v_ctx_4067_, 5);
lean_inc(v_openDecls_4075_);
lean_inc(v_currNamespace_4074_);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_currNamespace_4074_);
lean_ctor_set(v___x_4076_, 1, v_openDecls_4075_);
v_msg_4077_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4077_, 0, v___x_4076_);
lean_ctor_set(v_msg_4077_, 1, v_msg_4068_);
lean_inc_ref(v_opts_4073_);
lean_inc_ref(v_lctx_4072_);
lean_inc_ref(v_mctx_4071_);
lean_inc_ref(v_env_4070_);
v___x_4078_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4078_, 0, v_env_4070_);
lean_ctor_set(v___x_4078_, 1, v_mctx_4071_);
lean_ctor_set(v___x_4078_, 2, v_lctx_4072_);
lean_ctor_set(v___x_4078_, 3, v_opts_4073_);
v___x_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
v___x_4080_ = l_Lean_MessageData_format(v_msg_4077_, v___x_4079_);
v___x_4081_ = l_Std_Format_defWidth;
v___x_4082_ = lean_unsigned_to_nat(0u);
v___x_4083_ = l_Std_Format_pretty(v___x_4080_, v___x_4081_, v___x_4082_, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4084_, lean_object* v_msg_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4084_, v_msg_4085_);
lean_dec_ref(v_ctx_4084_);
return v_res_4087_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4088_, lean_object* v_a_4089_, uint8_t v_b_4090_){
_start:
{
lean_object* v_str_4091_; lean_object* v_startInclusive_4092_; lean_object* v_endExclusive_4093_; lean_object* v___x_4094_; uint8_t v_decide_4095_; 
v_str_4091_ = lean_ctor_get(v_s_4088_, 0);
v_startInclusive_4092_ = lean_ctor_get(v_s_4088_, 1);
v_endExclusive_4093_ = lean_ctor_get(v_s_4088_, 2);
v___x_4094_ = lean_nat_sub(v_endExclusive_4093_, v_startInclusive_4092_);
v_decide_4095_ = lean_nat_dec_eq(v_a_4089_, v___x_4094_);
lean_dec(v___x_4094_);
if (v_decide_4095_ == 0)
{
lean_object* v___x_4096_; uint32_t v___x_4097_; uint32_t v___x_4098_; uint8_t v___x_4099_; 
v___x_4096_ = lean_nat_add(v_startInclusive_4092_, v_a_4089_);
lean_dec(v_a_4089_);
v___x_4097_ = lean_string_utf8_get_fast(v_str_4091_, v___x_4096_);
v___x_4098_ = 10;
v___x_4099_ = lean_uint32_dec_eq(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = lean_string_utf8_next_fast(v_str_4091_, v___x_4096_);
lean_dec(v___x_4096_);
v___x_4101_ = lean_nat_sub(v___x_4100_, v_startInclusive_4092_);
v_a_4089_ = v___x_4101_;
v_b_4090_ = v___x_4099_;
goto _start;
}
else
{
lean_dec(v___x_4096_);
return v___x_4099_;
}
}
else
{
lean_dec(v_a_4089_);
return v_b_4090_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4103_, lean_object* v_a_4104_, lean_object* v_b_4105_){
_start:
{
uint8_t v_b_boxed_4106_; uint8_t v_res_4107_; lean_object* v_r_4108_; 
v_b_boxed_4106_ = lean_unbox(v_b_4105_);
v_res_4107_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4103_, v_a_4104_, v_b_boxed_4106_);
lean_dec_ref(v_s_4103_);
v_r_4108_ = lean_box(v_res_4107_);
return v_r_4108_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4109_){
_start:
{
lean_object* v_searcher_4110_; uint8_t v___x_4111_; uint8_t v___x_4112_; 
v_searcher_4110_ = lean_unsigned_to_nat(0u);
v___x_4111_ = 0;
v___x_4112_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4109_, v_searcher_4110_, v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4113_){
_start:
{
uint8_t v_res_4114_; lean_object* v_r_4115_; 
v_res_4114_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4113_);
lean_dec_ref(v_s_4113_);
v_r_4115_ = lean_box(v_res_4114_);
return v_r_4115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4116_, lean_object* v_val_4117_, lean_object* v_a_4118_, lean_object* v_b_4119_){
_start:
{
uint8_t v_decide_4120_; 
v_decide_4120_ = lean_nat_dec_eq(v_a_4118_, v___x_4116_);
if (v_decide_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4121_ = lean_string_utf8_next_fast(v_val_4117_, v_a_4118_);
lean_dec(v_a_4118_);
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_nat_add(v_b_4119_, v___x_4122_);
lean_dec(v_b_4119_);
v_a_4118_ = v___x_4121_;
v_b_4119_ = v___x_4123_;
goto _start;
}
else
{
lean_dec(v_a_4118_);
return v_b_4119_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4125_, lean_object* v_val_4126_, lean_object* v_a_4127_, lean_object* v_b_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4125_, v_val_4126_, v_a_4127_, v_b_4128_);
lean_dec_ref(v_val_4126_);
lean_dec(v___x_4125_);
return v_res_4129_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4131_ = l_Lean_MessageData_ofFormat(v___x_4130_);
return v___x_4131_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_4136_ = l_Lean_MessageData_ofFormat(v___x_4135_);
return v___x_4136_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_4141_ = l_Lean_MessageData_ofFormat(v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4142_, lean_object* v_maxInlineLength_4143_, lean_object* v_ctx_4144_){
_start:
{
lean_object* v_msg_4146_; lean_object* v___x_4147_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v_msg_4146_ = l_Lean_MessageData_ofExpr(v_e_4142_);
lean_inc_ref(v_msg_4146_);
v___x_4147_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4144_, v_msg_4146_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_string_utf8_byte_size(v___x_4147_);
lean_inc_ref(v___x_4147_);
v___x_4154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4147_);
lean_ctor_set(v___x_4154_, 1, v___x_4152_);
lean_ctor_set(v___x_4154_, 2, v___x_4153_);
v___x_4155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4153_, v___x_4147_, v___x_4152_, v___x_4152_);
lean_dec_ref(v___x_4147_);
v___x_4156_ = lean_nat_dec_lt(v_maxInlineLength_4143_, v___x_4155_);
lean_dec(v___x_4155_);
if (v___x_4156_ == 0)
{
uint8_t v___x_4157_; 
v___x_4157_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4154_);
lean_dec_ref_known(v___x_4154_, 3);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4158_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v_msg_4146_);
v___x_4160_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
return v___x_4161_;
}
else
{
goto v___jp_4148_;
}
}
else
{
lean_dec_ref_known(v___x_4154_, 3);
goto v___jp_4148_;
}
v___jp_4148_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = l_Lean_indentD(v_msg_4146_);
v___x_4150_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
return v___x_4151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4162_, lean_object* v_maxInlineLength_4163_, lean_object* v_ctx_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_inlineExpr___lam__0(v_e_4162_, v_maxInlineLength_4163_, v_ctx_4164_);
lean_dec_ref(v_ctx_4164_);
lean_dec(v_maxInlineLength_4163_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4167_, lean_object* v_x_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4170_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4171_ = l_Lean_MessageData_ofExpr(v_e_4167_);
v___x_4172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4170_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4175_, lean_object* v_x_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_inlineExpr___lam__2(v_e_4175_, v_x_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4179_, lean_object* v_maxInlineLength_4180_){
_start:
{
lean_object* v___f_4181_; lean_object* v___f_4182_; lean_object* v___f_4183_; lean_object* v___x_4184_; 
lean_inc_ref_n(v_e_4179_, 2);
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4181_, 0, v_e_4179_);
lean_closure_set(v___f_4181_, 1, v_maxInlineLength_4180_);
v___f_4182_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4182_, 0, v_e_4179_);
v___f_4183_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4183_, 0, v_e_4179_);
v___x_4184_ = l_Lean_MessageData_lazy(v___f_4181_, v___f_4182_, v___f_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v_val_4187_, lean_object* v_inst_4188_, lean_object* v_R_4189_, lean_object* v_a_4190_, lean_object* v_b_4191_, lean_object* v_c_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4185_, v_val_4187_, v_a_4190_, v_b_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4194_, lean_object* v___x_4195_, lean_object* v_val_4196_, lean_object* v_inst_4197_, lean_object* v_R_4198_, lean_object* v_a_4199_, lean_object* v_b_4200_, lean_object* v_c_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4194_, v___x_4195_, v_val_4196_, v_inst_4197_, v_R_4198_, v_a_4199_, v_b_4200_, v_c_4201_);
lean_dec_ref(v_val_4196_);
lean_dec_ref(v___x_4195_);
lean_dec(v___x_4194_);
return v_res_4202_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4203_, lean_object* v_inst_4204_, lean_object* v_R_4205_, lean_object* v_a_4206_, uint8_t v_b_4207_, lean_object* v_c_4208_){
_start:
{
uint8_t v___x_4209_; 
v___x_4209_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4203_, v_a_4206_, v_b_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4210_, lean_object* v_inst_4211_, lean_object* v_R_4212_, lean_object* v_a_4213_, lean_object* v_b_4214_, lean_object* v_c_4215_){
_start:
{
uint8_t v_b_boxed_4216_; uint8_t v_res_4217_; lean_object* v_r_4218_; 
v_b_boxed_4216_ = lean_unbox(v_b_4214_);
v_res_4217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4210_, v_inst_4211_, v_R_4212_, v_a_4213_, v_b_boxed_4216_, v_c_4215_);
lean_dec_ref(v_s_4210_);
v_r_4218_ = lean_box(v_res_4217_);
return v_r_4218_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4223_ = l_Lean_MessageData_ofFormat(v___x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4224_, lean_object* v_maxInlineLength_4225_, lean_object* v_ctx_4226_){
_start:
{
lean_object* v_msg_4228_; lean_object* v___x_4229_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; 
v_msg_4228_ = l_Lean_MessageData_ofExpr(v_e_4224_);
lean_inc_ref(v_msg_4228_);
v___x_4229_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4226_, v_msg_4228_);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_string_utf8_byte_size(v___x_4229_);
lean_inc_ref(v___x_4229_);
v___x_4234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4229_);
lean_ctor_set(v___x_4234_, 1, v___x_4232_);
lean_ctor_set(v___x_4234_, 2, v___x_4233_);
v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4233_, v___x_4229_, v___x_4232_, v___x_4232_);
lean_dec_ref(v___x_4229_);
v___x_4236_ = lean_nat_dec_lt(v_maxInlineLength_4225_, v___x_4235_);
lean_dec(v___x_4235_);
if (v___x_4236_ == 0)
{
uint8_t v___x_4237_; 
v___x_4237_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4234_);
lean_dec_ref_known(v___x_4234_, 3);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4238_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
lean_ctor_set(v___x_4239_, 1, v_msg_4228_);
v___x_4240_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4239_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
return v___x_4241_;
}
else
{
goto v___jp_4230_;
}
}
else
{
lean_dec_ref_known(v___x_4234_, 3);
goto v___jp_4230_;
}
v___jp_4230_:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_indentD(v_msg_4228_);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4242_, lean_object* v_maxInlineLength_4243_, lean_object* v_ctx_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_inlineExprTrailing___lam__0(v_e_4242_, v_maxInlineLength_4243_, v_ctx_4244_);
lean_dec_ref(v_ctx_4244_);
lean_dec(v_maxInlineLength_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4247_, lean_object* v_x_4248_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4250_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4251_ = l_Lean_MessageData_ofExpr(v_e_4247_);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4255_, lean_object* v_x_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_inlineExprTrailing___lam__2(v_e_4255_, v_x_4256_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4259_, lean_object* v_maxInlineLength_4260_){
_start:
{
lean_object* v___f_4261_; lean_object* v___f_4262_; lean_object* v___f_4263_; lean_object* v___x_4264_; 
lean_inc_ref_n(v_e_4259_, 2);
v___f_4261_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4261_, 0, v_e_4259_);
lean_closure_set(v___f_4261_, 1, v_maxInlineLength_4260_);
v___f_4262_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4262_, 0, v_e_4259_);
v___f_4263_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4263_, 0, v_e_4259_);
v___x_4264_ = l_Lean_MessageData_lazy(v___f_4261_, v___f_4262_, v___f_4263_);
return v___x_4264_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4269_ = l_Lean_MessageData_ofFormat(v___x_4268_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4274_ = l_Lean_MessageData_ofFormat(v___x_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4275_){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4276_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
lean_ctor_set(v___x_4277_, 1, v_msg_4275_);
v___x_4278_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_msg_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_apply_1(v_inst_4280_, v_msg_4282_);
v___x_4284_ = lean_apply_2(v_inst_4281_, lean_box(0), v___x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4285_, lean_object* v_inst_4286_){
_start:
{
lean_object* v___f_4287_; 
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4287_, 0, v_inst_4286_);
lean_closure_set(v___f_4287_, 1, v_inst_4285_);
return v___f_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4288_, lean_object* v_n_4289_, lean_object* v_inst_4290_, lean_object* v_inst_4291_){
_start:
{
lean_object* v___f_4292_; 
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4292_, 0, v_inst_4291_);
lean_closure_set(v___f_4292_, 1, v_inst_4290_);
return v___f_4292_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = lean_unsigned_to_nat(32u);
v___x_4294_ = lean_mk_empty_array_with_capacity(v___x_4293_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
return v___x_4295_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4296_ = ((size_t)5ULL);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_unsigned_to_nat(32u);
v___x_4299_ = lean_mk_empty_array_with_capacity(v___x_4298_);
v___x_4300_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4301_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v___x_4299_);
lean_ctor_set(v___x_4301_, 2, v___x_4297_);
lean_ctor_set(v___x_4301_, 3, v___x_4297_);
lean_ctor_set_usize(v___x_4301_, 4, v___x_4296_);
return v___x_4301_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4302_ = lean_box(1);
v___x_4303_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4304_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
lean_ctor_set(v___x_4305_, 1, v___x_4303_);
lean_ctor_set(v___x_4305_, 2, v___x_4302_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4306_, lean_object* v_msgData_4307_, lean_object* v_toPure_4308_, lean_object* v_opts_4309_){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4310_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4311_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4312_, 0, v_env_4306_);
lean_ctor_set(v___x_4312_, 1, v___x_4310_);
lean_ctor_set(v___x_4312_, 2, v___x_4311_);
lean_ctor_set(v___x_4312_, 3, v_opts_4309_);
v___x_4313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
lean_ctor_set(v___x_4313_, 1, v_msgData_4307_);
v___x_4314_ = lean_apply_2(v_toPure_4308_, lean_box(0), v___x_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4315_, lean_object* v_toPure_4316_, lean_object* v_toBind_4317_, lean_object* v_inst_4318_, lean_object* v_env_4319_){
_start:
{
lean_object* v___f_4320_; lean_object* v___x_4321_; 
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4320_, 0, v_env_4319_);
lean_closure_set(v___f_4320_, 1, v_msgData_4315_);
lean_closure_set(v___f_4320_, 2, v_toPure_4316_);
v___x_4321_ = lean_apply_4(v_toBind_4317_, lean_box(0), lean_box(0), v_inst_4318_, v___f_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4322_, lean_object* v_inst_4323_, lean_object* v_inst_4324_, lean_object* v_msgData_4325_){
_start:
{
lean_object* v_toApplicative_4326_; lean_object* v_toBind_4327_; lean_object* v_getEnv_4328_; lean_object* v_toPure_4329_; lean_object* v___f_4330_; lean_object* v___x_4331_; 
v_toApplicative_4326_ = lean_ctor_get(v_inst_4322_, 0);
lean_inc_ref(v_toApplicative_4326_);
v_toBind_4327_ = lean_ctor_get(v_inst_4322_, 1);
lean_inc_n(v_toBind_4327_, 2);
lean_dec_ref(v_inst_4322_);
v_getEnv_4328_ = lean_ctor_get(v_inst_4323_, 0);
lean_inc(v_getEnv_4328_);
lean_dec_ref(v_inst_4323_);
v_toPure_4329_ = lean_ctor_get(v_toApplicative_4326_, 1);
lean_inc(v_toPure_4329_);
lean_dec_ref(v_toApplicative_4326_);
v___f_4330_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4330_, 0, v_msgData_4325_);
lean_closure_set(v___f_4330_, 1, v_toPure_4329_);
lean_closure_set(v___f_4330_, 2, v_toBind_4327_);
lean_closure_set(v___f_4330_, 3, v_inst_4324_);
v___x_4331_ = lean_apply_4(v_toBind_4327_, lean_box(0), lean_box(0), v_getEnv_4328_, v___f_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4332_, lean_object* v_inst_4333_, lean_object* v_inst_4334_, lean_object* v_inst_4335_, lean_object* v_msgData_4336_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Lean_addMessageContextPartial___redArg(v_inst_4333_, v_inst_4334_, v_inst_4335_, v_msgData_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4338_, lean_object* v_mctx_4339_, lean_object* v_lctx_4340_, lean_object* v_msgData_4341_, lean_object* v_toPure_4342_, lean_object* v_opts_4343_){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4344_, 0, v_env_4338_);
lean_ctor_set(v___x_4344_, 1, v_mctx_4339_);
lean_ctor_set(v___x_4344_, 2, v_lctx_4340_);
lean_ctor_set(v___x_4344_, 3, v_opts_4343_);
v___x_4345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v_msgData_4341_);
v___x_4346_ = lean_apply_2(v_toPure_4342_, lean_box(0), v___x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4347_, lean_object* v_mctx_4348_, lean_object* v_msgData_4349_, lean_object* v_toPure_4350_, lean_object* v_toBind_4351_, lean_object* v_inst_4352_, lean_object* v_lctx_4353_){
_start:
{
lean_object* v___f_4354_; lean_object* v___x_4355_; 
v___f_4354_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4354_, 0, v_env_4347_);
lean_closure_set(v___f_4354_, 1, v_mctx_4348_);
lean_closure_set(v___f_4354_, 2, v_lctx_4353_);
lean_closure_set(v___f_4354_, 3, v_msgData_4349_);
lean_closure_set(v___f_4354_, 4, v_toPure_4350_);
v___x_4355_ = lean_apply_4(v_toBind_4351_, lean_box(0), lean_box(0), v_inst_4352_, v___f_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4356_, lean_object* v_msgData_4357_, lean_object* v_toPure_4358_, lean_object* v_toBind_4359_, lean_object* v_inst_4360_, lean_object* v_inst_4361_, lean_object* v_mctx_4362_){
_start:
{
lean_object* v___f_4363_; lean_object* v___x_4364_; 
lean_inc(v_toBind_4359_);
v___f_4363_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4363_, 0, v_env_4356_);
lean_closure_set(v___f_4363_, 1, v_mctx_4362_);
lean_closure_set(v___f_4363_, 2, v_msgData_4357_);
lean_closure_set(v___f_4363_, 3, v_toPure_4358_);
lean_closure_set(v___f_4363_, 4, v_toBind_4359_);
lean_closure_set(v___f_4363_, 5, v_inst_4360_);
v___x_4364_ = lean_apply_4(v_toBind_4359_, lean_box(0), lean_box(0), v_inst_4361_, v___f_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4365_, lean_object* v_msgData_4366_, lean_object* v_toPure_4367_, lean_object* v_toBind_4368_, lean_object* v_inst_4369_, lean_object* v_inst_4370_, lean_object* v_env_4371_){
_start:
{
lean_object* v_getMCtx_4372_; lean_object* v___f_4373_; lean_object* v___x_4374_; 
v_getMCtx_4372_ = lean_ctor_get(v_inst_4365_, 0);
lean_inc(v_getMCtx_4372_);
lean_dec_ref(v_inst_4365_);
lean_inc(v_toBind_4368_);
v___f_4373_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4373_, 0, v_env_4371_);
lean_closure_set(v___f_4373_, 1, v_msgData_4366_);
lean_closure_set(v___f_4373_, 2, v_toPure_4367_);
lean_closure_set(v___f_4373_, 3, v_toBind_4368_);
lean_closure_set(v___f_4373_, 4, v_inst_4369_);
lean_closure_set(v___f_4373_, 5, v_inst_4370_);
v___x_4374_ = lean_apply_4(v_toBind_4368_, lean_box(0), lean_box(0), v_getMCtx_4372_, v___f_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4375_, lean_object* v_inst_4376_, lean_object* v_inst_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_, lean_object* v_msgData_4380_){
_start:
{
lean_object* v_toApplicative_4381_; lean_object* v_toBind_4382_; lean_object* v_getEnv_4383_; lean_object* v_toPure_4384_; lean_object* v___f_4385_; lean_object* v___x_4386_; 
v_toApplicative_4381_ = lean_ctor_get(v_inst_4375_, 0);
lean_inc_ref(v_toApplicative_4381_);
v_toBind_4382_ = lean_ctor_get(v_inst_4375_, 1);
lean_inc_n(v_toBind_4382_, 2);
lean_dec_ref(v_inst_4375_);
v_getEnv_4383_ = lean_ctor_get(v_inst_4376_, 0);
lean_inc(v_getEnv_4383_);
lean_dec_ref(v_inst_4376_);
v_toPure_4384_ = lean_ctor_get(v_toApplicative_4381_, 1);
lean_inc(v_toPure_4384_);
lean_dec_ref(v_toApplicative_4381_);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4385_, 0, v_inst_4377_);
lean_closure_set(v___f_4385_, 1, v_msgData_4380_);
lean_closure_set(v___f_4385_, 2, v_toPure_4384_);
lean_closure_set(v___f_4385_, 3, v_toBind_4382_);
lean_closure_set(v___f_4385_, 4, v_inst_4379_);
lean_closure_set(v___f_4385_, 5, v_inst_4378_);
v___x_4386_ = lean_apply_4(v_toBind_4382_, lean_box(0), lean_box(0), v_getEnv_4383_, v___f_4385_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4387_, lean_object* v_inst_4388_, lean_object* v_inst_4389_, lean_object* v_inst_4390_, lean_object* v_inst_4391_, lean_object* v_inst_4392_, lean_object* v_msgData_4393_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_addMessageContextFull___redArg(v_inst_4388_, v_inst_4389_, v_inst_4390_, v_inst_4391_, v_inst_4392_, v_msgData_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4399_);
lean_dec_ref(v_s_4399_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4401_, lean_object* v___x_4402_, lean_object* v___x_4403_, lean_object* v_a_4404_, lean_object* v_b_4405_){
_start:
{
lean_object* v_it_4407_; lean_object* v_startInclusive_4408_; lean_object* v_endExclusive_4409_; 
if (lean_obj_tag(v_a_4404_) == 0)
{
lean_object* v_currPos_4415_; lean_object* v_searcher_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4439_; 
v_currPos_4415_ = lean_ctor_get(v_a_4404_, 0);
v_searcher_4416_ = lean_ctor_get(v_a_4404_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_a_4404_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4418_ = v_a_4404_;
v_isShared_4419_ = v_isSharedCheck_4439_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_searcher_4416_);
lean_inc(v_currPos_4415_);
lean_dec(v_a_4404_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4439_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
uint8_t v_decide_4420_; 
v_decide_4420_ = lean_nat_dec_eq(v_searcher_4416_, v___x_4403_);
if (v_decide_4420_ == 0)
{
uint32_t v___x_4421_; uint32_t v___x_4422_; uint8_t v___x_4423_; 
v___x_4421_ = 10;
v___x_4422_ = lean_string_utf8_get_fast(v_str_4401_, v_searcher_4416_);
v___x_4423_ = lean_uint32_dec_eq(v___x_4422_, v___x_4421_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = lean_string_utf8_next_fast(v_str_4401_, v_searcher_4416_);
lean_dec(v_searcher_4416_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 1, v___x_4424_);
v___x_4426_ = v___x_4418_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_currPos_4415_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
v_a_4404_ = v___x_4426_;
goto _start;
}
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v_slice_4432_; lean_object* v_nextIt_4434_; 
v___x_4429_ = lean_string_utf8_next_fast(v_str_4401_, v_searcher_4416_);
v___x_4430_ = lean_nat_sub(v___x_4429_, v_searcher_4416_);
v___x_4431_ = lean_nat_add(v_searcher_4416_, v___x_4430_);
lean_dec(v___x_4430_);
v_slice_4432_ = l_String_Slice_subslice_x21(v___x_4402_, v_currPos_4415_, v_searcher_4416_);
lean_inc(v___x_4431_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 1, v___x_4431_);
lean_ctor_set(v___x_4418_, 0, v___x_4431_);
v_nextIt_4434_ = v___x_4418_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4437_, 1, v___x_4431_);
v_nextIt_4434_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v_startInclusive_4435_; lean_object* v_endExclusive_4436_; 
v_startInclusive_4435_ = lean_ctor_get(v_slice_4432_, 0);
lean_inc(v_startInclusive_4435_);
v_endExclusive_4436_ = lean_ctor_get(v_slice_4432_, 1);
lean_inc(v_endExclusive_4436_);
lean_dec_ref(v_slice_4432_);
v_it_4407_ = v_nextIt_4434_;
v_startInclusive_4408_ = v_startInclusive_4435_;
v_endExclusive_4409_ = v_endExclusive_4436_;
goto v___jp_4406_;
}
}
}
else
{
lean_object* v___x_4438_; 
lean_del_object(v___x_4418_);
lean_dec(v_searcher_4416_);
v___x_4438_ = lean_box(1);
lean_inc(v___x_4403_);
v_it_4407_ = v___x_4438_;
v_startInclusive_4408_ = v_currPos_4415_;
v_endExclusive_4409_ = v___x_4403_;
goto v___jp_4406_;
}
}
}
else
{
lean_dec(v___x_4403_);
return v_b_4405_;
}
v___jp_4406_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4410_ = lean_string_utf8_extract_fast(v_str_4401_, v_startInclusive_4408_, v_endExclusive_4409_);
lean_dec(v_endExclusive_4409_);
lean_dec(v_startInclusive_4408_);
v___x_4411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
v___x_4412_ = l_Lean_MessageData_ofFormat(v___x_4411_);
v___x_4413_ = lean_array_push(v_b_4405_, v___x_4412_);
v_a_4404_ = v_it_4407_;
v_b_4405_ = v___x_4413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4440_, lean_object* v___x_4441_, lean_object* v___x_4442_, lean_object* v_a_4443_, lean_object* v_b_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4440_, v___x_4441_, v___x_4442_, v_a_4443_, v_b_4444_);
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_str_4440_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4448_){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v_lines_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = lean_string_utf8_byte_size(v_str_4448_);
lean_inc_ref(v_str_4448_);
v___x_4451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4451_, 0, v_str_4448_);
lean_ctor_set(v___x_4451_, 1, v___x_4449_);
lean_ctor_set(v___x_4451_, 2, v___x_4450_);
v_lines_4452_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4451_);
v___x_4453_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4448_, v___x_4451_, v___x_4450_, v_lines_4452_, v___x_4453_);
lean_dec_ref_known(v___x_4451_, 3);
lean_dec_ref(v_str_4448_);
v___x_4455_ = lean_array_to_list(v___x_4454_);
v___x_4456_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4457_ = l_Lean_MessageData_joinSep(v___x_4455_, v___x_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4458_, lean_object* v___x_4459_, lean_object* v___x_4460_, lean_object* v_inst_4461_, lean_object* v_R_4462_, lean_object* v_a_4463_, lean_object* v_b_4464_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4458_, v___x_4459_, v___x_4460_, v_a_4463_, v_b_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4466_, lean_object* v___x_4467_, lean_object* v___x_4468_, lean_object* v_inst_4469_, lean_object* v_R_4470_, lean_object* v_a_4471_, lean_object* v_b_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4466_, v___x_4467_, v___x_4468_, v_inst_4469_, v_R_4470_, v_a_4471_, v_b_4472_);
lean_dec_ref(v___x_4467_);
lean_dec_ref(v_str_4466_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4474_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4476_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4476_, 0, lean_box(0));
lean_closure_set(v___x_4476_, 1, lean_box(0));
lean_closure_set(v___x_4476_, 2, lean_box(0));
lean_closure_set(v___x_4476_, 3, v___x_4475_);
lean_closure_set(v___x_4476_, 4, v_inst_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4477_, lean_object* v_inst_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4486_){
_start:
{
lean_object* v___f_4487_; 
v___f_4487_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_instToMessageDataTSyntax(v_k_4488_);
lean_dec(v_k_4488_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4494_, lean_object* v_as_4495_){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_box(0);
v___x_4497_ = l_List_mapTR_loop___redArg(v_inst_4494_, v_as_4495_, v___x_4496_);
v___x_4498_ = l_Lean_MessageData_ofList(v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4499_){
_start:
{
lean_object* v___f_4500_; 
v___f_4500_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4500_, 0, v_inst_4499_);
return v___f_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4501_, lean_object* v_inst_4502_){
_start:
{
lean_object* v___f_4503_; 
v___f_4503_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4503_, 0, v_inst_4502_);
return v___f_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4504_, lean_object* v_as_4505_){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4506_ = lean_array_to_list(v_as_4505_);
v___x_4507_ = lean_box(0);
v___x_4508_ = l_List_mapTR_loop___redArg(v_inst_4504_, v___x_4506_, v___x_4507_);
v___x_4509_ = l_Lean_MessageData_ofList(v___x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4510_){
_start:
{
lean_object* v___f_4511_; 
v___f_4511_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4511_, 0, v_inst_4510_);
return v___f_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4512_, lean_object* v_inst_4513_){
_start:
{
lean_object* v___f_4514_; 
v___f_4514_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4514_, 0, v_inst_4513_);
return v___f_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4515_, lean_object* v_acc_4516_, lean_object* v_recur_4517_){
_start:
{
lean_object* v_array_4518_; lean_object* v_start_4519_; lean_object* v_stop_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4533_; 
v_array_4518_ = lean_ctor_get(v_it_4515_, 0);
v_start_4519_ = lean_ctor_get(v_it_4515_, 1);
v_stop_4520_ = lean_ctor_get(v_it_4515_, 2);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_it_4515_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4522_ = v_it_4515_;
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_stop_4520_);
lean_inc(v_start_4519_);
lean_inc(v_array_4518_);
lean_dec(v_it_4515_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
uint8_t v___x_4524_; 
v___x_4524_ = lean_nat_dec_lt(v_start_4519_, v_stop_4520_);
if (v___x_4524_ == 0)
{
lean_del_object(v___x_4522_);
lean_dec(v_stop_4520_);
lean_dec(v_start_4519_);
lean_dec_ref(v_array_4518_);
lean_dec_ref(v_recur_4517_);
return v_acc_4516_;
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4528_; 
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = lean_nat_add(v_start_4519_, v___x_4525_);
lean_inc_ref(v_array_4518_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 1, v___x_4526_);
v___x_4528_ = v___x_4522_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_array_4518_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4526_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_stop_4520_);
v___x_4528_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = lean_array_fget(v_array_4518_, v_start_4519_);
lean_dec(v_start_4519_);
lean_dec_ref(v_array_4518_);
v___x_4530_ = lean_array_push(v_acc_4516_, v___x_4529_);
v___x_4531_ = lean_apply_3(v_recur_4517_, v___x_4528_, v___x_4530_, lean_box(0));
return v___x_4531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4536_, lean_object* v_inst_4537_, lean_object* v_as_4538_){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4539_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4540_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4536_, v_as_4538_, v___x_4539_);
v___x_4541_ = lean_array_to_list(v___x_4540_);
v___x_4542_ = lean_box(0);
v___x_4543_ = l_List_mapTR_loop___redArg(v_inst_4537_, v___x_4541_, v___x_4542_);
v___x_4544_ = l_Lean_MessageData_ofList(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4546_){
_start:
{
lean_object* v___f_4547_; lean_object* v___f_4548_; 
v___f_4547_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4548_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4548_, 0, v___f_4547_);
lean_closure_set(v___f_4548_, 1, v_inst_4546_);
return v___f_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4549_, lean_object* v_inst_4550_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4550_);
return v___x_4551_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4556_ = l_Lean_MessageData_ofFormat(v___x_4555_);
return v___x_4556_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4560_ = l_Lean_MessageData_ofFormat(v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4561_, lean_object* v_x_4562_){
_start:
{
if (lean_obj_tag(v_x_4562_) == 0)
{
lean_object* v___x_4563_; 
lean_dec_ref(v_inst_4561_);
v___x_4563_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4563_;
}
else
{
lean_object* v_val_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_val_4564_ = lean_ctor_get(v_x_4562_, 0);
lean_inc(v_val_4564_);
lean_dec_ref_known(v_x_4562_, 1);
v___x_4565_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4566_ = lean_apply_1(v_inst_4561_, v_val_4564_);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4567_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
return v___x_4569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4570_){
_start:
{
lean_object* v___f_4571_; 
v___f_4571_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4571_, 0, v_inst_4570_);
return v___f_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4572_, lean_object* v_inst_4573_){
_start:
{
lean_object* v___f_4574_; 
v___f_4574_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4574_, 0, v_inst_4573_);
return v___f_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4575_, lean_object* v_inst_4576_, lean_object* v_x_4577_){
_start:
{
lean_object* v_fst_4578_; lean_object* v_snd_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4593_; 
v_fst_4578_ = lean_ctor_get(v_x_4577_, 0);
v_snd_4579_ = lean_ctor_get(v_x_4577_, 1);
v_isSharedCheck_4593_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4581_ = v_x_4577_;
v_isShared_4582_ = v_isSharedCheck_4593_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_snd_4579_);
lean_inc(v_fst_4578_);
lean_dec(v_x_4577_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4593_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4586_; 
v___x_4583_ = lean_apply_1(v_inst_4575_, v_fst_4578_);
v___x_4584_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 7);
lean_ctor_set(v___x_4581_, 1, v___x_4584_);
lean_ctor_set(v___x_4581_, 0, v___x_4583_);
v___x_4586_ = v___x_4581_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v___x_4584_);
v___x_4586_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4587_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = lean_apply_1(v_inst_4576_, v_snd_4579_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4588_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = l_Lean_MessageData_paren(v___x_4590_);
return v___x_4591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4594_, lean_object* v_inst_4595_){
_start:
{
lean_object* v___f_4596_; 
v___f_4596_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4596_, 0, v_inst_4594_);
lean_closure_set(v___f_4596_, 1, v_inst_4595_);
return v___f_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4597_, lean_object* v_00_u03b2_4598_, lean_object* v_inst_4599_, lean_object* v_inst_4600_){
_start:
{
lean_object* v___f_4601_; 
v___f_4601_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4601_, 0, v_inst_4599_);
lean_closure_set(v___f_4601_, 1, v_inst_4600_);
return v___f_4601_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4606_ = l_Lean_MessageData_ofFormat(v___x_4605_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4607_){
_start:
{
if (lean_obj_tag(v_x_4607_) == 0)
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4608_;
}
else
{
lean_object* v_val_4609_; lean_object* v___x_4610_; 
v_val_4609_ = lean_ctor_get(v_x_4607_, 0);
lean_inc(v_val_4609_);
lean_dec_ref_known(v_x_4607_, 1);
v___x_4610_ = l_Lean_MessageData_ofExpr(v_val_4609_);
return v___x_4610_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_4645_ = l_String_toRawSubstring_x27(v___x_4644_);
return v___x_4645_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4661_ = l_String_toRawSubstring_x27(v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v___x_4678_; uint8_t v___x_4679_; 
v___x_4678_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4675_);
v___x_4679_ = l_Lean_Syntax_isOfKind(v_x_4675_, v___x_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_dec(v_x_4675_);
v___x_4680_ = lean_box(1);
v___x_4681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
lean_ctor_set(v___x_4681_, 1, v_a_4677_);
return v___x_4681_;
}
else
{
lean_object* v_quotContext_4682_; lean_object* v_currMacroScope_4683_; lean_object* v_ref_4684_; lean_object* v___x_4685_; lean_object* v_interpStr_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_quotContext_4682_ = lean_ctor_get(v_a_4676_, 1);
v_currMacroScope_4683_ = lean_ctor_get(v_a_4676_, 2);
v_ref_4684_ = lean_ctor_get(v_a_4676_, 5);
v___x_4685_ = lean_unsigned_to_nat(1u);
v_interpStr_4686_ = l_Lean_Syntax_getArg(v_x_4675_, v___x_4685_);
lean_dec(v_x_4675_);
v___x_4687_ = 0;
v___x_4688_ = l_Lean_SourceInfo_fromRef(v_ref_4684_, v___x_4687_);
v___x_4689_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4690_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4683_, 2);
lean_inc_n(v_quotContext_4682_, 2);
v___x_4691_ = l_Lean_addMacroScope(v_quotContext_4682_, v___x_4690_, v_currMacroScope_4683_);
v___x_4692_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4688_);
v___x_4693_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4688_);
lean_ctor_set(v___x_4693_, 1, v___x_4689_);
lean_ctor_set(v___x_4693_, 2, v___x_4691_);
lean_ctor_set(v___x_4693_, 3, v___x_4692_);
v___x_4694_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4695_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4696_ = l_Lean_addMacroScope(v_quotContext_4682_, v___x_4695_, v_currMacroScope_4683_);
v___x_4697_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4688_);
lean_ctor_set(v___x_4698_, 1, v___x_4694_);
lean_ctor_set(v___x_4698_, 2, v___x_4696_);
lean_ctor_set(v___x_4698_, 3, v___x_4697_);
lean_inc_ref(v___x_4698_);
v___x_4699_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4686_, v___x_4693_, v___x_4698_, v___x_4698_, v_a_4676_, v_a_4677_);
lean_dec(v_interpStr_4686_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_a_4701_ = lean_ctor_get(v___x_4699_, 1);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4699_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4700_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
v_a_4709_ = lean_ctor_get(v___x_4699_, 0);
v_a_4710_ = lean_ctor_get(v___x_4699_, 1);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4699_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_inc(v_a_4709_);
lean_dec(v___x_4699_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4709_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4718_, v_a_4719_, v_a_4720_);
lean_dec_ref(v_a_4719_);
return v_res_4721_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4723_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4724_ = l_Lean_stringToMessageData(v___x_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4725_){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4726_ = lean_array_to_list(v_msgs_4725_);
v___x_4727_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4728_ = l_Lean_MessageData_joinSep(v___x_4726_, v___x_4727_);
v___x_4729_ = l_Lean_indentD(v___x_4728_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4730_, lean_object* v_lctx_4731_, lean_object* v_opts_4732_, lean_object* v_msg_4733_){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4734_ = lean_elab_environment_of_kernel_env(v_env_4730_);
v___x_4735_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4736_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4734_);
lean_ctor_set(v___x_4736_, 1, v___x_4735_);
lean_ctor_set(v___x_4736_, 2, v_lctx_4731_);
lean_ctor_set(v___x_4736_, 3, v_opts_4732_);
v___x_4737_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
lean_ctor_set(v___x_4737_, 1, v_msg_4733_);
return v___x_4737_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4739_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4740_ = l_Lean_stringToMessageData(v___x_4739_);
return v___x_4740_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4743_ = l_Lean_stringToMessageData(v___x_4742_);
return v___x_4743_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4746_ = l_Lean_stringToMessageData(v___x_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4747_, lean_object* v_n_4748_, lean_object* v_expectedType_4749_){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4750_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4751_ = l_Lean_MessageData_ofName(v_n_4748_);
v___x_4752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
v___x_4753_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4752_);
lean_ctor_set(v___x_4754_, 1, v___x_4753_);
v___x_4755_ = l_Lean_indentExpr(v_givenType_4747_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4754_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = l_Lean_indentExpr(v_expectedType_4749_);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
return v___x_4760_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4761_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
return v___x_4763_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4764_ = lean_box(1);
v___x_4765_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4766_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
lean_ctor_set(v___x_4767_, 1, v___x_4765_);
lean_ctor_set(v___x_4767_, 2, v___x_4764_);
return v___x_4767_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4769_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4770_ = l_Lean_stringToMessageData(v___x_4769_);
return v___x_4770_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4773_ = l_Lean_stringToMessageData(v___x_4772_);
return v___x_4773_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4776_ = l_Lean_stringToMessageData(v___x_4775_);
return v___x_4776_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4781_ = l_Lean_MessageData_ofFormat(v___x_4780_);
return v___x_4781_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4784_ = l_Lean_stringToMessageData(v___x_4783_);
return v___x_4784_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4787_ = l_Lean_stringToMessageData(v___x_4786_);
return v___x_4787_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4789_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4790_ = l_Lean_stringToMessageData(v___x_4789_);
return v___x_4790_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4793_ = l_Lean_stringToMessageData(v___x_4792_);
return v___x_4793_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4796_ = l_Lean_stringToMessageData(v___x_4795_);
return v___x_4796_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4799_ = l_Lean_stringToMessageData(v___x_4798_);
return v___x_4799_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4802_ = l_Lean_stringToMessageData(v___x_4801_);
return v___x_4802_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4805_ = l_Lean_stringToMessageData(v___x_4804_);
return v___x_4805_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4808_ = l_Lean_stringToMessageData(v___x_4807_);
return v___x_4808_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4811_ = l_Lean_stringToMessageData(v___x_4810_);
return v___x_4811_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4813_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4814_ = l_Lean_stringToMessageData(v___x_4813_);
return v___x_4814_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4816_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4817_ = l_Lean_stringToMessageData(v___x_4816_);
return v___x_4817_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4819_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4820_ = l_Lean_stringToMessageData(v___x_4819_);
return v___x_4820_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4823_ = l_Lean_stringToMessageData(v___x_4822_);
return v___x_4823_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4828_ = l_Lean_MessageData_ofFormat(v___x_4827_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4833_ = l_Lean_MessageData_ofFormat(v___x_4832_);
return v___x_4833_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4838_ = l_Lean_MessageData_ofFormat(v___x_4837_);
return v___x_4838_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4843_ = l_Lean_MessageData_ofFormat(v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4844_, lean_object* v_opts_4845_){
_start:
{
switch(lean_obj_tag(v_e_4844_))
{
case 0:
{
lean_object* v_env_4846_; lean_object* v_name_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4860_; 
v_env_4846_ = lean_ctor_get(v_e_4844_, 0);
v_name_4847_ = lean_ctor_get(v_e_4844_, 1);
v_isSharedCheck_4860_ = !lean_is_exclusive(v_e_4844_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4849_ = v_e_4844_;
v_isShared_4850_ = v_isSharedCheck_4860_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_name_4847_);
lean_inc(v_env_4846_);
lean_dec(v_e_4844_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4860_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4851_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4852_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4853_ = l_Lean_MessageData_ofName(v_name_4847_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set_tag(v___x_4849_, 7);
lean_ctor_set(v___x_4849_, 1, v___x_4853_);
lean_ctor_set(v___x_4849_, 0, v___x_4852_);
v___x_4855_ = v___x_4849_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4859_, 1, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4855_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4846_, v___x_4851_, v_opts_4845_, v___x_4857_);
return v___x_4858_;
}
}
}
case 1:
{
lean_object* v_env_4861_; lean_object* v_name_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4876_; 
v_env_4861_ = lean_ctor_get(v_e_4844_, 0);
v_name_4862_ = lean_ctor_get(v_e_4844_, 1);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_e_4844_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4864_ = v_e_4844_;
v_isShared_4865_ = v_isSharedCheck_4876_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_name_4862_);
lean_inc(v_env_4861_);
lean_dec(v_e_4844_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4876_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4866_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4867_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4868_ = 1;
v___x_4869_ = l_Lean_MessageData_ofConstName(v_name_4862_, v___x_4868_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set_tag(v___x_4864_, 7);
lean_ctor_set(v___x_4864_, 1, v___x_4869_);
lean_ctor_set(v___x_4864_, 0, v___x_4867_);
v___x_4871_ = v___x_4864_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4867_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4872_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4861_, v___x_4866_, v_opts_4845_, v___x_4873_);
return v___x_4874_;
}
}
}
case 2:
{
lean_object* v_env_4877_; lean_object* v_decl_4878_; lean_object* v_givenType_4879_; lean_object* v___x_4880_; 
v_env_4877_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4877_);
v_decl_4878_ = lean_ctor_get(v_e_4844_, 1);
lean_inc(v_decl_4878_);
v_givenType_4879_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_givenType_4879_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4880_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4878_))
{
case 1:
{
lean_object* v_val_4881_; lean_object* v_toConstantVal_4882_; lean_object* v_name_4883_; lean_object* v_type_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_val_4881_ = lean_ctor_get(v_decl_4878_, 0);
lean_inc_ref(v_val_4881_);
lean_dec_ref_known(v_decl_4878_, 1);
v_toConstantVal_4882_ = lean_ctor_get(v_val_4881_, 0);
lean_inc_ref(v_toConstantVal_4882_);
lean_dec_ref(v_val_4881_);
v_name_4883_ = lean_ctor_get(v_toConstantVal_4882_, 0);
lean_inc(v_name_4883_);
v_type_4884_ = lean_ctor_get(v_toConstantVal_4882_, 2);
lean_inc_ref(v_type_4884_);
lean_dec_ref(v_toConstantVal_4882_);
v___x_4885_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4879_, v_name_4883_, v_type_4884_);
v___x_4886_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4877_, v___x_4880_, v_opts_4845_, v___x_4885_);
return v___x_4886_;
}
case 2:
{
lean_object* v_val_4887_; lean_object* v_toConstantVal_4888_; lean_object* v_name_4889_; lean_object* v_type_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v_val_4887_ = lean_ctor_get(v_decl_4878_, 0);
lean_inc_ref(v_val_4887_);
lean_dec_ref_known(v_decl_4878_, 1);
v_toConstantVal_4888_ = lean_ctor_get(v_val_4887_, 0);
lean_inc_ref(v_toConstantVal_4888_);
lean_dec_ref(v_val_4887_);
v_name_4889_ = lean_ctor_get(v_toConstantVal_4888_, 0);
lean_inc(v_name_4889_);
v_type_4890_ = lean_ctor_get(v_toConstantVal_4888_, 2);
lean_inc_ref(v_type_4890_);
lean_dec_ref(v_toConstantVal_4888_);
v___x_4891_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4879_, v_name_4889_, v_type_4890_);
v___x_4892_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4877_, v___x_4880_, v_opts_4845_, v___x_4891_);
return v___x_4892_;
}
default: 
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec_ref(v_givenType_4879_);
lean_dec(v_decl_4878_);
v___x_4893_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4894_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4877_, v___x_4880_, v_opts_4845_, v___x_4893_);
return v___x_4894_;
}
}
}
case 3:
{
lean_object* v_env_4895_; lean_object* v_name_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v_env_4895_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4895_);
v_name_4896_ = lean_ctor_get(v_e_4844_, 1);
lean_inc(v_name_4896_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4897_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4898_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4899_ = 1;
v___x_4900_ = l_Lean_MessageData_ofConstName(v_name_4896_, v___x_4899_);
v___x_4901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4898_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
v___x_4902_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4901_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4895_, v___x_4897_, v_opts_4845_, v___x_4903_);
return v___x_4904_;
}
case 4:
{
lean_object* v_env_4905_; lean_object* v_name_4906_; lean_object* v_expr_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v_env_4905_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4905_);
v_name_4906_ = lean_ctor_get(v_e_4844_, 1);
lean_inc(v_name_4906_);
v_expr_4907_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_expr_4907_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4908_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4909_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4910_ = 1;
v___x_4911_ = l_Lean_MessageData_ofConstName(v_name_4906_, v___x_4910_);
v___x_4912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4909_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
v___x_4913_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = l_Lean_indentExpr(v_expr_4907_);
v___x_4916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
v___x_4917_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4905_, v___x_4908_, v_opts_4845_, v___x_4916_);
return v___x_4917_;
}
case 5:
{
lean_object* v_env_4918_; lean_object* v_lctx_4919_; lean_object* v_expr_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v_env_4918_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4918_);
v_lctx_4919_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4919_);
v_expr_4920_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_expr_4920_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4921_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4922_ = l_Lean_indentExpr(v_expr_4920_);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4921_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
v___x_4924_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4918_, v_lctx_4919_, v_opts_4845_, v___x_4923_);
return v___x_4924_;
}
case 6:
{
lean_object* v_env_4925_; lean_object* v_lctx_4926_; lean_object* v_expr_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_env_4925_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4925_);
v_lctx_4926_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4926_);
v_expr_4927_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_expr_4927_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4928_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4929_ = l_Lean_indentExpr(v_expr_4927_);
v___x_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4925_, v_lctx_4926_, v_opts_4845_, v___x_4930_);
return v___x_4931_;
}
case 7:
{
lean_object* v_env_4932_; lean_object* v_lctx_4933_; lean_object* v_name_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v_env_4932_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4932_);
v_lctx_4933_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4933_);
v_name_4934_ = lean_ctor_get(v_e_4844_, 2);
lean_inc(v_name_4934_);
lean_dec_ref_known(v_e_4844_, 5);
v___x_4935_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4936_ = l_Lean_MessageData_ofName(v_name_4934_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4932_, v_lctx_4933_, v_opts_4845_, v___x_4939_);
return v___x_4940_;
}
case 8:
{
lean_object* v_env_4941_; lean_object* v_lctx_4942_; lean_object* v_expr_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v_env_4941_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4941_);
v_lctx_4942_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4942_);
v_expr_4943_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_expr_4943_);
lean_dec_ref_known(v_e_4844_, 4);
v___x_4944_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_4945_ = l_Lean_indentExpr(v_expr_4943_);
v___x_4946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4944_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
v___x_4947_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4941_, v_lctx_4942_, v_opts_4845_, v___x_4946_);
return v___x_4947_;
}
case 9:
{
lean_object* v_env_4948_; lean_object* v_lctx_4949_; lean_object* v_app_4950_; lean_object* v_funType_4951_; lean_object* v_argType_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_env_4948_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4948_);
v_lctx_4949_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4949_);
v_app_4950_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_app_4950_);
v_funType_4951_ = lean_ctor_get(v_e_4844_, 3);
lean_inc_ref(v_funType_4951_);
v_argType_4952_ = lean_ctor_get(v_e_4844_, 4);
lean_inc_ref(v_argType_4952_);
lean_dec_ref_known(v_e_4844_, 5);
v___x_4953_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_4954_ = l_Lean_indentExpr(v_app_4950_);
v___x_4955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4953_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l_Lean_indentExpr(v_argType_4952_);
v___x_4959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_4961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4959_);
lean_ctor_set(v___x_4961_, 1, v___x_4960_);
v___x_4962_ = l_Lean_indentExpr(v_funType_4951_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4961_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4948_, v_lctx_4949_, v_opts_4845_, v___x_4963_);
return v___x_4964_;
}
case 10:
{
lean_object* v_env_4965_; lean_object* v_lctx_4966_; lean_object* v_proj_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_env_4965_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4965_);
v_lctx_4966_ = lean_ctor_get(v_e_4844_, 1);
lean_inc_ref(v_lctx_4966_);
v_proj_4967_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_proj_4967_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4968_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_4969_ = l_Lean_indentExpr(v_proj_4967_);
v___x_4970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4968_);
lean_ctor_set(v___x_4970_, 1, v___x_4969_);
v___x_4971_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4965_, v_lctx_4966_, v_opts_4845_, v___x_4970_);
return v___x_4971_;
}
case 11:
{
lean_object* v_env_4972_; lean_object* v_name_4973_; lean_object* v_type_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v_env_4972_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_env_4972_);
v_name_4973_ = lean_ctor_get(v_e_4844_, 1);
lean_inc(v_name_4973_);
v_type_4974_ = lean_ctor_get(v_e_4844_, 2);
lean_inc_ref(v_type_4974_);
lean_dec_ref_known(v_e_4844_, 3);
v___x_4975_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4976_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_4977_ = 1;
v___x_4978_ = l_Lean_MessageData_ofConstName(v_name_4973_, v___x_4977_);
v___x_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4976_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = l_Lean_indentExpr(v_type_4974_);
v___x_4983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4972_, v___x_4975_, v_opts_4845_, v___x_4983_);
return v___x_4984_;
}
case 12:
{
lean_object* v_msg_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
lean_dec_ref(v_opts_4845_);
v_msg_4985_ = lean_ctor_get(v_e_4844_, 0);
lean_inc_ref(v_msg_4985_);
lean_dec_ref_known(v_e_4844_, 1);
v___x_4986_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_4987_ = l_Lean_stringToMessageData(v_msg_4985_);
v___x_4988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
return v___x_4988_;
}
case 13:
{
lean_object* v___x_4989_; 
lean_dec_ref(v_opts_4845_);
v___x_4989_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_4989_;
}
case 14:
{
lean_object* v___x_4990_; 
lean_dec_ref(v_opts_4845_);
v___x_4990_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_4990_;
}
case 15:
{
lean_object* v___x_4991_; 
lean_dec_ref(v_opts_4845_);
v___x_4991_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_4991_;
}
default: 
{
lean_object* v___x_4992_; 
lean_dec_ref(v_opts_4845_);
v___x_4992_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_4992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4993_, lean_object* v_e_4994_, lean_object* v_cls_4995_){
_start:
{
lean_object* v___x_4996_; double v___x_4997_; uint8_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_4996_ = lean_box(0);
v___x_4997_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4998_ = 1;
v___x_4999_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_5000_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5000_, 0, v_cls_4995_);
lean_ctor_set(v___x_5000_, 1, v___x_4996_);
lean_ctor_set(v___x_5000_, 2, v___x_4999_);
lean_ctor_set_float(v___x_5000_, sizeof(void*)*3, v___x_4997_);
lean_ctor_set_float(v___x_5000_, sizeof(void*)*3 + 8, v___x_4997_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*3 + 16, v___x_4998_);
v___x_5001_ = lean_apply_1(v_inst_4993_, v_e_4994_);
v___x_5002_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_5003_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5000_);
lean_ctor_set(v___x_5003_, 1, v___x_5001_);
lean_ctor_set(v___x_5003_, 2, v___x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_5004_, lean_object* v_inst_5005_, lean_object* v_e_5006_, lean_object* v_cls_5007_){
_start:
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Lean_toTraceElem___redArg(v_inst_5005_, v_e_5006_, v_cls_5007_);
return v___x_5008_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Linter_CodeQuality_Basic(builtin);
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
lean_object* initialize_Lean_Linter_CodeQuality_Basic(uint8_t builtin);
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
res = initialize_Lean_Linter_CodeQuality_Basic(builtin);
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
