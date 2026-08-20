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
if (lean_obj_tag(v___y_39_) == 0)
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
v_val_45_ = lean_ctor_get(v___y_39_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_39_, 1);
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
case 11:
{
lean_object* v___x_376_; 
v___x_376_ = lean_unsigned_to_nat(11u);
return v___x_376_;
}
default: 
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(12u);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___boxed(lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_MessageData_ctorIdx(v_x_378_);
lean_dec_ref(v_x_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_380_, lean_object* v_k_381_){
_start:
{
switch(lean_obj_tag(v_t_380_))
{
case 0:
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_a_382_);
lean_dec_ref_known(v_t_380_, 1);
v___x_383_ = lean_apply_1(v_k_381_, v_a_382_);
return v___x_383_;
}
case 1:
{
lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_384_ = lean_ctor_get(v_t_380_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_t_380_, 1);
v___x_385_ = lean_apply_1(v_k_381_, v_a_384_);
return v___x_385_;
}
case 5:
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_386_ = lean_ctor_get(v_t_380_, 0);
lean_inc(v_a_386_);
v_a_387_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_a_387_);
lean_dec_ref_known(v_t_380_, 2);
v___x_388_ = lean_apply_2(v_k_381_, v_a_386_, v_a_387_);
return v___x_388_;
}
case 6:
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_a_389_);
lean_dec_ref_known(v_t_380_, 1);
v___x_390_ = lean_apply_1(v_k_381_, v_a_389_);
return v___x_390_;
}
case 8:
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_391_ = lean_ctor_get(v_t_380_, 0);
lean_inc(v_a_391_);
v_a_392_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_a_392_);
lean_dec_ref_known(v_t_380_, 2);
v___x_393_ = lean_apply_2(v_k_381_, v_a_391_, v_a_392_);
return v___x_393_;
}
case 9:
{
lean_object* v_data_394_; lean_object* v_msg_395_; lean_object* v_children_396_; lean_object* v___x_397_; 
v_data_394_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_data_394_);
v_msg_395_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_msg_395_);
v_children_396_ = lean_ctor_get(v_t_380_, 2);
lean_inc_ref(v_children_396_);
lean_dec_ref_known(v_t_380_, 3);
v___x_397_ = lean_apply_3(v_k_381_, v_data_394_, v_msg_395_, v_children_396_);
return v___x_397_;
}
case 11:
{
lean_object* v_a_398_; lean_object* v_a_399_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v_t_380_, 0);
lean_inc(v_a_398_);
v_a_399_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_a_399_);
lean_dec_ref_known(v_t_380_, 2);
v___x_400_ = lean_apply_2(v_k_381_, v_a_398_, v_a_399_);
return v___x_400_;
}
default: 
{
lean_object* v_a_401_; lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_a_401_);
v_a_402_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_a_402_);
lean_dec_ref(v_t_380_);
v___x_403_ = lean_apply_2(v_k_381_, v_a_401_, v_a_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_404_, lean_object* v_ctorIdx_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_k_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_MessageData_ctorElim___redArg(v_t_406_, v_k_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_410_, lean_object* v_ctorIdx_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_k_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_MessageData_ctorElim(v_motive__1_410_, v_ctorIdx_411_, v_t_412_, v_h_413_, v_k_414_);
lean_dec(v_ctorIdx_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_416_, lean_object* v_ofFormatWithInfos_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MessageData_ctorElim___redArg(v_t_416_, v_ofFormatWithInfos_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_ofFormatWithInfos_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_MessageData_ctorElim___redArg(v_t_420_, v_ofFormatWithInfos_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_424_, lean_object* v_ofGoal_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_MessageData_ctorElim___redArg(v_t_424_, v_ofGoal_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_ofGoal_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MessageData_ctorElim___redArg(v_t_428_, v_ofGoal_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_432_, lean_object* v_ofWidget_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MessageData_ctorElim___redArg(v_t_432_, v_ofWidget_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_ofWidget_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MessageData_ctorElim___redArg(v_t_436_, v_ofWidget_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_440_, lean_object* v_withContext_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_MessageData_ctorElim___redArg(v_t_440_, v_withContext_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_withContext_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_MessageData_ctorElim___redArg(v_t_444_, v_withContext_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_448_, lean_object* v_withNamingContext_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_MessageData_ctorElim___redArg(v_t_448_, v_withNamingContext_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_withNamingContext_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MessageData_ctorElim___redArg(v_t_452_, v_withNamingContext_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_456_, lean_object* v_nest_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MessageData_ctorElim___redArg(v_t_456_, v_nest_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_nest_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_MessageData_ctorElim___redArg(v_t_460_, v_nest_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_464_, lean_object* v_group_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_MessageData_ctorElim___redArg(v_t_464_, v_group_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_group_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MessageData_ctorElim___redArg(v_t_468_, v_group_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_472_, lean_object* v_compose_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_MessageData_ctorElim___redArg(v_t_472_, v_compose_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_compose_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MessageData_ctorElim___redArg(v_t_476_, v_compose_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_480_, lean_object* v_tagged_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MessageData_ctorElim___redArg(v_t_480_, v_tagged_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_tagged_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MessageData_ctorElim___redArg(v_t_484_, v_tagged_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_488_, lean_object* v_trace_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_MessageData_ctorElim___redArg(v_t_488_, v_trace_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_trace_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MessageData_ctorElim___redArg(v_t_492_, v_trace_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_496_, lean_object* v_ofLazy_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_MessageData_ctorElim___redArg(v_t_496_, v_ofLazy_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_ofLazy_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_MessageData_ctorElim___redArg(v_t_500_, v_ofLazy_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_504_, lean_object* v_ofOriginatingSyntax_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_MessageData_ctorElim___redArg(v_t_504_, v_ofOriginatingSyntax_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_ofOriginatingSyntax_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_MessageData_ctorElim___redArg(v_t_508_, v_ofOriginatingSyntax_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim___redArg(lean_object* v_t_512_, lean_object* v_ofCodeQualityEntry_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_MessageData_ctorElim___redArg(v_t_512_, v_ofCodeQualityEntry_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofCodeQualityEntry_elim(lean_object* v_motive__1_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_ofCodeQualityEntry_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_MessageData_ctorElim___redArg(v_t_516_, v_ofCodeQualityEntry_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_box(1);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_fmt_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_535_, lean_object* v_onMissingContext_536_, lean_object* v_f_537_, lean_object* v_ctx_x3f_538_){
_start:
{
lean_object* v_msg_541_; 
if (lean_obj_tag(v_ctx_x3f_538_) == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_f_537_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_2(v_onMissingContext_536_, v___x_543_, lean_box(0));
v_msg_541_ = v___x_544_;
goto v___jp_540_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_546_; 
lean_dec_ref(v_onMissingContext_536_);
v_val_545_ = lean_ctor_get(v_ctx_x3f_538_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_ctx_x3f_538_, 1);
v___x_546_ = lean_apply_2(v_f_537_, v_val_545_, lean_box(0));
v_msg_541_ = v___x_546_;
goto v___jp_540_;
}
v___jp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_535_);
lean_ctor_set(v___x_542_, 1, v_msg_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_547_, lean_object* v_onMissingContext_548_, lean_object* v_f_549_, lean_object* v_ctx_x3f_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_MessageData_lazy___lam__0(v___x_547_, v_onMissingContext_548_, v_f_549_, v_ctx_x3f_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_553_, lean_object* v_hasSyntheticSorry_554_, lean_object* v_onMissingContext_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
v___x_556_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_557_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_557_, 0, v___x_556_);
lean_closure_set(v___f_557_, 1, v_onMissingContext_555_);
lean_closure_set(v___f_557_, 2, v_f_553_);
v___x_558_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_558_, 0, v___f_557_);
lean_ctor_set(v___x_558_, 1, v_hasSyntheticSorry_554_);
return v___x_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_559_, lean_object* v_x_560_){
_start:
{
switch(lean_obj_tag(v_x_560_))
{
case 3:
{
lean_object* v_a_561_; 
v_a_561_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_561_);
lean_dec_ref_known(v_x_560_, 2);
v_x_560_ = v_a_561_;
goto _start;
}
case 4:
{
lean_object* v_a_563_; 
v_a_563_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_563_);
lean_dec_ref_known(v_x_560_, 2);
v_x_560_ = v_a_563_;
goto _start;
}
case 5:
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v_x_560_, 2);
v_x_560_ = v_a_565_;
goto _start;
}
case 6:
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v_x_560_, 0);
lean_inc_ref(v_a_567_);
lean_dec_ref_known(v_x_560_, 1);
v_x_560_ = v_a_567_;
goto _start;
}
case 7:
{
lean_object* v_a_569_; lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_569_ = lean_ctor_get(v_x_560_, 0);
lean_inc_ref(v_a_569_);
v_a_570_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_570_);
lean_dec_ref_known(v_x_560_, 2);
lean_inc_ref(v_p_559_);
v___x_571_ = l_Lean_MessageData_hasTag(v_p_559_, v_a_569_);
if (v___x_571_ == 0)
{
v_x_560_ = v_a_570_;
goto _start;
}
else
{
lean_dec_ref(v_a_570_);
lean_dec_ref(v_p_559_);
return v___x_571_;
}
}
case 8:
{
lean_object* v_a_573_; lean_object* v_a_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_a_573_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_a_573_);
v_a_574_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_574_);
lean_dec_ref_known(v_x_560_, 2);
lean_inc_ref(v_p_559_);
v___x_575_ = lean_apply_1(v_p_559_, v_a_573_);
v___x_576_ = lean_unbox(v___x_575_);
if (v___x_576_ == 0)
{
v_x_560_ = v_a_574_;
goto _start;
}
else
{
uint8_t v___x_578_; 
lean_dec_ref(v_a_574_);
lean_dec_ref(v_p_559_);
v___x_578_ = lean_unbox(v___x_575_);
return v___x_578_;
}
}
case 9:
{
lean_object* v_data_579_; lean_object* v_msg_580_; lean_object* v_children_581_; lean_object* v_cls_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_data_579_ = lean_ctor_get(v_x_560_, 0);
lean_inc_ref(v_data_579_);
v_msg_580_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_msg_580_);
v_children_581_ = lean_ctor_get(v_x_560_, 2);
lean_inc_ref(v_children_581_);
lean_dec_ref_known(v_x_560_, 3);
v_cls_582_ = lean_ctor_get(v_data_579_, 0);
lean_inc(v_cls_582_);
lean_dec_ref(v_data_579_);
lean_inc_ref(v_p_559_);
v___x_583_ = lean_apply_1(v_p_559_, v_cls_582_);
v___x_584_ = lean_unbox(v___x_583_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
lean_inc_ref(v_p_559_);
v___x_585_ = l_Lean_MessageData_hasTag(v_p_559_, v_msg_580_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_get_size(v_children_581_);
v___x_588_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_dec_ref(v_children_581_);
lean_dec_ref(v_p_559_);
return v___x_585_;
}
else
{
if (v___x_588_ == 0)
{
lean_dec_ref(v_children_581_);
lean_dec_ref(v_p_559_);
return v___x_585_;
}
else
{
size_t v___x_589_; size_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_587_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_559_, v_children_581_, v___x_589_, v___x_590_);
lean_dec_ref(v_children_581_);
return v___x_591_;
}
}
}
else
{
lean_dec_ref(v_children_581_);
lean_dec_ref(v_p_559_);
return v___x_585_;
}
}
else
{
uint8_t v___x_592_; 
lean_dec_ref(v_children_581_);
lean_dec_ref(v_msg_580_);
lean_dec_ref(v_p_559_);
v___x_592_ = lean_unbox(v___x_583_);
return v___x_592_;
}
}
case 11:
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_593_);
lean_dec_ref_known(v_x_560_, 2);
v_x_560_ = v_a_593_;
goto _start;
}
case 12:
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_a_595_);
lean_dec_ref_known(v_x_560_, 2);
v_x_560_ = v_a_595_;
goto _start;
}
default: 
{
uint8_t v___x_597_; 
lean_dec_ref(v_x_560_);
lean_dec_ref(v_p_559_);
v___x_597_ = 0;
return v___x_597_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_598_, lean_object* v_as_599_, size_t v_i_600_, size_t v_stop_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_usize_dec_eq(v_i_600_, v_stop_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_uget_borrowed(v_as_599_, v_i_600_);
lean_inc(v___x_603_);
lean_inc_ref(v_p_598_);
v___x_604_ = l_Lean_MessageData_hasTag(v_p_598_, v___x_603_);
if (v___x_604_ == 0)
{
size_t v___x_605_; size_t v___x_606_; 
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_600_, v___x_605_);
v_i_600_ = v___x_606_;
goto _start;
}
else
{
lean_dec_ref(v_p_598_);
return v___x_604_;
}
}
else
{
uint8_t v___x_608_; 
lean_dec_ref(v_p_598_);
v___x_608_ = 0;
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_609_, lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_stop_612_){
_start:
{
size_t v_i_boxed_613_; size_t v_stop_boxed_614_; uint8_t v_res_615_; lean_object* v_r_616_; 
v_i_boxed_613_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_stop_boxed_614_ = lean_unbox_usize(v_stop_612_);
lean_dec(v_stop_612_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_609_, v_as_610_, v_i_boxed_613_, v_stop_boxed_614_);
lean_dec_ref(v_as_610_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_617_, lean_object* v_x_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Lean_MessageData_hasTag(v_p_617_, v_x_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_621_){
_start:
{
switch(lean_obj_tag(v_x_621_))
{
case 3:
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v_x_621_, 1);
v_x_621_ = v_a_622_;
goto _start;
}
case 4:
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v_x_621_, 1);
v_x_621_ = v_a_624_;
goto _start;
}
case 8:
{
lean_object* v_a_626_; 
v_a_626_ = lean_ctor_get(v_x_621_, 0);
lean_inc(v_a_626_);
return v_a_626_;
}
case 9:
{
lean_object* v_data_627_; lean_object* v_cls_628_; 
v_data_627_ = lean_ctor_get(v_x_621_, 0);
v_cls_628_ = lean_ctor_get(v_data_627_, 0);
lean_inc(v_cls_628_);
return v_cls_628_;
}
case 11:
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v_x_621_, 1);
v_x_621_ = v_a_629_;
goto _start;
}
case 12:
{
lean_object* v_a_631_; 
v_a_631_ = lean_ctor_get(v_x_621_, 1);
v_x_621_ = v_a_631_;
goto _start;
}
default: 
{
lean_object* v___x_633_; 
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_MessageData_kind(v_x_634_);
lean_dec_ref(v_x_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 11)
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
v_a_637_ = lean_ctor_get(v_x_636_, 0);
v_a_638_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_inc(v_a_637_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_a_637_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_a_638_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_x_636_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f(lean_object* v_x_649_){
_start:
{
switch(lean_obj_tag(v_x_649_))
{
case 12:
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v_x_649_, 0);
lean_inc_ref(v_a_650_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_a_650_);
return v___x_651_;
}
case 3:
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v_x_649_, 1);
v_x_649_ = v_a_652_;
goto _start;
}
case 4:
{
lean_object* v_a_654_; 
v_a_654_ = lean_ctor_get(v_x_649_, 1);
v_x_649_ = v_a_654_;
goto _start;
}
case 8:
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v_x_649_, 1);
v_x_649_ = v_a_656_;
goto _start;
}
case 11:
{
lean_object* v_a_658_; 
v_a_658_ = lean_ctor_get(v_x_649_, 1);
v_x_649_ = v_a_658_;
goto _start;
}
default: 
{
lean_object* v___x_660_; 
v___x_660_ = lean_box(0);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_codeQualityEntry_x3f___boxed(lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_MessageData_codeQualityEntry_x3f(v_x_661_);
lean_dec_ref(v_x_661_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_663_){
_start:
{
switch(lean_obj_tag(v_x_663_))
{
case 3:
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v_x_663_, 1);
v_x_663_ = v_a_664_;
goto _start;
}
case 4:
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v_x_663_, 1);
v_x_663_ = v_a_666_;
goto _start;
}
case 8:
{
lean_object* v_a_668_; 
v_a_668_ = lean_ctor_get(v_x_663_, 1);
v_x_663_ = v_a_668_;
goto _start;
}
case 9:
{
uint8_t v___x_670_; 
v___x_670_ = 1;
return v___x_670_;
}
case 11:
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v_x_663_, 1);
v_x_663_ = v_a_671_;
goto _start;
}
case 12:
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v_x_663_, 1);
v_x_663_ = v_a_673_;
goto _start;
}
default: 
{
uint8_t v___x_675_; 
v___x_675_ = 0;
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lean_MessageData_isTrace(v_x_676_);
lean_dec_ref(v_x_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
switch(lean_obj_tag(v_x_679_))
{
case 3:
{
lean_object* v_a_681_; lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_690_; 
v_a_681_ = lean_ctor_get(v_x_679_, 0);
v_a_682_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_690_ == 0)
{
v___x_684_ = v_x_679_;
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_inc(v_a_681_);
lean_dec(v_x_679_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_MessageData_composePreservingKind(v_a_682_, v_x_680_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_686_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_681_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
case 4:
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_a_691_ = lean_ctor_get(v_x_679_, 0);
v_a_692_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v_x_679_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_inc(v_a_691_);
lean_dec(v_x_679_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_MessageData_composePreservingKind(v_a_692_, v_x_680_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
case 8:
{
lean_object* v_a_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_a_701_ = lean_ctor_get(v_x_679_, 0);
v_a_702_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v_x_679_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_inc(v_a_701_);
lean_dec(v_x_679_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 7);
lean_ctor_set(v___x_704_, 1, v_x_680_);
lean_ctor_set(v___x_704_, 0, v_a_702_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_702_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_x_680_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_708_, 0, v_a_701_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
}
}
case 11:
{
lean_object* v_a_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_a_711_ = lean_ctor_get(v_x_679_, 0);
v_a_712_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v_x_679_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_inc(v_a_711_);
lean_dec(v_x_679_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Lean_MessageData_composePreservingKind(v_a_712_, v_x_680_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_711_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
case 12:
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_a_721_ = lean_ctor_get(v_x_679_, 0);
v_a_722_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v_x_679_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_inc(v_a_721_);
lean_dec(v_x_679_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_MessageData_composePreservingKind(v_a_722_, v_x_680_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_721_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
default: 
{
lean_object* v___x_731_; 
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v_x_679_);
lean_ctor_set(v___x_731_, 1, v_x_680_);
return v___x_731_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(0);
v___x_733_ = l_Lean_MessageData_ofFormat(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_735_, lean_object* v_ctx_736_){
_start:
{
lean_object* v_env_737_; lean_object* v_mctx_738_; lean_object* v_lctx_739_; lean_object* v_opts_740_; lean_object* v_currNamespace_741_; lean_object* v_openDecls_742_; lean_object* v___x_743_; 
v_env_737_ = lean_ctor_get(v_ctx_736_, 0);
v_mctx_738_ = lean_ctor_get(v_ctx_736_, 1);
v_lctx_739_ = lean_ctor_get(v_ctx_736_, 2);
v_opts_740_ = lean_ctor_get(v_ctx_736_, 3);
v_currNamespace_741_ = lean_ctor_get(v_nCtx_735_, 0);
v_openDecls_742_ = lean_ctor_get(v_nCtx_735_, 1);
lean_inc(v_openDecls_742_);
lean_inc(v_currNamespace_741_);
lean_inc_ref(v_opts_740_);
lean_inc_ref(v_lctx_739_);
lean_inc_ref(v_mctx_738_);
lean_inc_ref(v_env_737_);
v___x_743_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_743_, 0, v_env_737_);
lean_ctor_set(v___x_743_, 1, v_mctx_738_);
lean_ctor_set(v___x_743_, 2, v_lctx_739_);
lean_ctor_set(v___x_743_, 3, v_opts_740_);
lean_ctor_set(v___x_743_, 4, v_currNamespace_741_);
lean_ctor_set(v___x_743_, 5, v_openDecls_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_744_, lean_object* v_ctx_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MessageData_mkPPContext(v_nCtx_744_, v_ctx_745_);
lean_dec_ref(v_ctx_745_);
lean_dec_ref(v_nCtx_744_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = 0;
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_749_);
lean_dec_ref(v_x_749_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_752_, lean_object* v_stx_753_, lean_object* v_ctx_x3f_754_){
_start:
{
lean_object* v_val_757_; 
if (lean_obj_tag(v_ctx_x3f_754_) == 0)
{
lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_box(0);
v___x_761_ = 0;
v___x_762_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_760_, v___x_761_);
v_val_757_ = v___x_762_;
goto v___jp_756_;
}
else
{
lean_object* v_val_763_; lean_object* v___x_764_; 
v_val_763_ = lean_ctor_get(v_ctx_x3f_754_, 0);
lean_inc(v_val_763_);
lean_dec_ref_known(v_ctx_x3f_754_, 1);
v___x_764_ = l_Lean_ppTerm(v_val_763_, v_stx_753_);
v_val_757_ = v___x_764_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l_Lean_MessageData_ofFormat(v_val_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_752_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_765_, lean_object* v_stx_766_, lean_object* v_ctx_x3f_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_765_, v_stx_766_, v_ctx_x3f_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_stx_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_772_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_773_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_774_ = lean_box(0);
v_stx_775_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_771_, v___x_774_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_776_, 0, v___x_773_);
lean_closure_set(v___f_776_, 1, v_stx_775_);
v___x_777_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_777_, 0, v___f_776_);
lean_ctor_set(v___x_777_, 1, v___f_772_);
return v___x_777_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_778_, lean_object* v_mctx_779_){
_start:
{
lean_object* v___x_780_; lean_object* v_fst_781_; uint8_t v___x_782_; 
v___x_780_ = l_Lean_instantiateMVarsCore(v_mctx_779_, v_e_778_);
v_fst_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_fst_781_);
lean_dec_ref(v___x_780_);
v___x_782_ = l_Lean_Expr_hasSyntheticSorry(v_fst_781_);
lean_dec(v_fst_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_783_, lean_object* v_mctx_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_MessageData_ofExpr___lam__0(v_e_783_, v_mctx_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_787_, lean_object* v_e_788_, lean_object* v_ctx_x3f_789_){
_start:
{
lean_object* v_val_792_; 
if (lean_obj_tag(v_ctx_x3f_789_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = lean_expr_dbg_to_string(v_e_788_);
lean_dec_ref(v_e_788_);
v___x_796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
v___x_797_ = lean_box(1);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_val_792_ = v___x_798_;
goto v___jp_791_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; 
v_val_799_ = lean_ctor_get(v_ctx_x3f_789_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v_ctx_x3f_789_, 1);
v___x_800_ = l_Lean_ppExprWithInfos(v_val_799_, v_e_788_);
v_val_792_ = v___x_800_;
goto v___jp_791_;
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_val_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_787_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_801_, lean_object* v_e_802_, lean_object* v_ctx_x3f_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_MessageData_ofExpr___lam__1(v___x_801_, v_e_802_, v_ctx_x3f_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; 
lean_inc_ref(v_e_806_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_807_, 0, v_e_806_);
v___x_808_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_809_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_809_, 0, v___x_808_);
lean_closure_set(v___f_809_, 1, v_e_806_);
v___x_810_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_810_, 0, v___f_809_);
lean_ctor_set(v___x_810_, 1, v___f_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(0);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_MessageData_ofLevel___lam__0(v_x_813_);
lean_dec(v_x_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_815_, lean_object* v_l_816_, lean_object* v___f_817_, lean_object* v_ctx_x3f_818_){
_start:
{
lean_object* v_val_821_; 
if (lean_obj_tag(v_ctx_x3f_818_) == 0)
{
uint8_t v___x_824_; lean_object* v___x_825_; 
v___x_824_ = 1;
v___x_825_ = l_Lean_Level_format(v_l_816_, v___x_824_, v___f_817_);
v_val_821_ = v___x_825_;
goto v___jp_820_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; 
lean_dec_ref(v___f_817_);
v_val_826_ = lean_ctor_get(v_ctx_x3f_818_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_ctx_x3f_818_, 1);
v___x_827_ = l_Lean_ppLevel(v_val_826_, v_l_816_);
v_val_821_ = v___x_827_;
goto v___jp_820_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = l_Lean_MessageData_ofFormat(v_val_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_815_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_828_, lean_object* v_l_829_, lean_object* v___f_830_, lean_object* v_ctx_x3f_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MessageData_ofLevel___lam__2(v___x_828_, v_l_829_, v___f_830_, v_ctx_x3f_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_835_){
_start:
{
lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___x_840_; 
v___f_836_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_837_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_838_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___f_839_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_839_, 0, v___x_838_);
lean_closure_set(v___f_839_, 1, v_l_835_);
lean_closure_set(v___f_839_, 2, v___f_836_);
v___x_840_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_840_, 0, v___f_839_);
lean_ctor_set(v___x_840_, 1, v___f_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_841_){
_start:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = 1;
v___x_843_ = l_Lean_Name_toString(v_n_841_, v___x_842_);
v___x_844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___x_845_ = l_Lean_MessageData_ofFormat(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_849_, lean_object* v_k_850_, uint8_t v_v_851_){
_start:
{
lean_object* v_map_852_; uint8_t v_hasTrace_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_867_; 
v_map_852_ = lean_ctor_get(v_o_849_, 0);
v_hasTrace_853_ = lean_ctor_get_uint8(v_o_849_, sizeof(void*)*1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_o_849_);
if (v_isSharedCheck_867_ == 0)
{
v___x_855_ = v_o_849_;
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_map_852_);
lean_dec(v_o_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_857_, 0, v_v_851_);
lean_inc(v_k_850_);
v___x_858_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_850_, v___x_857_, v_map_852_);
if (v_hasTrace_853_ == 0)
{
lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_862_; 
v___x_859_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_860_ = l_Lean_Name_isPrefixOf(v___x_859_, v_k_850_);
lean_dec(v_k_850_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_858_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_858_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v___x_860_);
return v___x_862_;
}
}
else
{
lean_object* v___x_865_; 
lean_dec(v_k_850_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_858_);
v___x_865_ = v___x_855_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*1, v_hasTrace_853_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_868_, lean_object* v_k_869_, lean_object* v_v_870_){
_start:
{
uint8_t v_v_boxed_871_; lean_object* v_res_872_; 
v_v_boxed_871_ = lean_unbox(v_v_870_);
v_res_872_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_868_, v_k_869_, v_v_boxed_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_878_, lean_object* v_constName_879_, uint8_t v_fullNames_880_, lean_object* v_ctx_x3f_881_){
_start:
{
lean_object* v_val_884_; lean_object* v___y_888_; 
if (lean_obj_tag(v_ctx_x3f_881_) == 0)
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_889_ = 1;
v___x_890_ = l_Lean_Name_toString(v_constName_879_, v___x_889_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_box(1);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v_val_884_ = v___x_893_;
goto v___jp_883_;
}
else
{
if (v_fullNames_880_ == 0)
{
lean_object* v_val_894_; lean_object* v___x_895_; 
v_val_894_ = lean_ctor_get(v_ctx_x3f_881_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_ctx_x3f_881_, 1);
v___x_895_ = l_Lean_ppConstNameWithInfos(v_val_894_, v_constName_879_);
v___y_888_ = v___x_895_;
goto v___jp_887_;
}
else
{
lean_object* v_val_896_; lean_object* v_env_897_; lean_object* v_mctx_898_; lean_object* v_lctx_899_; lean_object* v_opts_900_; lean_object* v_currNamespace_901_; lean_object* v_openDecls_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_val_896_ = lean_ctor_get(v_ctx_x3f_881_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v_ctx_x3f_881_, 1);
v_env_897_ = lean_ctor_get(v_val_896_, 0);
v_mctx_898_ = lean_ctor_get(v_val_896_, 1);
v_lctx_899_ = lean_ctor_get(v_val_896_, 2);
v_opts_900_ = lean_ctor_get(v_val_896_, 3);
v_currNamespace_901_ = lean_ctor_get(v_val_896_, 4);
v_openDecls_902_ = lean_ctor_get(v_val_896_, 5);
v_isSharedCheck_912_ = !lean_is_exclusive(v_val_896_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v_val_896_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_openDecls_902_);
lean_inc(v_currNamespace_901_);
lean_inc(v_opts_900_);
lean_inc(v_lctx_899_);
lean_inc(v_mctx_898_);
lean_inc(v_env_897_);
lean_dec(v_val_896_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_907_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_900_, v___x_906_, v_fullNames_880_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 3, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_env_897_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_mctx_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_lctx_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_currNamespace_901_);
lean_ctor_set(v_reuseFailAlloc_911_, 5, v_openDecls_902_);
v___x_909_ = v_reuseFailAlloc_911_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_ppConstNameWithInfos(v___x_909_, v_constName_879_);
v___y_888_ = v___x_910_;
goto v___jp_887_;
}
}
}
}
v___jp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_val_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_878_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
return v___x_886_;
}
v___jp_887_:
{
v_val_884_ = v___y_888_;
goto v___jp_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_913_, lean_object* v_constName_914_, lean_object* v_fullNames_915_, lean_object* v_ctx_x3f_916_, lean_object* v___y_917_){
_start:
{
uint8_t v_fullNames_boxed_918_; lean_object* v_res_919_; 
v_fullNames_boxed_918_ = lean_unbox(v_fullNames_915_);
v_res_919_ = l_Lean_MessageData_ofConstName___lam__1(v___x_913_, v_constName_914_, v_fullNames_boxed_918_, v_ctx_x3f_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_920_, uint8_t v_fullNames_921_){
_start:
{
lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; 
v___f_922_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_923_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_924_ = lean_box(v_fullNames_921_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_925_, 0, v___x_923_);
lean_closure_set(v___f_925_, 1, v_constName_920_);
lean_closure_set(v___f_925_, 2, v___x_924_);
v___x_926_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_926_, 0, v___f_925_);
lean_ctor_set(v___x_926_, 1, v___f_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_927_, lean_object* v_fullNames_928_){
_start:
{
uint8_t v_fullNames_boxed_929_; lean_object* v_res_930_; 
v_fullNames_boxed_929_ = lean_unbox(v_fullNames_928_);
v_res_930_ = l_Lean_MessageData_ofConstName(v_constName_927_, v_fullNames_boxed_929_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_val_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_MessageData_withExprHover___lam__0(v_val_935_, v___y_936_);
lean_dec_ref(v___y_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_939_, lean_object* v_v_940_, lean_object* v_t_941_){
_start:
{
if (lean_obj_tag(v_t_941_) == 0)
{
lean_object* v_size_942_; lean_object* v_k_943_; lean_object* v_v_944_; lean_object* v_l_945_; lean_object* v_r_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1227_; 
v_size_942_ = lean_ctor_get(v_t_941_, 0);
v_k_943_ = lean_ctor_get(v_t_941_, 1);
v_v_944_ = lean_ctor_get(v_t_941_, 2);
v_l_945_ = lean_ctor_get(v_t_941_, 3);
v_r_946_ = lean_ctor_get(v_t_941_, 4);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_t_941_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_948_ = v_t_941_;
v_isShared_949_ = v_isSharedCheck_1227_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_r_946_);
lean_inc(v_l_945_);
lean_inc(v_v_944_);
lean_inc(v_k_943_);
lean_inc(v_size_942_);
lean_dec(v_t_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1227_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_lt(v_k_939_, v_k_943_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_eq(v_k_939_, v_k_943_);
if (v___x_951_ == 0)
{
lean_object* v_impl_952_; lean_object* v___x_953_; 
lean_dec(v_size_942_);
v_impl_952_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_939_, v_v_940_, v_r_946_);
v___x_953_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_945_) == 0)
{
lean_object* v_size_954_; lean_object* v_size_955_; lean_object* v_k_956_; lean_object* v_v_957_; lean_object* v_l_958_; lean_object* v_r_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_size_954_ = lean_ctor_get(v_l_945_, 0);
v_size_955_ = lean_ctor_get(v_impl_952_, 0);
lean_inc(v_size_955_);
v_k_956_ = lean_ctor_get(v_impl_952_, 1);
lean_inc(v_k_956_);
v_v_957_ = lean_ctor_get(v_impl_952_, 2);
lean_inc(v_v_957_);
v_l_958_ = lean_ctor_get(v_impl_952_, 3);
lean_inc(v_l_958_);
v_r_959_ = lean_ctor_get(v_impl_952_, 4);
lean_inc(v_r_959_);
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_mul(v___x_960_, v_size_954_);
v___x_962_ = lean_nat_dec_lt(v___x_961_, v_size_955_);
lean_dec(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_r_959_);
lean_dec(v_l_958_);
lean_dec(v_v_957_);
lean_dec(v_k_956_);
v___x_963_ = lean_nat_add(v___x_953_, v_size_954_);
v___x_964_ = lean_nat_add(v___x_963_, v_size_955_);
lean_dec(v_size_955_);
lean_dec(v___x_963_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_impl_952_);
lean_ctor_set(v___x_948_, 0, v___x_964_);
v___x_966_ = v___x_948_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_945_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_impl_952_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1031_; 
v_isSharedCheck_1031_ = !lean_is_exclusive(v_impl_952_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1032_ = lean_ctor_get(v_impl_952_, 4);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_impl_952_, 3);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_impl_952_, 2);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_952_, 1);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_952_, 0);
lean_dec(v_unused_1036_);
v___x_969_ = v_impl_952_;
v_isShared_970_ = v_isSharedCheck_1031_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_impl_952_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1031_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_size_971_; lean_object* v_k_972_; lean_object* v_v_973_; lean_object* v_l_974_; lean_object* v_r_975_; lean_object* v_size_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_size_971_ = lean_ctor_get(v_l_958_, 0);
v_k_972_ = lean_ctor_get(v_l_958_, 1);
v_v_973_ = lean_ctor_get(v_l_958_, 2);
v_l_974_ = lean_ctor_get(v_l_958_, 3);
v_r_975_ = lean_ctor_get(v_l_958_, 4);
v_size_976_ = lean_ctor_get(v_r_959_, 0);
v___x_977_ = lean_unsigned_to_nat(2u);
v___x_978_ = lean_nat_mul(v___x_977_, v_size_976_);
v___x_979_ = lean_nat_dec_lt(v_size_971_, v___x_978_);
lean_dec(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1007_; 
lean_inc(v_r_975_);
lean_inc(v_l_974_);
lean_inc(v_v_973_);
lean_inc(v_k_972_);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_l_958_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; 
v_unused_1008_ = lean_ctor_get(v_l_958_, 4);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_l_958_, 3);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_l_958_, 2);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_l_958_, 1);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_l_958_, 0);
lean_dec(v_unused_1012_);
v___x_981_ = v_l_958_;
v_isShared_982_ = v_isSharedCheck_1007_;
goto v_resetjp_980_;
}
else
{
lean_dec(v_l_958_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1007_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_997_; 
v___x_983_ = lean_nat_add(v___x_953_, v_size_954_);
v___x_984_ = lean_nat_add(v___x_983_, v_size_955_);
lean_dec(v_size_955_);
if (lean_obj_tag(v_l_974_) == 0)
{
lean_object* v_size_1005_; 
v_size_1005_ = lean_ctor_get(v_l_974_, 0);
lean_inc(v_size_1005_);
v___y_997_ = v_size_1005_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___y_997_ = v___x_1006_;
goto v___jp_996_;
}
v___jp_985_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_nat_add(v___y_986_, v___y_988_);
lean_dec(v___y_988_);
lean_dec(v___y_986_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v_r_959_);
lean_ctor_set(v___x_981_, 3, v_r_975_);
lean_ctor_set(v___x_981_, 2, v_v_957_);
lean_ctor_set(v___x_981_, 1, v_k_956_);
lean_ctor_set(v___x_981_, 0, v___x_989_);
v___x_991_ = v___x_981_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_r_975_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_r_959_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v___x_991_);
lean_ctor_set(v___x_969_, 3, v___y_987_);
lean_ctor_set(v___x_969_, 2, v_v_973_);
lean_ctor_set(v___x_969_, 1, v_k_972_);
lean_ctor_set(v___x_969_, 0, v___x_984_);
v___x_993_ = v___x_969_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_972_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_973_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___y_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_nat_add(v___x_983_, v___y_997_);
lean_dec(v___y_997_);
lean_dec(v___x_983_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_l_974_);
lean_ctor_set(v___x_948_, 0, v___x_998_);
v___x_1000_ = v___x_948_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_l_945_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_l_974_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_nat_add(v___x_953_, v_size_976_);
if (lean_obj_tag(v_r_975_) == 0)
{
lean_object* v_size_1002_; 
v_size_1002_ = lean_ctor_get(v_r_975_, 0);
lean_inc(v_size_1002_);
v___y_986_ = v___x_1001_;
v___y_987_ = v___x_1000_;
v___y_988_ = v_size_1002_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___y_986_ = v___x_1001_;
v___y_987_ = v___x_1000_;
v___y_988_ = v___x_1003_;
goto v___jp_985_;
}
}
}
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_del_object(v___x_948_);
v___x_1013_ = lean_nat_add(v___x_953_, v_size_954_);
v___x_1014_ = lean_nat_add(v___x_1013_, v_size_955_);
lean_dec(v_size_955_);
v___x_1015_ = lean_nat_add(v___x_1013_, v_size_971_);
lean_dec(v___x_1013_);
lean_inc_ref(v_l_945_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_l_958_);
lean_ctor_set(v___x_969_, 3, v_l_945_);
lean_ctor_set(v___x_969_, 2, v_v_944_);
lean_ctor_set(v___x_969_, 1, v_k_943_);
lean_ctor_set(v___x_969_, 0, v___x_1015_);
v___x_1017_ = v___x_969_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_l_945_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_l_958_);
v___x_1017_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v_l_945_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; 
v_unused_1025_ = lean_ctor_get(v_l_945_, 4);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_l_945_, 3);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_l_945_, 2);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_l_945_, 1);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_l_945_, 0);
lean_dec(v_unused_1029_);
v___x_1019_ = v_l_945_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_l_945_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_r_959_);
lean_ctor_set(v___x_1019_, 3, v___x_1017_);
lean_ctor_set(v___x_1019_, 2, v_v_957_);
lean_ctor_set(v___x_1019_, 1, v_k_956_);
lean_ctor_set(v___x_1019_, 0, v___x_1014_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_r_959_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1037_; 
v_l_1037_ = lean_ctor_get(v_impl_952_, 3);
lean_inc(v_l_1037_);
if (lean_obj_tag(v_l_1037_) == 0)
{
lean_object* v_r_1038_; lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1063_; 
v_r_1038_ = lean_ctor_get(v_impl_952_, 4);
v_k_1039_ = lean_ctor_get(v_impl_952_, 1);
v_v_1040_ = lean_ctor_get(v_impl_952_, 2);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_impl_952_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; lean_object* v_unused_1065_; 
v_unused_1064_ = lean_ctor_get(v_impl_952_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_impl_952_, 0);
lean_dec(v_unused_1065_);
v___x_1042_ = v_impl_952_;
v_isShared_1043_ = v_isSharedCheck_1063_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_r_1038_);
lean_inc(v_v_1040_);
lean_inc(v_k_1039_);
lean_dec(v_impl_952_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1063_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_k_1044_; lean_object* v_v_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1059_; 
v_k_1044_ = lean_ctor_get(v_l_1037_, 1);
v_v_1045_ = lean_ctor_get(v_l_1037_, 2);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_l_1037_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1060_ = lean_ctor_get(v_l_1037_, 4);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_1037_, 3);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_l_1037_, 0);
lean_dec(v_unused_1062_);
v___x_1047_ = v_l_1037_;
v_isShared_1048_ = v_isSharedCheck_1059_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_v_1045_);
lean_inc(v_k_1044_);
lean_dec(v_l_1037_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1059_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1038_, 2);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_r_1038_);
lean_ctor_set(v___x_1047_, 3, v_r_1038_);
lean_ctor_set(v___x_1047_, 2, v_v_944_);
lean_ctor_set(v___x_1047_, 1, v_k_943_);
lean_ctor_set(v___x_1047_, 0, v___x_953_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_r_1038_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_r_1038_);
v___x_1051_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
lean_inc(v_r_1038_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 3, v_r_1038_);
lean_ctor_set(v___x_1042_, 0, v___x_953_);
v___x_1053_ = v___x_1042_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_r_1038_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_r_1038_);
v___x_1053_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v___x_1053_);
lean_ctor_set(v___x_948_, 3, v___x_1051_);
lean_ctor_set(v___x_948_, 2, v_v_1045_);
lean_ctor_set(v___x_948_, 1, v_k_1044_);
lean_ctor_set(v___x_948_, 0, v___x_1049_);
v___x_1055_ = v___x_948_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_v_1045_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
else
{
lean_object* v_r_1066_; 
v_r_1066_ = lean_ctor_get(v_impl_952_, 4);
lean_inc(v_r_1066_);
if (lean_obj_tag(v_r_1066_) == 0)
{
lean_object* v_k_1067_; lean_object* v_v_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_k_1067_ = lean_ctor_get(v_impl_952_, 1);
v_v_1068_ = lean_ctor_get(v_impl_952_, 2);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_impl_952_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; lean_object* v_unused_1082_; 
v_unused_1080_ = lean_ctor_get(v_impl_952_, 4);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_impl_952_, 3);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_impl_952_, 0);
lean_dec(v_unused_1082_);
v___x_1070_ = v_impl_952_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_v_1068_);
lean_inc(v_k_1067_);
lean_dec(v_impl_952_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(3u);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 4, v_l_1037_);
lean_ctor_set(v___x_1070_, 2, v_v_944_);
lean_ctor_set(v___x_1070_, 1, v_k_943_);
lean_ctor_set(v___x_1070_, 0, v___x_953_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_l_1037_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_l_1037_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_r_1066_);
lean_ctor_set(v___x_948_, 3, v___x_1074_);
lean_ctor_set(v___x_948_, 2, v_v_1068_);
lean_ctor_set(v___x_948_, 1, v_k_1067_);
lean_ctor_set(v___x_948_, 0, v___x_1072_);
v___x_1076_ = v___x_948_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_r_1066_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_unsigned_to_nat(2u);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_impl_952_);
lean_ctor_set(v___x_948_, 3, v_r_1066_);
lean_ctor_set(v___x_948_, 0, v___x_1083_);
v___x_1085_ = v___x_948_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_r_1066_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_impl_952_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_v_944_);
lean_dec(v_k_943_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v_v_940_);
lean_ctor_set(v___x_948_, 1, v_k_939_);
v___x_1088_ = v___x_948_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_size_942_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_945_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_r_946_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_impl_1090_; lean_object* v___x_1091_; 
lean_dec(v_size_942_);
v_impl_1090_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_939_, v_v_940_, v_l_945_);
v___x_1091_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_946_) == 0)
{
lean_object* v_size_1092_; lean_object* v_size_1093_; lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v_l_1096_; lean_object* v_r_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_size_1092_ = lean_ctor_get(v_r_946_, 0);
v_size_1093_ = lean_ctor_get(v_impl_1090_, 0);
lean_inc(v_size_1093_);
v_k_1094_ = lean_ctor_get(v_impl_1090_, 1);
lean_inc(v_k_1094_);
v_v_1095_ = lean_ctor_get(v_impl_1090_, 2);
lean_inc(v_v_1095_);
v_l_1096_ = lean_ctor_get(v_impl_1090_, 3);
lean_inc(v_l_1096_);
v_r_1097_ = lean_ctor_get(v_impl_1090_, 4);
lean_inc(v_r_1097_);
v___x_1098_ = lean_unsigned_to_nat(3u);
v___x_1099_ = lean_nat_mul(v___x_1098_, v_size_1092_);
v___x_1100_ = lean_nat_dec_lt(v___x_1099_, v_size_1093_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v_r_1097_);
lean_dec(v_l_1096_);
lean_dec(v_v_1095_);
lean_dec(v_k_1094_);
v___x_1101_ = lean_nat_add(v___x_1091_, v_size_1093_);
lean_dec(v_size_1093_);
v___x_1102_ = lean_nat_add(v___x_1101_, v_size_1092_);
lean_dec(v___x_1101_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 3, v_impl_1090_);
lean_ctor_set(v___x_948_, 0, v___x_1102_);
v___x_1104_ = v___x_948_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_impl_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_r_946_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
else
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1171_; 
v_isSharedCheck_1171_ = !lean_is_exclusive(v_impl_1090_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1172_ = lean_ctor_get(v_impl_1090_, 4);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_impl_1090_, 3);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_impl_1090_, 2);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1090_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1090_, 0);
lean_dec(v_unused_1176_);
v___x_1107_ = v_impl_1090_;
v_isShared_1108_ = v_isSharedCheck_1171_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v_impl_1090_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1171_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_size_1109_; lean_object* v_size_1110_; lean_object* v_k_1111_; lean_object* v_v_1112_; lean_object* v_l_1113_; lean_object* v_r_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_size_1109_ = lean_ctor_get(v_l_1096_, 0);
v_size_1110_ = lean_ctor_get(v_r_1097_, 0);
v_k_1111_ = lean_ctor_get(v_r_1097_, 1);
v_v_1112_ = lean_ctor_get(v_r_1097_, 2);
v_l_1113_ = lean_ctor_get(v_r_1097_, 3);
v_r_1114_ = lean_ctor_get(v_r_1097_, 4);
v___x_1115_ = lean_unsigned_to_nat(2u);
v___x_1116_ = lean_nat_mul(v___x_1115_, v_size_1109_);
v___x_1117_ = lean_nat_dec_lt(v_size_1110_, v___x_1116_);
lean_dec(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1146_; 
lean_inc(v_r_1114_);
lean_inc(v_l_1113_);
lean_inc(v_v_1112_);
lean_inc(v_k_1111_);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_r_1097_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1147_ = lean_ctor_get(v_r_1097_, 4);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_r_1097_, 3);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_1097_, 2);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1097_, 1);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1097_, 0);
lean_dec(v_unused_1151_);
v___x_1119_ = v_r_1097_;
v_isShared_1120_ = v_isSharedCheck_1146_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_r_1097_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1146_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___x_1134_; lean_object* v___y_1136_; 
v___x_1121_ = lean_nat_add(v___x_1091_, v_size_1093_);
lean_dec(v_size_1093_);
v___x_1122_ = lean_nat_add(v___x_1121_, v_size_1092_);
lean_dec(v___x_1121_);
v___x_1134_ = lean_nat_add(v___x_1091_, v_size_1109_);
if (lean_obj_tag(v_l_1113_) == 0)
{
lean_object* v_size_1144_; 
v_size_1144_ = lean_ctor_get(v_l_1113_, 0);
lean_inc(v_size_1144_);
v___y_1136_ = v_size_1144_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___y_1136_ = v___x_1145_;
goto v___jp_1135_;
}
v___jp_1123_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_nat_add(v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec(v___y_1125_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 4, v_r_946_);
lean_ctor_set(v___x_1119_, 3, v_r_1114_);
lean_ctor_set(v___x_1119_, 2, v_v_944_);
lean_ctor_set(v___x_1119_, 1, v_k_943_);
lean_ctor_set(v___x_1119_, 0, v___x_1127_);
v___x_1129_ = v___x_1119_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_r_1114_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_r_946_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 4, v___x_1129_);
lean_ctor_set(v___x_1107_, 3, v___y_1124_);
lean_ctor_set(v___x_1107_, 2, v_v_1112_);
lean_ctor_set(v___x_1107_, 1, v_k_1111_);
lean_ctor_set(v___x_1107_, 0, v___x_1122_);
v___x_1131_ = v___x_1107_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_1111_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v___y_1124_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
v___jp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_nat_add(v___x_1134_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec(v___x_1134_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_l_1113_);
lean_ctor_set(v___x_948_, 3, v_l_1096_);
lean_ctor_set(v___x_948_, 2, v_v_1095_);
lean_ctor_set(v___x_948_, 1, v_k_1094_);
lean_ctor_set(v___x_948_, 0, v___x_1137_);
v___x_1139_ = v___x_948_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_l_1096_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_l_1113_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_nat_add(v___x_1091_, v_size_1092_);
if (lean_obj_tag(v_r_1114_) == 0)
{
lean_object* v_size_1141_; 
v_size_1141_ = lean_ctor_get(v_r_1114_, 0);
lean_inc(v_size_1141_);
v___y_1124_ = v___x_1139_;
v___y_1125_ = v___x_1140_;
v___y_1126_ = v_size_1141_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___y_1124_ = v___x_1139_;
v___y_1125_ = v___x_1140_;
v___y_1126_ = v___x_1142_;
goto v___jp_1123_;
}
}
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_del_object(v___x_948_);
v___x_1152_ = lean_nat_add(v___x_1091_, v_size_1093_);
lean_dec(v_size_1093_);
v___x_1153_ = lean_nat_add(v___x_1152_, v_size_1092_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_nat_add(v___x_1091_, v_size_1092_);
v___x_1155_ = lean_nat_add(v___x_1154_, v_size_1110_);
lean_dec(v___x_1154_);
lean_inc_ref(v_r_946_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 4, v_r_946_);
lean_ctor_set(v___x_1107_, 3, v_r_1097_);
lean_ctor_set(v___x_1107_, 2, v_v_944_);
lean_ctor_set(v___x_1107_, 1, v_k_943_);
lean_ctor_set(v___x_1107_, 0, v___x_1155_);
v___x_1157_ = v___x_1107_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_r_1097_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_946_);
v___x_1157_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_isSharedCheck_1164_ = !lean_is_exclusive(v_r_946_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1165_ = lean_ctor_get(v_r_946_, 4);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_r_946_, 3);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_r_946_, 2);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_946_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_946_, 0);
lean_dec(v_unused_1169_);
v___x_1159_ = v_r_946_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_r_946_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1157_);
lean_ctor_set(v___x_1159_, 3, v_l_1096_);
lean_ctor_set(v___x_1159_, 2, v_v_1095_);
lean_ctor_set(v___x_1159_, 1, v_k_1094_);
lean_ctor_set(v___x_1159_, 0, v___x_1153_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_l_1096_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v___x_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1177_; 
v_l_1177_ = lean_ctor_get(v_impl_1090_, 3);
lean_inc(v_l_1177_);
if (lean_obj_tag(v_l_1177_) == 0)
{
lean_object* v_r_1178_; lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1191_; 
v_r_1178_ = lean_ctor_get(v_impl_1090_, 4);
v_k_1179_ = lean_ctor_get(v_impl_1090_, 1);
v_v_1180_ = lean_ctor_get(v_impl_1090_, 2);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_impl_1090_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; lean_object* v_unused_1193_; 
v_unused_1192_ = lean_ctor_get(v_impl_1090_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1090_, 0);
lean_dec(v_unused_1193_);
v___x_1182_ = v_impl_1090_;
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_r_1178_);
lean_inc(v_v_1180_);
lean_inc(v_k_1179_);
lean_dec(v_impl_1090_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1178_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 3, v_r_1178_);
lean_ctor_set(v___x_1182_, 2, v_v_944_);
lean_ctor_set(v___x_1182_, 1, v_k_943_);
lean_ctor_set(v___x_1182_, 0, v___x_1091_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_r_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_r_1178_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v___x_1186_);
lean_ctor_set(v___x_948_, 3, v_l_1177_);
lean_ctor_set(v___x_948_, 2, v_v_1180_);
lean_ctor_set(v___x_948_, 1, v_k_1179_);
lean_ctor_set(v___x_948_, 0, v___x_1184_);
v___x_1188_ = v___x_948_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_1179_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_1180_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_l_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v___x_1186_);
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
else
{
lean_object* v_r_1194_; 
v_r_1194_ = lean_ctor_get(v_impl_1090_, 4);
lean_inc(v_r_1194_);
if (lean_obj_tag(v_r_1194_) == 0)
{
lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1219_; 
v_k_1195_ = lean_ctor_get(v_impl_1090_, 1);
v_v_1196_ = lean_ctor_get(v_impl_1090_, 2);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_impl_1090_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1220_ = lean_ctor_get(v_impl_1090_, 4);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_impl_1090_, 3);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_impl_1090_, 0);
lean_dec(v_unused_1222_);
v___x_1198_ = v_impl_1090_;
v_isShared_1199_ = v_isSharedCheck_1219_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
lean_dec(v_impl_1090_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1219_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_k_1200_; lean_object* v_v_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1215_; 
v_k_1200_ = lean_ctor_get(v_r_1194_, 1);
v_v_1201_ = lean_ctor_get(v_r_1194_, 2);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_r_1194_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1216_ = lean_ctor_get(v_r_1194_, 4);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_r_1194_, 3);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_r_1194_, 0);
lean_dec(v_unused_1218_);
v___x_1203_ = v_r_1194_;
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_v_1201_);
lean_inc(v_k_1200_);
lean_dec(v_r_1194_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_unsigned_to_nat(3u);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v_l_1177_);
lean_ctor_set(v___x_1203_, 3, v_l_1177_);
lean_ctor_set(v___x_1203_, 2, v_v_1196_);
lean_ctor_set(v___x_1203_, 1, v_k_1195_);
lean_ctor_set(v___x_1203_, 0, v___x_1091_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_l_1177_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_l_1177_);
v___x_1207_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v_l_1177_);
lean_ctor_set(v___x_1198_, 2, v_v_944_);
lean_ctor_set(v___x_1198_, 1, v_k_943_);
lean_ctor_set(v___x_1198_, 0, v___x_1091_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_l_1177_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_l_1177_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v___x_1209_);
lean_ctor_set(v___x_948_, 3, v___x_1207_);
lean_ctor_set(v___x_948_, 2, v_v_1201_);
lean_ctor_set(v___x_948_, 1, v_k_1200_);
lean_ctor_set(v___x_948_, 0, v___x_1205_);
v___x_1211_ = v___x_948_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(2u);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_r_1194_);
lean_ctor_set(v___x_948_, 3, v_impl_1090_);
lean_ctor_set(v___x_948_, 0, v___x_1223_);
v___x_1225_ = v___x_948_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_impl_1090_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_r_1194_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_k_939_);
lean_ctor_set(v___x_1229_, 2, v_v_940_);
lean_ctor_set(v___x_1229_, 3, v_t_941_);
lean_ctor_set(v___x_1229_, 4, v_t_941_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1230_, lean_object* v_b_1231_){
_start:
{
if (lean_obj_tag(v_as_x27_1230_) == 0)
{
return v_b_1231_;
}
else
{
lean_object* v_head_1232_; lean_object* v_tail_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v_r_1236_; 
v_head_1232_ = lean_ctor_get(v_as_x27_1230_, 0);
v_tail_1233_ = lean_ctor_get(v_as_x27_1230_, 1);
v_fst_1234_ = lean_ctor_get(v_head_1232_, 0);
v_snd_1235_ = lean_ctor_get(v_head_1232_, 1);
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
v_r_1236_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1234_, v_snd_1235_, v_b_1231_);
v_as_x27_1230_ = v_tail_1233_;
v_b_1231_ = v_r_1236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1238_, lean_object* v_b_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1238_, v_b_1239_);
lean_dec(v_as_x27_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1249_, lean_object* v_expr_1250_, lean_object* v_lctx_1251_, lean_object* v_location_x3f_1252_, lean_object* v_docString_x3f_1253_, lean_object* v_mkDocString_x3f_1254_, uint8_t v_explicit_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___y_1263_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_fmt_1249_);
v___x_1258_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1259_ = lean_box(0);
v___x_1260_ = 0;
v___x_1261_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1261_, 0, v___x_1258_);
lean_ctor_set(v___x_1261_, 1, v_lctx_1251_);
lean_ctor_set(v___x_1261_, 2, v___x_1259_);
lean_ctor_set(v___x_1261_, 3, v_expr_1250_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*4, v___x_1260_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*4 + 1, v___x_1260_);
if (lean_obj_tag(v_mkDocString_x3f_1254_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1253_) == 0)
{
v___y_1263_ = v_mkDocString_x3f_1254_;
goto v___jp_1262_;
}
else
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
v_val_1273_ = lean_ctor_get(v_docString_x3f_1253_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_docString_x3f_1253_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v_docString_x3f_1253_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v_docString_x3f_1253_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___f_1277_; lean_object* v___x_1279_; 
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1277_, 0, v_val_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___f_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___f_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1263_ = v___x_1279_;
goto v___jp_1262_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1253_);
v___y_1263_ = v_mkDocString_x3f_1254_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_r_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1264_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1261_);
lean_ctor_set(v___x_1264_, 1, v_location_x3f_1252_);
lean_ctor_set(v___x_1264_, 2, v___y_1263_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*3, v_explicit_1255_);
v___x_1265_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1256_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v_r_1269_ = lean_box(1);
v___x_1270_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1268_, v_r_1269_);
lean_dec_ref_known(v___x_1268_, 2);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1257_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1282_, lean_object* v_expr_1283_, lean_object* v_lctx_1284_, lean_object* v_location_x3f_1285_, lean_object* v_docString_x3f_1286_, lean_object* v_mkDocString_x3f_1287_, lean_object* v_explicit_1288_){
_start:
{
uint8_t v_explicit_boxed_1289_; lean_object* v_res_1290_; 
v_explicit_boxed_1289_ = lean_unbox(v_explicit_1288_);
v_res_1290_ = l_Lean_MessageData_withExprHover(v_fmt_1282_, v_expr_1283_, v_lctx_1284_, v_location_x3f_1285_, v_docString_x3f_1286_, v_mkDocString_x3f_1287_, v_explicit_boxed_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1291_, lean_object* v_k_1292_, lean_object* v_v_1293_, lean_object* v_t_1294_, lean_object* v_hl_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1292_, v_v_1293_, v_t_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1297_, lean_object* v_as_x27_1298_, lean_object* v_b_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1298_, v_b_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1302_, lean_object* v_as_x27_1303_, lean_object* v_b_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1302_, v_as_x27_1303_, v_b_1304_, v_a_1305_);
lean_dec(v_as_x27_1303_);
lean_dec(v_as_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1307_, lean_object* v_expr_1308_, lean_object* v_location_x3f_1309_, lean_object* v_docString_x3f_1310_, lean_object* v_mkDocString_x3f_1311_, uint8_t v_explicit_1312_, lean_object* v_toPure_1313_, lean_object* v_lctx_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = l_Lean_MessageData_withExprHover(v_fmt_1307_, v_expr_1308_, v_lctx_1314_, v_location_x3f_1309_, v_docString_x3f_1310_, v_mkDocString_x3f_1311_, v_explicit_1312_);
v___x_1316_ = lean_apply_2(v_toPure_1313_, lean_box(0), v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1317_, lean_object* v_expr_1318_, lean_object* v_location_x3f_1319_, lean_object* v_docString_x3f_1320_, lean_object* v_mkDocString_x3f_1321_, lean_object* v_explicit_1322_, lean_object* v_toPure_1323_, lean_object* v_lctx_1324_){
_start:
{
uint8_t v_explicit_boxed_1325_; lean_object* v_res_1326_; 
v_explicit_boxed_1325_ = lean_unbox(v_explicit_1322_);
v_res_1326_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1317_, v_expr_1318_, v_location_x3f_1319_, v_docString_x3f_1320_, v_mkDocString_x3f_1321_, v_explicit_boxed_1325_, v_toPure_1323_, v_lctx_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_fmt_1329_, lean_object* v_expr_1330_, lean_object* v_lctx_x3f_1331_, lean_object* v_location_x3f_1332_, lean_object* v_docString_x3f_1333_, lean_object* v_mkDocString_x3f_1334_, uint8_t v_explicit_1335_){
_start:
{
lean_object* v_toApplicative_1336_; lean_object* v_toBind_1337_; lean_object* v_toPure_1338_; lean_object* v___x_1339_; lean_object* v___f_1340_; 
v_toApplicative_1336_ = lean_ctor_get(v_inst_1327_, 0);
lean_inc_ref(v_toApplicative_1336_);
v_toBind_1337_ = lean_ctor_get(v_inst_1327_, 1);
lean_inc(v_toBind_1337_);
lean_dec_ref(v_inst_1327_);
v_toPure_1338_ = lean_ctor_get(v_toApplicative_1336_, 1);
lean_inc_n(v_toPure_1338_, 2);
lean_dec_ref(v_toApplicative_1336_);
v___x_1339_ = lean_box(v_explicit_1335_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1340_, 0, v_fmt_1329_);
lean_closure_set(v___f_1340_, 1, v_expr_1330_);
lean_closure_set(v___f_1340_, 2, v_location_x3f_1332_);
lean_closure_set(v___f_1340_, 3, v_docString_x3f_1333_);
lean_closure_set(v___f_1340_, 4, v_mkDocString_x3f_1334_);
lean_closure_set(v___f_1340_, 5, v___x_1339_);
lean_closure_set(v___f_1340_, 6, v_toPure_1338_);
if (lean_obj_tag(v_lctx_x3f_1331_) == 0)
{
lean_object* v___x_1341_; 
lean_dec(v_toPure_1338_);
v___x_1341_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v_inst_1328_, v___f_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_inst_1328_);
v_val_1342_ = lean_ctor_get(v_lctx_x3f_1331_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v_lctx_x3f_1331_, 1);
v___x_1343_ = lean_apply_2(v_toPure_1338_, lean_box(0), v_val_1342_);
v___x_1344_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v___x_1343_, v___f_1340_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_fmt_1347_, lean_object* v_expr_1348_, lean_object* v_lctx_x3f_1349_, lean_object* v_location_x3f_1350_, lean_object* v_docString_x3f_1351_, lean_object* v_mkDocString_x3f_1352_, lean_object* v_explicit_1353_){
_start:
{
uint8_t v_explicit_boxed_1354_; lean_object* v_res_1355_; 
v_explicit_boxed_1354_ = lean_unbox(v_explicit_1353_);
v_res_1355_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1345_, v_inst_1346_, v_fmt_1347_, v_expr_1348_, v_lctx_x3f_1349_, v_location_x3f_1350_, v_docString_x3f_1351_, v_mkDocString_x3f_1352_, v_explicit_boxed_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_fmt_1359_, lean_object* v_expr_1360_, lean_object* v_lctx_x3f_1361_, lean_object* v_location_x3f_1362_, lean_object* v_docString_x3f_1363_, lean_object* v_mkDocString_x3f_1364_, uint8_t v_explicit_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1357_, v_inst_1358_, v_fmt_1359_, v_expr_1360_, v_lctx_x3f_1361_, v_location_x3f_1362_, v_docString_x3f_1363_, v_mkDocString_x3f_1364_, v_explicit_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_fmt_1370_, lean_object* v_expr_1371_, lean_object* v_lctx_x3f_1372_, lean_object* v_location_x3f_1373_, lean_object* v_docString_x3f_1374_, lean_object* v_mkDocString_x3f_1375_, lean_object* v_explicit_1376_){
_start:
{
uint8_t v_explicit_boxed_1377_; lean_object* v_res_1378_; 
v_explicit_boxed_1377_ = lean_unbox(v_explicit_1376_);
v_res_1378_ = l_Lean_MessageData_withExprHoverM(v_m_1367_, v_inst_1368_, v_inst_1369_, v_fmt_1370_, v_expr_1371_, v_lctx_x3f_1372_, v_location_x3f_1373_, v_docString_x3f_1374_, v_mkDocString_x3f_1375_, v_explicit_boxed_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1379_, lean_object* v_display_1380_, lean_object* v_toPure_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_____do__lift_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1384_, v_userName_1379_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
v___x_1386_ = l_Lean_MessageData_ofName(v_display_1380_);
v___x_1387_ = lean_apply_2(v_toPure_1381_, lean_box(0), v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_val_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_toPure_1381_);
v_val_1388_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1390_ = v___x_1385_;
v_isShared_1391_ = v_isSharedCheck_1402_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_val_1388_);
lean_dec(v___x_1385_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1402_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = 1;
v___x_1393_ = l_Lean_Name_toString(v_display_1380_, v___x_1392_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set_tag(v___x_1390_, 3);
lean_ctor_set(v___x_1390_, 0, v___x_1393_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; 
v___x_1396_ = l_Lean_LocalDecl_fvarId(v_val_1388_);
lean_dec(v_val_1388_);
v___x_1397_ = l_Lean_Expr_fvar___override(v___x_1396_);
v___x_1398_ = lean_box(0);
v___x_1399_ = 0;
v___x_1400_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1382_, v_inst_1383_, v___x_1395_, v___x_1397_, v___x_1398_, v___x_1398_, v___x_1398_, v___x_1398_, v___x_1399_);
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1403_, lean_object* v_display_1404_, lean_object* v_toPure_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_____do__lift_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1403_, v_display_1404_, v_toPure_1405_, v_inst_1406_, v_inst_1407_, v_____do__lift_1408_);
lean_dec_ref(v_____do__lift_1408_);
lean_dec(v_userName_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_userName_1412_){
_start:
{
lean_object* v_toApplicative_1413_; lean_object* v_toBind_1414_; lean_object* v_toPure_1415_; lean_object* v_display_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; 
v_toApplicative_1413_ = lean_ctor_get(v_inst_1410_, 0);
v_toBind_1414_ = lean_ctor_get(v_inst_1410_, 1);
lean_inc(v_toBind_1414_);
v_toPure_1415_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_inc(v_toPure_1415_);
lean_inc(v_userName_1412_);
v_display_1416_ = l_Lean_Name_simpMacroScopes(v_userName_1412_);
lean_inc(v_inst_1411_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1417_, 0, v_userName_1412_);
lean_closure_set(v___f_1417_, 1, v_display_1416_);
lean_closure_set(v___f_1417_, 2, v_toPure_1415_);
lean_closure_set(v___f_1417_, 3, v_inst_1410_);
lean_closure_set(v___f_1417_, 4, v_inst_1411_);
v___x_1418_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v_inst_1411_, v___f_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_userName_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1420_, v_inst_1421_, v_userName_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1424_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
lean_ctor_set(v___x_1429_, 3, v___x_1428_);
lean_ctor_set(v___x_1429_, 4, v___x_1427_);
lean_ctor_set(v___x_1429_, 5, v___x_1427_);
lean_ctor_set(v___x_1429_, 6, v___x_1427_);
lean_ctor_set(v___x_1429_, 7, v___x_1427_);
lean_ctor_set(v___x_1429_, 8, v___x_1427_);
lean_ctor_set(v___x_1429_, 9, v___x_1427_);
lean_ctor_set(v___x_1429_, 10, v___x_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1430_, lean_object* v_a_1431_){
_start:
{
switch(lean_obj_tag(v_a_1431_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1430_) == 0)
{
lean_object* v_hasSyntheticSorry_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_hasSyntheticSorry_1432_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_hasSyntheticSorry_1432_);
lean_dec_ref_known(v_a_1431_, 2);
v___x_1433_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1434_ = lean_apply_1(v_hasSyntheticSorry_1432_, v___x_1433_);
v___x_1435_ = lean_unbox(v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v_hasSyntheticSorry_1436_; lean_object* v_val_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_hasSyntheticSorry_1436_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_hasSyntheticSorry_1436_);
lean_dec_ref_known(v_a_1431_, 2);
v_val_1437_ = lean_ctor_get(v_mctx_x3f_1430_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v_mctx_x3f_1430_, 1);
v___x_1438_ = lean_apply_1(v_hasSyntheticSorry_1436_, v_val_1437_);
v___x_1439_ = lean_unbox(v___x_1438_);
return v___x_1439_;
}
}
case 3:
{
lean_object* v_a_1440_; lean_object* v_a_1441_; lean_object* v_mctx_1442_; lean_object* v___x_1443_; 
lean_dec(v_mctx_x3f_1430_);
v_a_1440_ = lean_ctor_get(v_a_1431_, 0);
lean_inc_ref(v_a_1440_);
v_a_1441_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1441_);
lean_dec_ref_known(v_a_1431_, 2);
v_mctx_1442_ = lean_ctor_get(v_a_1440_, 1);
lean_inc_ref(v_mctx_1442_);
lean_dec_ref(v_a_1440_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_mctx_1442_);
v_mctx_x3f_1430_ = v___x_1443_;
v_a_1431_ = v_a_1441_;
goto _start;
}
case 4:
{
lean_object* v_a_1445_; 
v_a_1445_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1445_);
lean_dec_ref_known(v_a_1431_, 2);
v_a_1431_ = v_a_1445_;
goto _start;
}
case 5:
{
lean_object* v_a_1447_; 
v_a_1447_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1447_);
lean_dec_ref_known(v_a_1431_, 2);
v_a_1431_ = v_a_1447_;
goto _start;
}
case 6:
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v_a_1431_, 0);
lean_inc_ref(v_a_1449_);
lean_dec_ref_known(v_a_1431_, 1);
v_a_1431_ = v_a_1449_;
goto _start;
}
case 7:
{
lean_object* v_a_1451_; lean_object* v_a_1452_; uint8_t v___x_1453_; 
v_a_1451_ = lean_ctor_get(v_a_1431_, 0);
lean_inc_ref(v_a_1451_);
v_a_1452_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1452_);
lean_dec_ref_known(v_a_1431_, 2);
lean_inc(v_mctx_x3f_1430_);
v___x_1453_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1430_, v_a_1451_);
if (v___x_1453_ == 0)
{
v_a_1431_ = v_a_1452_;
goto _start;
}
else
{
lean_dec_ref(v_a_1452_);
lean_dec(v_mctx_x3f_1430_);
return v___x_1453_;
}
}
case 8:
{
lean_object* v_a_1455_; 
v_a_1455_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1455_);
lean_dec_ref_known(v_a_1431_, 2);
v_a_1431_ = v_a_1455_;
goto _start;
}
case 11:
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1457_);
lean_dec_ref_known(v_a_1431_, 2);
v_a_1431_ = v_a_1457_;
goto _start;
}
case 12:
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_a_1459_);
lean_dec_ref_known(v_a_1431_, 2);
v_a_1431_ = v_a_1459_;
goto _start;
}
case 9:
{
lean_object* v_msg_1461_; lean_object* v_children_1462_; uint8_t v___x_1463_; 
v_msg_1461_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_msg_1461_);
v_children_1462_ = lean_ctor_get(v_a_1431_, 2);
lean_inc_ref(v_children_1462_);
lean_dec_ref_known(v_a_1431_, 3);
lean_inc(v_mctx_x3f_1430_);
v___x_1463_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1430_, v_msg_1461_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_array_get_size(v_children_1462_);
v___x_1466_ = lean_nat_dec_lt(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v_children_1462_);
lean_dec(v_mctx_x3f_1430_);
return v___x_1463_;
}
else
{
if (v___x_1466_ == 0)
{
lean_dec_ref(v_children_1462_);
lean_dec(v_mctx_x3f_1430_);
return v___x_1463_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1465_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1430_, v_children_1462_, v___x_1467_, v___x_1468_);
lean_dec_ref(v_children_1462_);
return v___x_1469_;
}
}
}
else
{
lean_dec_ref(v_children_1462_);
lean_dec(v_mctx_x3f_1430_);
return v___x_1463_;
}
}
default: 
{
uint8_t v___x_1470_; 
lean_dec_ref(v_a_1431_);
lean_dec(v_mctx_x3f_1430_);
v___x_1470_ = 0;
return v___x_1470_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1471_, lean_object* v_as_1472_, size_t v_i_1473_, size_t v_stop_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_usize_dec_eq(v_i_1473_, v_stop_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_array_uget_borrowed(v_as_1472_, v_i_1473_);
lean_inc(v___x_1476_);
lean_inc(v_mctx_x3f_1471_);
v___x_1477_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1471_, v___x_1476_);
if (v___x_1477_ == 0)
{
size_t v___x_1478_; size_t v___x_1479_; 
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_add(v_i_1473_, v___x_1478_);
v_i_1473_ = v___x_1479_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1471_);
return v___x_1477_;
}
}
else
{
uint8_t v___x_1481_; 
lean_dec(v_mctx_x3f_1471_);
v___x_1481_ = 0;
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1482_, lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_){
_start:
{
size_t v_i_boxed_1486_; size_t v_stop_boxed_1487_; uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_i_boxed_1486_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1487_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1482_, v_as_1483_, v_i_boxed_1486_, v_stop_boxed_1487_);
lean_dec_ref(v_as_1483_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1490_, lean_object* v_a_1491_){
_start:
{
uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_res_1492_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1490_, v_a_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1494_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1495_, v_msg_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1497_){
_start:
{
uint8_t v_res_1498_; lean_object* v_r_1499_; 
v_res_1498_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1497_);
v_r_1499_ = lean_box(v_res_1498_);
return v_r_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(lean_object* v_name_1500_, lean_object* v_decl_1501_, lean_object* v_ref_1502_){
_start:
{
lean_object* v_defValue_1504_; lean_object* v_descr_1505_; lean_object* v_deprecation_x3f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_defValue_1504_ = lean_ctor_get(v_decl_1501_, 0);
v_descr_1505_ = lean_ctor_get(v_decl_1501_, 1);
v_deprecation_x3f_1506_ = lean_ctor_get(v_decl_1501_, 2);
lean_inc(v_defValue_1504_);
v___x_1507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_defValue_1504_);
lean_inc(v_deprecation_x3f_1506_);
lean_inc_ref(v_descr_1505_);
lean_inc_n(v_name_1500_, 2);
v___x_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1508_, 0, v_name_1500_);
lean_ctor_set(v___x_1508_, 1, v_ref_1502_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set(v___x_1508_, 3, v_descr_1505_);
lean_ctor_set(v___x_1508_, 4, v_deprecation_x3f_1506_);
v___x_1509_ = lean_register_option(v_name_1500_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1509_, 0);
lean_dec(v_unused_1518_);
v___x_1511_ = v___x_1509_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v___x_1509_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_inc(v_defValue_1504_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_name_1500_);
lean_ctor_set(v___x_1513_, 1, v_defValue_1504_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_name_1500_);
v_a_1519_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1509_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1509_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1527_, lean_object* v_decl_1528_, lean_object* v_ref_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v_name_1527_, v_decl_1528_, v_ref_1529_);
lean_dec_ref(v_decl_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1546_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1547_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_));
v___x_1548_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4__spec__0(v___x_1545_, v___x_1546_, v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4____boxed(lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1084813479____hygCtx___hyg_4_();
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_nat_to_int(v_a_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = l_instMonadBaseIO;
v___x_1555_ = l_instInhabitedOfMonad___redArg(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_2233__overap_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_2233__overap_1559_ = lean_panic_fn_borrowed(v___x_1558_, v_msg_1556_);
v___x_1560_ = lean_apply_1(v___x_2233__overap_1559_, lean_box(0));
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_dec(v_x_1564_);
return v_x_1565_;
}
else
{
lean_object* v_head_1567_; lean_object* v_tail_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1577_; 
v_head_1567_ = lean_ctor_get(v_x_1566_, 0);
v_tail_1568_ = lean_ctor_get(v_x_1566_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1570_ = v_x_1566_;
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_tail_1568_);
lean_inc(v_head_1567_);
lean_dec(v_x_1566_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1577_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
lean_inc(v_x_1564_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 5);
lean_ctor_set(v___x_1570_, 1, v_x_1564_);
lean_ctor_set(v___x_1570_, 0, v_x_1565_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_x_1565_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_x_1564_);
v___x_1573_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_head_1567_);
v_x_1565_ = v___x_1574_;
v_x_1566_ = v_tail_1568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1578_) == 0)
{
lean_object* v___x_1580_; 
lean_dec(v_x_1579_);
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v_tail_1581_; 
v_tail_1581_ = lean_ctor_get(v_x_1578_, 1);
if (lean_obj_tag(v_tail_1581_) == 0)
{
lean_object* v_head_1582_; 
lean_dec(v_x_1579_);
v_head_1582_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_head_1582_);
lean_dec_ref_known(v_x_1578_, 2);
return v_head_1582_;
}
else
{
lean_object* v_head_1583_; lean_object* v___x_1584_; 
lean_inc(v_tail_1581_);
v_head_1583_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_head_1583_);
lean_dec_ref_known(v_x_1578_, 2);
v___x_1584_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1579_, v_head_1583_, v_tail_1581_);
return v___x_1584_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1599_; double v___x_1600_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_float_of_nat(v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
switch(lean_obj_tag(v_x_1606_))
{
case 0:
{
lean_object* v_a_1608_; lean_object* v_fmt_1609_; 
lean_dec(v_x_1605_);
lean_dec_ref(v_x_1604_);
v_a_1608_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_a_1608_);
lean_dec_ref_known(v_x_1606_, 1);
v_fmt_1609_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_fmt_1609_);
lean_dec_ref(v_a_1608_);
return v_fmt_1609_;
}
case 1:
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v_x_1604_);
v_a_1610_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v_x_1606_, 1);
v___x_1611_ = l_Lean_formatRawGoal(v_a_1610_);
return v___x_1611_;
}
else
{
lean_object* v_a_1612_; lean_object* v_val_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_a_1612_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v_x_1606_, 1);
v_val_1613_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v_x_1605_, 1);
v___x_1614_ = l_Lean_MessageData_mkPPContext(v_x_1604_, v_val_1613_);
lean_dec(v_val_1613_);
lean_dec_ref(v_x_1604_);
v___x_1615_ = l_Lean_ppGoal(v___x_1614_, v_a_1612_);
return v___x_1615_;
}
}
case 3:
{
lean_object* v_a_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; 
lean_dec(v_x_1605_);
v_a_1616_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_a_1616_);
v_a_1617_ = lean_ctor_get(v_x_1606_, 1);
lean_inc_ref(v_a_1617_);
lean_dec_ref_known(v_x_1606_, 2);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_a_1616_);
v_x_1605_ = v___x_1618_;
v_x_1606_ = v_a_1617_;
goto _start;
}
case 4:
{
lean_object* v_a_1620_; lean_object* v_a_1621_; 
lean_dec_ref(v_x_1604_);
v_a_1620_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_a_1620_);
v_a_1621_ = lean_ctor_get(v_x_1606_, 1);
lean_inc_ref(v_a_1621_);
lean_dec_ref_known(v_x_1606_, 2);
v_x_1604_ = v_a_1620_;
v_x_1606_ = v_a_1621_;
goto _start;
}
case 5:
{
lean_object* v_a_1623_; lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1633_; 
v_a_1623_ = lean_ctor_get(v_x_1606_, 0);
v_a_1624_ = lean_ctor_get(v_x_1606_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1606_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1626_ = v_x_1606_;
v_isShared_1627_ = v_isSharedCheck_1633_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_inc(v_a_1623_);
lean_dec(v_x_1606_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1633_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1628_ = l_Lean_MessageData_formatAux(v_x_1604_, v_x_1605_, v_a_1624_);
v___x_1629_ = lean_nat_to_int(v_a_1623_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 4);
lean_ctor_set(v___x_1626_, 1, v___x_1628_);
lean_ctor_set(v___x_1626_, 0, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1628_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
case 6:
{
lean_object* v_a_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_a_1634_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_a_1634_);
lean_dec_ref_known(v_x_1606_, 1);
v___x_1635_ = l_Lean_MessageData_formatAux(v_x_1604_, v_x_1605_, v_a_1634_);
v___x_1636_ = 0;
v___x_1637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*1, v___x_1636_);
return v___x_1637_;
}
case 7:
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1648_; 
v_a_1638_ = lean_ctor_get(v_x_1606_, 0);
v_a_1639_ = lean_ctor_get(v_x_1606_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1606_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1641_ = v_x_1606_;
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_inc(v_a_1638_);
lean_dec(v_x_1606_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1648_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
lean_inc(v_x_1605_);
lean_inc_ref(v_x_1604_);
v___x_1643_ = l_Lean_MessageData_formatAux(v_x_1604_, v_x_1605_, v_a_1638_);
v___x_1644_ = l_Lean_MessageData_formatAux(v_x_1604_, v_x_1605_, v_a_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 5);
lean_ctor_set(v___x_1641_, 1, v___x_1644_);
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1646_ = v___x_1641_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
case 9:
{
lean_object* v_data_1649_; lean_object* v_msg_1650_; lean_object* v_children_1651_; size_t v_sz_1652_; size_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v_cls_1668_; lean_object* v_result_x3f_1669_; double v_startTime_1670_; double v_stopTime_1671_; lean_object* v_msg_1673_; uint8_t v___x_1688_; 
v_data_1649_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_data_1649_);
v_msg_1650_ = lean_ctor_get(v_x_1606_, 1);
lean_inc_ref(v_msg_1650_);
v_children_1651_ = lean_ctor_get(v_x_1606_, 2);
lean_inc_ref(v_children_1651_);
lean_dec_ref_known(v_x_1606_, 3);
v_sz_1652_ = lean_array_size(v_children_1651_);
v___x_1653_ = ((size_t)0ULL);
lean_inc(v_x_1605_);
lean_inc_ref(v_x_1604_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1604_, v_x_1605_, v_sz_1652_, v___x_1653_, v_children_1651_);
v_cls_1668_ = lean_ctor_get(v_data_1649_, 0);
lean_inc(v_cls_1668_);
v_result_x3f_1669_ = lean_ctor_get(v_data_1649_, 1);
lean_inc(v_result_x3f_1669_);
v_startTime_1670_ = lean_ctor_get_float(v_data_1649_, sizeof(void*)*3);
v_stopTime_1671_ = lean_ctor_get_float(v_data_1649_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1649_);
v___x_1688_ = l_Lean_Name_isAnonymous(v_cls_1668_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; double v___x_1704_; uint8_t v___x_1705_; 
v___x_1689_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1690_ = 1;
v___x_1691_ = l_Lean_Name_toString(v_cls_1668_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1689_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1704_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1705_ = lean_float_beq(v_startTime_1670_, v___x_1704_);
if (v___x_1705_ == 0)
{
goto v___jp_1696_;
}
else
{
if (v___x_1688_ == 0)
{
v_msg_1673_ = v___x_1695_;
goto v___jp_1672_;
}
else
{
goto v___jp_1696_;
}
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; double v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1697_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_float_sub(v_stopTime_1671_, v_startTime_1670_);
v___x_1700_ = lean_float_to_string(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1698_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1694_);
v_msg_1673_ = v___x_1703_;
goto v___jp_1672_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v_result_x3f_1669_);
lean_dec(v_cls_1668_);
lean_dec_ref(v_msg_1650_);
lean_dec(v_x_1605_);
lean_dec_ref(v_x_1604_);
v___x_1706_ = lean_array_to_list(v___x_1654_);
v___x_1707_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1708_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1706_, v___x_1707_);
return v___x_1708_;
}
v___jp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1658_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___y_1656_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___y_1657_);
v___x_1662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1659_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_array_to_list(v___x_1654_);
v___x_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1666_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1664_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1660_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
return v___x_1667_;
}
v___jp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_MessageData_formatAux(v_x_1604_, v_x_1605_, v_msg_1650_);
if (lean_obj_tag(v_result_x3f_1669_) == 0)
{
v___y_1656_ = v_msg_1673_;
v___y_1657_ = v___x_1674_;
goto v___jp_1655_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1687_; 
v_val_1675_ = lean_ctor_get(v_result_x3f_1669_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_result_x3f_1669_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1677_ = v_result_x3f_1669_;
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_val_1675_);
lean_dec(v_result_x3f_1669_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_unbox(v_val_1675_);
lean_dec(v_val_1675_);
v___x_1680_ = l_Lean_TraceResult_toEmoji(v___x_1679_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 3);
lean_ctor_set(v___x_1677_, 0, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1674_);
v___y_1656_ = v_msg_1673_;
v___y_1657_ = v___x_1685_;
goto v___jp_1655_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1709_; lean_object* v___x_1710_; lean_object* v___y_1712_; 
v_f_1709_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_f_1709_);
lean_dec_ref_known(v_x_1606_, 2);
v___x_1710_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_box(0);
v___y_1712_ = v___x_1728_;
goto v___jp_1711_;
}
else
{
lean_object* v_val_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_val_1729_ = lean_ctor_get(v_x_1605_, 0);
v___x_1730_ = l_Lean_MessageData_mkPPContext(v_x_1604_, v_val_1729_);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
v___y_1712_ = v___x_1731_;
goto v___jp_1711_;
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_apply_2(v_f_1709_, v___y_1712_, lean_box(0));
v___x_1714_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1713_, v___x_1710_);
if (lean_obj_tag(v___x_1714_) == 1)
{
lean_object* v_val_1715_; 
lean_dec(v___x_1713_);
v_val_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_x_1606_ = v_val_1715_;
goto _start;
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v___x_1714_);
lean_dec(v_x_1605_);
lean_dec_ref(v_x_1604_);
v___x_1717_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1718_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1719_ = lean_unsigned_to_nat(434u);
v___x_1720_ = lean_unsigned_to_nat(8u);
v___x_1721_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1722_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1713_);
lean_dec(v___x_1713_);
v___x_1723_ = 1;
v___x_1724_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1722_, v___x_1723_);
v___x_1725_ = lean_string_append(v___x_1721_, v___x_1724_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l_mkPanicMessageWithDecl(v___x_1717_, v___x_1718_, v___x_1719_, v___x_1720_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1726_);
return v___x_1727_;
}
}
}
default: 
{
lean_object* v_a_1732_; 
v_a_1732_ = lean_ctor_get(v_x_1606_, 1);
lean_inc_ref(v_a_1732_);
lean_dec_ref(v_x_1606_);
v_x_1606_ = v_a_1732_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1734_, lean_object* v_x_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_bs_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1740_ == 0)
{
lean_dec(v_x_1735_);
lean_dec_ref(v_x_1734_);
return v_bs_1738_;
}
else
{
lean_object* v_v_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_bs_x27_1744_; size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v_v_1741_ = lean_array_uget_borrowed(v_bs_1738_, v_i_1737_);
lean_inc(v_v_1741_);
lean_inc(v_x_1735_);
lean_inc_ref(v_x_1734_);
v___x_1742_ = l_Lean_MessageData_formatAux(v_x_1734_, v_x_1735_, v_v_1741_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v_bs_x27_1744_ = lean_array_uset(v_bs_1738_, v_i_1737_, v___x_1743_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1737_, v___x_1745_);
v___x_1747_ = lean_array_uset(v_bs_x27_1744_, v_i_1737_, v___x_1742_);
v_i_1737_ = v___x_1746_;
v_bs_1738_ = v___x_1747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_sz_1751_, lean_object* v_i_1752_, lean_object* v_bs_1753_, lean_object* v___y_1754_){
_start:
{
size_t v_sz_boxed_1755_; size_t v_i_boxed_1756_; lean_object* v_res_1757_; 
v_sz_boxed_1755_ = lean_unbox_usize(v_sz_1751_);
lean_dec(v_sz_1751_);
v_i_boxed_1756_ = lean_unbox_usize(v_i_1752_);
lean_dec(v_i_1752_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1749_, v_x_1750_, v_sz_boxed_1755_, v_i_boxed_1756_, v_bs_1753_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_MessageData_formatAux(v_x_1758_, v_x_1759_, v_x_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1766_, lean_object* v_ctx_x3f_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1770_ = l_Lean_MessageData_formatAux(v___x_1769_, v_ctx_x3f_1767_, v_msgData_1766_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1771_, lean_object* v_ctx_x3f_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_MessageData_format(v_msgData_1771_, v_ctx_x3f_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_MessageData_format(v_msgData_1775_, v___x_1777_);
v___x_1779_ = l_Std_Format_defWidth;
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = l_Std_Format_pretty(v___x_1778_, v___x_1779_, v___x_1780_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_MessageData_toString(v_msgData_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1785_);
lean_ctor_set(v___x_1787_, 1, v_a_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_s_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1815_ = l_Lean_MessageData_ofFormat(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1816_){
_start:
{
if (lean_obj_tag(v_o_1816_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1817_;
}
else
{
lean_object* v_val_1818_; lean_object* v___x_1819_; 
v_val_1818_ = lean_ctor_get(v_o_1816_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v_o_1816_, 1);
v___x_1819_ = l_Lean_MessageData_ofExpr(v_val_1818_);
return v___x_1819_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1823_ = l_Lean_MessageData_ofFormat(v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1828_ = l_Lean_MessageData_ofFormat(v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1829_, lean_object* v_i_1830_, lean_object* v_acc_1831_){
_start:
{
lean_object* v___y_1833_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_array_get_size(v_es_1829_);
v___x_1838_ = lean_nat_dec_lt(v_i_1830_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_i_1830_);
v___x_1839_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_acc_1831_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
return v___x_1840_;
}
else
{
lean_object* v_e_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_e_1841_ = lean_array_fget_borrowed(v_es_1829_, v_i_1830_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_eq(v_i_1830_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1844_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_acc_1831_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_inc(v_e_1841_);
v___x_1846_ = l_Lean_MessageData_ofExpr(v_e_1841_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___y_1833_ = v___x_1847_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_inc(v_e_1841_);
v___x_1848_ = l_Lean_MessageData_ofExpr(v_e_1841_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_acc_1831_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___y_1833_ = v___x_1849_;
goto v___jp_1832_;
}
}
v___jp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_add(v_i_1830_, v___x_1834_);
lean_dec(v_i_1830_);
v_i_1830_ = v___x_1835_;
v_acc_1831_ = v___y_1833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1850_, lean_object* v_i_1851_, lean_object* v_acc_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1850_, v_i_1851_, v_acc_1852_);
lean_dec_ref(v_es_1850_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1858_ = l_Lean_MessageData_ofFormat(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1862_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1859_, v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1863_);
lean_dec_ref(v_es_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1867_, lean_object* v_f_1868_, lean_object* v_r_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1870_ = lean_string_length(v_l_1867_);
v___x_1871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_l_1867_);
v___x_1872_ = l_Lean_MessageData_ofFormat(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v_f_1868_);
v___x_1874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_r_1869_);
v___x_1875_ = l_Lean_MessageData_ofFormat(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1870_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1881_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1882_ = l_Lean_MessageData_bracket(v___x_1880_, v_f_1879_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1883_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1885_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1886_ = l_Lean_MessageData_bracket(v___x_1884_, v_f_1883_, v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v___x_1889_; 
lean_dec_ref(v_x_1888_);
v___x_1889_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1889_;
}
else
{
lean_object* v_tail_1890_; 
v_tail_1890_ = lean_ctor_get(v_x_1887_, 1);
if (lean_obj_tag(v_tail_1890_) == 0)
{
lean_object* v_head_1891_; 
lean_dec_ref(v_x_1888_);
v_head_1891_ = lean_ctor_get(v_x_1887_, 0);
lean_inc(v_head_1891_);
lean_dec_ref_known(v_x_1887_, 2);
return v_head_1891_;
}
else
{
lean_object* v_head_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
lean_inc(v_tail_1890_);
v_head_1892_ = lean_ctor_get(v_x_1887_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_x_1887_, 1);
lean_dec(v_unused_1902_);
v___x_1894_ = v_x_1887_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_head_1892_);
lean_dec(v_x_1887_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
lean_inc_ref(v_x_1888_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 7);
lean_ctor_set(v___x_1894_, 1, v_x_1888_);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_head_1892_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_x_1888_);
v___x_1897_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = l_Lean_MessageData_joinSep(v_tail_1890_, v_x_1888_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
return v___x_1899_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1907_ = l_Lean_MessageData_ofFormat(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1912_ = l_Lean_MessageData_ofFormat(v___x_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_box(1);
v___x_1914_ = l_Lean_MessageData_ofFormat(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1916_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1918_){
_start:
{
if (lean_obj_tag(v_x_1918_) == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1921_ = l_Lean_MessageData_joinSep(v_x_1918_, v___x_1920_);
v___x_1922_ = l_Lean_MessageData_sbracket(v___x_1921_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1923_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_array_to_list(v_msgs_1923_);
v___x_1925_ = l_Lean_MessageData_ofList(v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1930_ = l_Lean_MessageData_ofFormat(v___x_1929_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1935_ = l_Lean_MessageData_ofFormat(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1941_){
_start:
{
if (lean_obj_tag(v_xs_1941_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1942_;
}
else
{
lean_object* v_tail_1943_; 
v_tail_1943_ = lean_ctor_get(v_xs_1941_, 1);
lean_inc(v_tail_1943_);
if (lean_obj_tag(v_tail_1943_) == 0)
{
lean_object* v_head_1944_; 
v_head_1944_ = lean_ctor_get(v_xs_1941_, 0);
lean_inc(v_head_1944_);
lean_dec_ref_known(v_xs_1941_, 2);
return v_head_1944_;
}
else
{
lean_object* v_tail_1945_; 
v_tail_1945_ = lean_ctor_get(v_tail_1943_, 1);
if (lean_obj_tag(v_tail_1945_) == 0)
{
lean_object* v_head_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1963_; 
v_head_1946_ = lean_ctor_get(v_xs_1941_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_xs_1941_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_xs_1941_, 1);
lean_dec(v_unused_1964_);
v___x_1948_ = v_xs_1941_;
v_isShared_1949_ = v_isSharedCheck_1963_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_head_1946_);
lean_dec(v_xs_1941_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1963_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_head_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1961_; 
v_head_1950_ = lean_ctor_get(v_tail_1943_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_tail_1943_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v_tail_1943_, 1);
lean_dec(v_unused_1962_);
v___x_1952_ = v_tail_1943_;
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_head_1950_);
lean_dec(v_tail_1943_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 7);
lean_ctor_set(v___x_1952_, 1, v___x_1954_);
lean_ctor_set(v___x_1952_, 0, v_head_1946_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_head_1946_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 7);
lean_ctor_set(v___x_1948_, 1, v_head_1950_);
lean_ctor_set(v___x_1948_, 0, v___x_1956_);
v___x_1958_ = v___x_1948_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_head_1950_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1988_; 
v_isSharedCheck_1988_ = !lean_is_exclusive(v_tail_1943_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; lean_object* v_unused_1990_; 
v_unused_1989_ = lean_ctor_get(v_tail_1943_, 1);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_tail_1943_, 0);
lean_dec(v_unused_1990_);
v___x_1966_ = v_tail_1943_;
v_isShared_1967_ = v_isSharedCheck_1988_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v_tail_1943_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1988_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1968_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1941_);
v___x_1969_ = lean_array_mk(v_xs_1941_);
v___x_1970_ = lean_array_pop(v___x_1969_);
v___x_1971_ = lean_array_to_list(v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1973_ = l_Lean_MessageData_joinSep(v___x_1971_, v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 7);
lean_ctor_set(v___x_1966_, 1, v___x_1974_);
lean_ctor_set(v___x_1966_, 0, v___x_1973_);
v___x_1976_ = v___x_1966_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v___x_1977_ = l_List_getLast_x21___redArg(v___x_1968_, v_xs_1941_);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_xs_1941_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1985_ = lean_ctor_get(v_xs_1941_, 1);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_xs_1941_, 0);
lean_dec(v_unused_1986_);
v___x_1979_ = v_xs_1941_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_xs_1941_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 7);
lean_ctor_set(v___x_1979_, 1, v___x_1977_);
lean_ctor_set(v___x_1979_, 0, v___x_1976_);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
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
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1995_ = l_Lean_MessageData_ofFormat(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_2000_ = l_Lean_MessageData_ofFormat(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_2001_){
_start:
{
if (lean_obj_tag(v_xs_2001_) == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_2002_;
}
else
{
lean_object* v_tail_2003_; 
v_tail_2003_ = lean_ctor_get(v_xs_2001_, 1);
lean_inc(v_tail_2003_);
if (lean_obj_tag(v_tail_2003_) == 0)
{
lean_object* v_head_2004_; 
v_head_2004_ = lean_ctor_get(v_xs_2001_, 0);
lean_inc(v_head_2004_);
lean_dec_ref_known(v_xs_2001_, 2);
return v_head_2004_;
}
else
{
lean_object* v_tail_2005_; 
v_tail_2005_ = lean_ctor_get(v_tail_2003_, 1);
if (lean_obj_tag(v_tail_2005_) == 0)
{
lean_object* v_head_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2023_; 
v_head_2006_ = lean_ctor_get(v_xs_2001_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_xs_2001_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_xs_2001_, 1);
lean_dec(v_unused_2024_);
v___x_2008_ = v_xs_2001_;
v_isShared_2009_ = v_isSharedCheck_2023_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_head_2006_);
lean_dec(v_xs_2001_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2023_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_head_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2021_; 
v_head_2010_ = lean_ctor_get(v_tail_2003_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_tail_2003_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v_tail_2003_, 1);
lean_dec(v_unused_2022_);
v___x_2012_ = v_tail_2003_;
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_head_2010_);
lean_dec(v_tail_2003_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 7);
lean_ctor_set(v___x_2012_, 1, v___x_2014_);
lean_ctor_set(v___x_2012_, 0, v_head_2006_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_head_2006_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 7);
lean_ctor_set(v___x_2008_, 1, v_head_2010_);
lean_ctor_set(v___x_2008_, 0, v___x_2016_);
v___x_2018_ = v___x_2008_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_head_2010_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2048_; 
v_isSharedCheck_2048_ = !lean_is_exclusive(v_tail_2003_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2049_ = lean_ctor_get(v_tail_2003_, 1);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_tail_2003_, 0);
lean_dec(v_unused_2050_);
v___x_2026_ = v_tail_2003_;
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v_tail_2003_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2048_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2028_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_2001_);
v___x_2029_ = lean_array_mk(v_xs_2001_);
v___x_2030_ = lean_array_pop(v___x_2029_);
v___x_2031_ = lean_array_to_list(v___x_2030_);
v___x_2032_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_2033_ = l_Lean_MessageData_joinSep(v___x_2031_, v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 7);
lean_ctor_set(v___x_2026_, 1, v___x_2034_);
lean_ctor_set(v___x_2026_, 0, v___x_2033_);
v___x_2036_ = v___x_2026_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v___x_2037_ = l_List_getLast_x21___redArg(v___x_2028_, v_xs_2001_);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_xs_2001_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2045_ = lean_ctor_get(v_xs_2001_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_xs_2001_, 0);
lean_dec(v_unused_2046_);
v___x_2039_ = v_xs_2001_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v_xs_2001_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 7);
lean_ctor_set(v___x_2039_, 1, v___x_2037_);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
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
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2057_ = l_Lean_MessageData_ofFormat(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2059_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___x_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2061_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_note_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2068_ = l_Lean_MessageData_ofFormat(v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2070_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_hint_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2078_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2079_ = lean_box(0);
v___x_2080_ = l_List_mapTR_loop___redArg(v___x_2078_, v_es_2077_, v___x_2079_);
v___x_2081_ = l_Lean_MessageData_ofList(v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2086_ = l_Lean_instInhabitedPosition_default;
v___x_2087_ = lean_box(0);
v___x_2088_ = 0;
v___x_2089_ = 2;
v___x_2090_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
lean_ctor_set(v___x_2090_, 1, v___x_2086_);
lean_ctor_set(v___x_2090_, 2, v___x_2087_);
lean_ctor_set(v___x_2090_, 3, v___x_2085_);
lean_ctor_set(v___x_2090_, 4, v_inst_2084_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*5, v___x_2088_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*5 + 1, v___x_2089_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*5 + 2, v___x_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2091_, lean_object* v_inst_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2096_, lean_object* v_inst_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2111_, lean_object* v_x_2112_){
_start:
{
lean_object* v_fileName_2113_; lean_object* v_pos_2114_; lean_object* v_endPos_2115_; uint8_t v_keepFullRange_2116_; uint8_t v_severity_2117_; uint8_t v_isSilent_2118_; lean_object* v_caption_2119_; lean_object* v_data_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_fileName_2113_ = lean_ctor_get(v_x_2112_, 0);
lean_inc_ref(v_fileName_2113_);
v_pos_2114_ = lean_ctor_get(v_x_2112_, 1);
lean_inc_ref(v_pos_2114_);
v_endPos_2115_ = lean_ctor_get(v_x_2112_, 2);
lean_inc(v_endPos_2115_);
v_keepFullRange_2116_ = lean_ctor_get_uint8(v_x_2112_, sizeof(void*)*5);
v_severity_2117_ = lean_ctor_get_uint8(v_x_2112_, sizeof(void*)*5 + 1);
v_isSilent_2118_ = lean_ctor_get_uint8(v_x_2112_, sizeof(void*)*5 + 2);
v_caption_2119_ = lean_ctor_get(v_x_2112_, 3);
lean_inc_ref(v_caption_2119_);
v_data_2120_ = lean_ctor_get(v_x_2112_, 4);
lean_inc(v_data_2120_);
lean_dec_ref(v_x_2112_);
v___x_2121_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2122_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_fileName_2113_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2128_ = l_Lean_instToJsonPosition_toJson(v_pos_2114_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2125_);
v___x_2131_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2132_ = l_Lean_Option_toJson___redArg(v___x_2121_, v_endPos_2115_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2125_);
v___x_2135_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2136_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2136_, 0, v_keepFullRange_2116_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_2125_);
v___x_2139_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2140_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2117_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2125_);
v___x_2143_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2144_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2144_, 0, v_isSilent_2118_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v___x_2125_);
v___x_2147_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_caption_2119_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___x_2125_);
v___x_2151_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2152_ = lean_apply_1(v_inst_2111_, v_data_2120_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___x_2125_);
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___x_2125_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2150_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2146_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2142_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2138_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2134_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2130_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2126_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2164_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2165_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2163_, v___x_2162_, v___x_2164_);
v___x_2166_ = l_Lean_Json_mkObj(v___x_2165_);
lean_dec(v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2167_, lean_object* v_inst_2168_, lean_object* v_x_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2168_, v_x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2172_, 0, lean_box(0));
lean_closure_set(v___x_2172_, 1, v_inst_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2173_, lean_object* v_inst_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2175_, 0, lean_box(0));
lean_closure_set(v___x_2175_, 1, v_inst_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = 1;
v___x_2182_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2183_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2186_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2187_ = lean_string_append(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = 1;
v___x_2191_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2194_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2195_ = lean_string_append(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2198_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2199_ = lean_string_append(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = 1;
v___x_2206_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2209_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2210_ = lean_string_append(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2212_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2213_ = lean_string_append(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = 1;
v___x_2217_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2220_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2221_ = lean_string_append(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2223_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2224_ = lean_string_append(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = 1;
v___x_2229_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2230_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2229_, v___x_2228_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2232_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2233_ = lean_string_append(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2235_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2236_ = lean_string_append(v___x_2235_, v___x_2234_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = 1;
v___x_2240_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2240_, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2243_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2244_ = lean_string_append(v___x_2243_, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2246_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2247_ = lean_string_append(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = 1;
v___x_2251_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2251_, v___x_2250_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2254_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2255_ = lean_string_append(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2257_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2258_ = lean_string_append(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = 1;
v___x_2262_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2262_, v___x_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2265_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2266_ = lean_string_append(v___x_2265_, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2268_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2269_ = lean_string_append(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = 1;
v___x_2273_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2274_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2276_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2277_ = lean_string_append(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2279_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2280_ = lean_string_append(v___x_2279_, v___x_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2281_, lean_object* v_json_2282_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2284_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2282_);
v___x_2285_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2283_, v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2290_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2291_ = lean_string_append(v___x_2290_, v_a_2286_);
lean_dec(v_a_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
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
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2296_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2285_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2285_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set_tag(v___x_2298_, 0);
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2304_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2305_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2306_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2307_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2282_);
v___x_2308_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2305_, v___x_2307_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2314_ = lean_string_append(v___x_2313_, v_a_2309_);
lean_dec(v_a_2309_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2314_);
v___x_2316_ = v___x_2311_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
else
{
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2319_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2308_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2308_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2327_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2328_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2282_);
v___x_2329_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2306_, v___x_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2339_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2335_ = lean_string_append(v___x_2334_, v_a_2330_);
lean_dec(v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2340_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2329_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2329_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 0);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2348_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2349_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2350_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2282_);
v___x_2351_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2349_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2357_ = lean_string_append(v___x_2356_, v_a_2352_);
lean_dec(v_a_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2362_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2351_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2351_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 0);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2370_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2371_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2372_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2282_);
v___x_2373_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2371_, v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2383_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2383_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2378_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2379_ = lean_string_append(v___x_2378_, v_a_2374_);
lean_dec(v_a_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2379_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
else
{
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2384_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2373_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2373_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set_tag(v___x_2386_, 0);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_a_2392_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2393_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2282_);
v___x_2394_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2349_, v___x_2393_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2404_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2404_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2399_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2400_ = lean_string_append(v___x_2399_, v_a_2395_);
lean_dec(v_a_2395_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2400_);
v___x_2402_ = v___x_2397_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
else
{
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2405_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2394_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2394_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 0);
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2413_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2414_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2282_);
v___x_2415_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v___x_2283_, v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_a_2413_);
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2425_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2425_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2420_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2421_ = lean_string_append(v___x_2420_, v_a_2416_);
lean_dec(v_a_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2421_);
v___x_2423_ = v___x_2418_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2413_);
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
lean_dec(v_json_2282_);
lean_dec_ref(v_inst_2281_);
v_a_2426_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2415_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2415_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set_tag(v___x_2428_, 0);
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_a_2434_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2435_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2436_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2282_, v_inst_2281_, v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_a_2434_);
lean_dec(v_a_2413_);
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2441_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2442_ = lean_string_append(v___x_2441_, v_a_2437_);
lean_dec(v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2442_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2434_);
lean_dec(v_a_2413_);
lean_dec(v_a_2392_);
lean_dec(v_a_2370_);
lean_dec(v_a_2348_);
lean_dec(v_a_2327_);
lean_dec(v_a_2304_);
v_a_2447_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2436_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2436_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 0);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2466_; 
v_a_2455_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2457_ = v___x_2436_;
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2436_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; uint8_t v___x_2461_; uint8_t v___x_2462_; lean_object* v___x_2464_; 
v___x_2459_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2459_, 0, v_a_2304_);
lean_ctor_set(v___x_2459_, 1, v_a_2327_);
lean_ctor_set(v___x_2459_, 2, v_a_2348_);
lean_ctor_set(v___x_2459_, 3, v_a_2434_);
lean_ctor_set(v___x_2459_, 4, v_a_2455_);
v___x_2460_ = lean_unbox(v_a_2370_);
lean_dec(v_a_2370_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*5, v___x_2460_);
v___x_2461_ = lean_unbox(v_a_2392_);
lean_dec(v_a_2392_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*5 + 1, v___x_2461_);
v___x_2462_ = lean_unbox(v_a_2413_);
lean_dec(v_a_2413_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*5 + 2, v___x_2462_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2459_);
v___x_2464_ = v___x_2457_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2459_);
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2467_, lean_object* v_inst_2468_, lean_object* v_json_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2468_, v_json_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2472_, 0, lean_box(0));
lean_closure_set(v___x_2472_, 1, v_inst_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2473_, lean_object* v_inst_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2475_, 0, lean_box(0));
lean_closure_set(v___x_2475_, 1, v_inst_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2476_){
_start:
{
if (lean_obj_tag(v_x_2476_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_box(0);
return v___x_2477_;
}
else
{
lean_object* v_val_2478_; lean_object* v___x_2479_; 
v_val_2478_ = lean_ctor_get(v_x_2476_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v_x_2476_, 1);
v___x_2479_ = l_Lean_instToJsonPosition_toJson(v_val_2478_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
if (lean_obj_tag(v_a_2480_) == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_array_to_list(v_a_2481_);
return v___x_2482_;
}
else
{
lean_object* v_head_2483_; lean_object* v_tail_2484_; lean_object* v___x_2485_; 
v_head_2483_ = lean_ctor_get(v_a_2480_, 0);
lean_inc(v_head_2483_);
v_tail_2484_ = lean_ctor_get(v_a_2480_, 1);
lean_inc(v_tail_2484_);
lean_dec_ref_known(v_a_2480_, 2);
v___x_2485_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2481_, v_head_2483_);
v_a_2480_ = v_tail_2484_;
v_a_2481_ = v___x_2485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2488_){
_start:
{
lean_object* v_toBaseMessage_2489_; lean_object* v_kind_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2555_; 
v_toBaseMessage_2489_ = lean_ctor_get(v_x_2488_, 0);
v_kind_2490_ = lean_ctor_get(v_x_2488_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_x_2488_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2492_ = v_x_2488_;
v_isShared_2493_ = v_isSharedCheck_2555_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_kind_2490_);
lean_inc(v_toBaseMessage_2489_);
lean_dec(v_x_2488_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2555_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_fileName_2494_; lean_object* v_pos_2495_; lean_object* v_endPos_2496_; uint8_t v_keepFullRange_2497_; uint8_t v_severity_2498_; uint8_t v_isSilent_2499_; lean_object* v_caption_2500_; lean_object* v_data_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v_fileName_2494_ = lean_ctor_get(v_toBaseMessage_2489_, 0);
lean_inc_ref(v_fileName_2494_);
v_pos_2495_ = lean_ctor_get(v_toBaseMessage_2489_, 1);
lean_inc_ref(v_pos_2495_);
v_endPos_2496_ = lean_ctor_get(v_toBaseMessage_2489_, 2);
lean_inc(v_endPos_2496_);
v_keepFullRange_2497_ = lean_ctor_get_uint8(v_toBaseMessage_2489_, sizeof(void*)*5);
v_severity_2498_ = lean_ctor_get_uint8(v_toBaseMessage_2489_, sizeof(void*)*5 + 1);
v_isSilent_2499_ = lean_ctor_get_uint8(v_toBaseMessage_2489_, sizeof(void*)*5 + 2);
v_caption_2500_ = lean_ctor_get(v_toBaseMessage_2489_, 3);
lean_inc_ref(v_caption_2500_);
v_data_2501_ = lean_ctor_get(v_toBaseMessage_2489_, 4);
lean_inc(v_data_2501_);
lean_dec_ref(v_toBaseMessage_2489_);
v___x_2502_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_fileName_2494_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2503_);
lean_ctor_set(v___x_2492_, 0, v___x_2502_);
v___x_2505_ = v___x_2492_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2509_ = l_Lean_instToJsonPosition_toJson(v_pos_2495_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2506_);
v___x_2512_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2513_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2496_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___x_2506_);
v___x_2516_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2517_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2517_, 0, v_keepFullRange_2497_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2506_);
v___x_2520_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2521_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2498_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2506_);
v___x_2524_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2525_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2525_, 0, v_isSilent_2499_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2506_);
v___x_2528_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_caption_2500_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___x_2506_);
v___x_2532_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_data_2501_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___x_2506_);
v___x_2536_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2537_ = 1;
v___x_2538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2490_, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2536_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2506_);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___x_2506_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2535_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2531_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2527_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2523_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2519_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2515_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2511_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2507_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2552_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2550_, v___x_2551_);
v___x_2553_ = l_Lean_Json_mkObj(v___x_2552_);
lean_dec(v___x_2552_);
return v___x_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2558_, lean_object* v_k_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = l_Lean_Json_getObjValD(v_j_2558_, v_k_2559_);
v___x_2561_ = l_Lean_Json_getStr_x3f(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2562_, lean_object* v_k_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2562_, v_k_2563_);
lean_dec_ref(v_k_2563_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2565_, lean_object* v_k_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = l_Lean_Json_getObjValD(v_j_2565_, v_k_2566_);
v___x_2568_ = l_Lean_instFromJsonPosition_fromJson(v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2569_, lean_object* v_k_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2569_, v_k_2570_);
lean_dec_ref(v_k_2570_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2572_, lean_object* v_k_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = l_Lean_Json_getObjValD(v_j_2572_, v_k_2573_);
v___x_2575_ = l_Lean_Json_getBool_x3f(v___x_2574_);
lean_dec(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2576_, lean_object* v_k_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2576_, v_k_2577_);
lean_dec_ref(v_k_2577_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2579_, lean_object* v_k_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = l_Lean_Json_getObjValD(v_j_2579_, v_k_2580_);
v___x_2582_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2583_, lean_object* v_k_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2583_, v_k_2584_);
lean_dec_ref(v_k_2584_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2586_, lean_object* v_k_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = l_Lean_Json_getObjValD(v_j_2586_, v_k_2587_);
v___x_2589_ = l_Lean_Name_fromJson_x3f(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2590_, lean_object* v_k_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2590_, v_k_2591_);
lean_dec_ref(v_k_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2595_){
_start:
{
if (lean_obj_tag(v_x_2595_) == 0)
{
lean_object* v___x_2596_; 
v___x_2596_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_instFromJsonPosition_fromJson(v_x_2595_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
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
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_a_2606_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v___x_2597_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2597_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = l_Lean_Json_getObjValD(v_j_2615_, v_k_2616_);
v___x_2618_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2619_, lean_object* v_k_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2619_, v_k_2620_);
lean_dec_ref(v_k_2620_);
return v_res_2621_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = 1;
v___x_2627_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2627_, v___x_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2630_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2631_ = lean_string_append(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2633_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2634_ = lean_string_append(v___x_2633_, v___x_2632_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2636_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2637_ = lean_string_append(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2639_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2640_ = lean_string_append(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2642_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2643_ = lean_string_append(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2645_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2646_ = lean_string_append(v___x_2645_, v___x_2644_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2648_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2649_ = lean_string_append(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2651_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2652_ = lean_string_append(v___x_2651_, v___x_2650_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2654_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2655_ = lean_string_append(v___x_2654_, v___x_2653_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2657_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2658_ = lean_string_append(v___x_2657_, v___x_2656_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2660_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2661_ = lean_string_append(v___x_2660_, v___x_2659_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2663_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2664_ = lean_string_append(v___x_2663_, v___x_2662_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2666_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2667_ = lean_string_append(v___x_2666_, v___x_2665_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2669_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2670_ = lean_string_append(v___x_2669_, v___x_2668_);
return v___x_2670_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2672_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2673_ = lean_string_append(v___x_2672_, v___x_2671_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2675_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2676_ = lean_string_append(v___x_2675_, v___x_2674_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2678_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2679_ = lean_string_append(v___x_2678_, v___x_2677_);
return v___x_2679_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = 1;
v___x_2683_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2683_, v___x_2682_);
return v___x_2684_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2686_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2687_ = lean_string_append(v___x_2686_, v___x_2685_);
return v___x_2687_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2689_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2690_ = lean_string_append(v___x_2689_, v___x_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2691_);
v___x_2693_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2691_, v___x_2692_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_json_2691_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2698_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2699_ = lean_string_append(v___x_2698_, v_a_2694_);
lean_dec(v_a_2694_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2699_);
v___x_2701_ = v___x_2696_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_json_2691_);
v_a_2704_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2693_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2693_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 0);
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_a_2712_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2713_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2691_);
v___x_2714_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2691_, v___x_2713_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2719_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2720_ = lean_string_append(v___x_2719_, v_a_2715_);
lean_dec(v_a_2715_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2720_);
v___x_2722_ = v___x_2717_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2725_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2714_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2714_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set_tag(v___x_2727_, 0);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2734_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2691_);
v___x_2735_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2691_, v___x_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2740_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2741_ = lean_string_append(v___x_2740_, v_a_2736_);
lean_dec(v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2741_);
v___x_2743_ = v___x_2738_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2746_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2735_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2735_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_a_2754_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2755_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2691_);
v___x_2756_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2691_, v___x_2755_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2761_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2762_ = lean_string_append(v___x_2761_, v_a_2757_);
lean_dec(v_a_2757_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2767_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2756_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set_tag(v___x_2769_, 0);
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_a_2775_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2776_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2691_);
v___x_2777_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2691_, v___x_2776_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2782_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2783_ = lean_string_append(v___x_2782_, v_a_2778_);
lean_dec(v_a_2778_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2783_);
v___x_2785_ = v___x_2780_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2788_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2777_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2777_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 0);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2796_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2797_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2691_);
v___x_2798_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2691_, v___x_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2803_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2804_ = lean_string_append(v___x_2803_, v_a_2799_);
lean_dec(v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2804_);
v___x_2806_ = v___x_2801_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
else
{
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2809_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2798_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2798_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 0);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2818_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2691_);
v___x_2819_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2691_, v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2824_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2825_ = lean_string_append(v___x_2824_, v_a_2820_);
lean_dec(v_a_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2830_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2819_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2819_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 0);
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2839_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2691_);
v___x_2840_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2691_, v___x_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2838_);
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2845_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2846_ = lean_string_append(v___x_2845_, v_a_2841_);
lean_dec(v_a_2841_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2846_);
v___x_2848_ = v___x_2843_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2838_);
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
lean_dec(v_json_2691_);
v_a_2851_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2840_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2840_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 0);
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_a_2859_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2840_, 1);
v___x_2860_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2861_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2691_, v___x_2860_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2859_);
lean_dec(v_a_2838_);
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2871_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2871_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2866_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2867_ = lean_string_append(v___x_2866_, v_a_2862_);
lean_dec(v_a_2862_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2867_);
v___x_2869_ = v___x_2864_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2859_);
lean_dec(v_a_2838_);
lean_dec(v_a_2817_);
lean_dec(v_a_2796_);
lean_dec(v_a_2775_);
lean_dec(v_a_2754_);
lean_dec(v_a_2733_);
lean_dec(v_a_2712_);
v_a_2872_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2861_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2861_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set_tag(v___x_2874_, 0);
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2892_; 
v_a_2880_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2882_ = v___x_2861_;
v_isShared_2883_ = v_isSharedCheck_2892_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2861_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2892_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; uint8_t v___x_2885_; uint8_t v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2884_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2884_, 0, v_a_2712_);
lean_ctor_set(v___x_2884_, 1, v_a_2733_);
lean_ctor_set(v___x_2884_, 2, v_a_2754_);
lean_ctor_set(v___x_2884_, 3, v_a_2838_);
lean_ctor_set(v___x_2884_, 4, v_a_2859_);
v___x_2885_ = lean_unbox(v_a_2775_);
lean_dec(v_a_2775_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*5, v___x_2885_);
v___x_2886_ = lean_unbox(v_a_2796_);
lean_dec(v_a_2796_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*5 + 1, v___x_2886_);
v___x_2887_ = lean_unbox(v_a_2817_);
lean_dec(v_a_2817_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*5 + 2, v___x_2887_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2884_);
lean_ctor_set(v___x_2888_, 1, v_a_2880_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2888_);
v___x_2890_ = v___x_2882_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2899_ = l_Lean_Name_str___override(v_errorName_2897_, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2900_, lean_object* v_name_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = l_Lean_kindOfErrorName(v_name_2901_);
v___x_2903_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v_msg_2900_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2905_){
_start:
{
switch(lean_obj_tag(v_a_2905_))
{
case 0:
{
return v_a_2905_;
}
case 1:
{
lean_object* v_pre_2906_; lean_object* v_str_2907_; lean_object* v_p_x27_2908_; uint8_t v___y_2910_; uint8_t v___x_2913_; 
v_pre_2906_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_pre_2906_);
v_str_2907_ = lean_ctor_get(v_a_2905_, 1);
lean_inc_ref(v_str_2907_);
lean_dec_ref_known(v_a_2905_, 2);
v_p_x27_2908_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2906_);
v___x_2913_ = l_Lean_Name_isAnonymous(v_p_x27_2908_);
if (v___x_2913_ == 0)
{
v___y_2910_ = v___x_2913_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2915_ = lean_string_dec_eq(v_str_2907_, v___x_2914_);
v___y_2910_ = v___x_2915_;
goto v___jp_2909_;
}
v___jp_2909_:
{
if (v___y_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Name_str___override(v_p_x27_2908_, v_str_2907_);
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; 
lean_dec(v_p_x27_2908_);
lean_dec_ref(v_str_2907_);
v___x_2912_ = lean_box(0);
return v___x_2912_;
}
}
}
default: 
{
lean_object* v_pre_2916_; lean_object* v_i_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_pre_2916_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_pre_2916_);
v_i_2917_ = lean_ctor_get(v_a_2905_, 1);
lean_inc(v_i_2917_);
lean_dec_ref_known(v_a_2905_, 2);
v___x_2918_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2916_);
v___x_2919_ = l_Lean_Name_num___override(v___x_2918_, v_i_2917_);
return v___x_2919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2920_){
_start:
{
switch(lean_obj_tag(v_x_2920_))
{
case 3:
{
lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_a_2921_ = lean_ctor_get(v_x_2920_, 0);
v_a_2922_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2924_ = v_x_2920_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_inc(v_a_2921_);
lean_dec(v_x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = l_Lean_MessageData_stripNestedTags(v_a_2922_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2921_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
case 4:
{
lean_object* v_a_2931_; lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2940_; 
v_a_2931_ = lean_ctor_get(v_x_2920_, 0);
v_a_2932_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2934_ = v_x_2920_;
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_inc(v_a_2931_);
lean_dec(v_x_2920_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = l_Lean_MessageData_stripNestedTags(v_a_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v___x_2936_);
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2931_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
case 8:
{
lean_object* v_a_2941_; lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2950_; 
v_a_2941_ = lean_ctor_get(v_x_2920_, 0);
v_a_2942_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2944_ = v_x_2920_;
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_inc(v_a_2941_);
lean_dec(v_x_2920_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2941_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_a_2942_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
case 11:
{
lean_object* v_a_2951_; lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2960_; 
v_a_2951_ = lean_ctor_get(v_x_2920_, 0);
v_a_2952_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2954_ = v_x_2920_;
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_inc(v_a_2951_);
lean_dec(v_x_2920_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = l_Lean_MessageData_stripNestedTags(v_a_2952_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2951_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
case 12:
{
lean_object* v_a_2961_; lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2970_; 
v_a_2961_ = lean_ctor_get(v_x_2920_, 0);
v_a_2962_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2964_ = v_x_2920_;
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_inc(v_a_2961_);
lean_dec(v_x_2920_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2970_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = l_Lean_MessageData_stripNestedTags(v_a_2962_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v___x_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2961_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
default: 
{
return v_x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2971_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 1)
{
lean_object* v_pre_2972_; lean_object* v_str_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v_pre_2972_ = lean_ctor_get(v_x_2971_, 0);
v_str_2973_ = lean_ctor_get(v_x_2971_, 1);
v___x_2974_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2975_ = lean_string_dec_eq(v_str_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_box(0);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; 
lean_inc(v_pre_2972_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_pre_2972_);
return v___x_2977_;
}
}
else
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_box(0);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_errorNameOfKind_x3f(v_x_2979_);
lean_dec(v_x_2979_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = l_Lean_MessageData_kind(v_msg_2981_);
v___x_2983_ = l_Lean_errorNameOfKind_x3f(v___x_2982_);
lean_dec(v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_MessageData_errorName_x3f(v_msg_2984_);
lean_dec_ref(v_msg_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2986_){
_start:
{
lean_object* v_data_2987_; lean_object* v___x_2988_; 
v_data_2987_ = lean_ctor_get(v_msg_2986_, 4);
v___x_2988_ = l_Lean_MessageData_errorName_x3f(v_data_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Message_errorName_x3f(v_msg_2989_);
lean_dec_ref(v_msg_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2991_){
_start:
{
lean_object* v_toBaseMessage_2992_; lean_object* v_fileName_2993_; lean_object* v_pos_2994_; lean_object* v_endPos_2995_; uint8_t v_keepFullRange_2996_; uint8_t v_severity_2997_; uint8_t v_isSilent_2998_; lean_object* v_caption_2999_; lean_object* v_data_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3009_; 
v_toBaseMessage_2992_ = lean_ctor_get(v_msg_2991_, 0);
lean_inc_ref(v_toBaseMessage_2992_);
lean_dec_ref(v_msg_2991_);
v_fileName_2993_ = lean_ctor_get(v_toBaseMessage_2992_, 0);
v_pos_2994_ = lean_ctor_get(v_toBaseMessage_2992_, 1);
v_endPos_2995_ = lean_ctor_get(v_toBaseMessage_2992_, 2);
v_keepFullRange_2996_ = lean_ctor_get_uint8(v_toBaseMessage_2992_, sizeof(void*)*5);
v_severity_2997_ = lean_ctor_get_uint8(v_toBaseMessage_2992_, sizeof(void*)*5 + 1);
v_isSilent_2998_ = lean_ctor_get_uint8(v_toBaseMessage_2992_, sizeof(void*)*5 + 2);
v_caption_2999_ = lean_ctor_get(v_toBaseMessage_2992_, 3);
v_data_3000_ = lean_ctor_get(v_toBaseMessage_2992_, 4);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_toBaseMessage_2992_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3002_ = v_toBaseMessage_2992_;
v_isShared_3003_ = v_isSharedCheck_3009_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_data_3000_);
lean_inc(v_caption_2999_);
lean_inc(v_endPos_2995_);
lean_inc(v_pos_2994_);
lean_inc(v_fileName_2993_);
lean_dec(v_toBaseMessage_2992_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3009_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_data_3000_);
v___x_3005_ = l_Lean_MessageData_ofFormat(v___x_3004_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 4, v___x_3005_);
v___x_3007_ = v___x_3002_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fileName_2993_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_pos_2994_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_endPos_2995_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_caption_2999_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v___x_3005_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*5, v_keepFullRange_2996_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*5 + 1, v_severity_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*5 + 2, v_isSilent_2998_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_3015_, uint8_t v_includeEndPos_3016_){
_start:
{
lean_object* v___y_3018_; lean_object* v___y_3022_; uint8_t v___y_3023_; uint32_t v___y_3024_; lean_object* v_str_3028_; lean_object* v_toBaseMessage_3040_; lean_object* v_kind_3041_; lean_object* v_fileName_3042_; lean_object* v_pos_3043_; lean_object* v_endPos_3044_; uint8_t v_severity_3045_; lean_object* v_caption_3046_; lean_object* v_data_3047_; lean_object* v___y_3049_; lean_object* v_str_3050_; lean_object* v___y_3058_; 
v_toBaseMessage_3040_ = lean_ctor_get(v_msg_3015_, 0);
lean_inc_ref(v_toBaseMessage_3040_);
v_kind_3041_ = lean_ctor_get(v_msg_3015_, 1);
lean_inc(v_kind_3041_);
lean_dec_ref(v_msg_3015_);
v_fileName_3042_ = lean_ctor_get(v_toBaseMessage_3040_, 0);
lean_inc_ref(v_fileName_3042_);
v_pos_3043_ = lean_ctor_get(v_toBaseMessage_3040_, 1);
lean_inc_ref(v_pos_3043_);
v_endPos_3044_ = lean_ctor_get(v_toBaseMessage_3040_, 2);
lean_inc(v_endPos_3044_);
v_severity_3045_ = lean_ctor_get_uint8(v_toBaseMessage_3040_, sizeof(void*)*5 + 1);
v_caption_3046_ = lean_ctor_get(v_toBaseMessage_3040_, 3);
lean_inc_ref(v_caption_3046_);
v_data_3047_ = lean_ctor_get(v_toBaseMessage_3040_, 4);
lean_inc(v_data_3047_);
lean_dec_ref(v_toBaseMessage_3040_);
if (v_includeEndPos_3016_ == 0)
{
lean_object* v___x_3064_; 
lean_dec(v_endPos_3044_);
v___x_3064_ = lean_box(0);
v___y_3058_ = v___x_3064_;
goto v___jp_3057_;
}
else
{
v___y_3058_ = v_endPos_3044_;
goto v___jp_3057_;
}
v___jp_3017_:
{
lean_object* v___x_3019_; lean_object* v_str_3020_; 
v___x_3019_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3020_ = lean_string_append(v___y_3018_, v___x_3019_);
return v_str_3020_;
}
v___jp_3021_:
{
uint32_t v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = 10;
v___x_3026_ = lean_uint32_dec_eq(v___y_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
v___y_3018_ = v___y_3022_;
goto v___jp_3017_;
}
else
{
if (v___y_3023_ == 0)
{
return v___y_3022_;
}
else
{
v___y_3018_ = v___y_3022_;
goto v___jp_3017_;
}
}
}
v___jp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_string_utf8_byte_size(v_str_3028_);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_nat_dec_eq(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_inc_ref(v_str_3028_);
v___x_3032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3032_, 0, v_str_3028_);
lean_ctor_set(v___x_3032_, 1, v___x_3030_);
lean_ctor_set(v___x_3032_, 2, v___x_3029_);
v___x_3033_ = l_String_Slice_Pos_prev_x3f(v___x_3032_, v___x_3029_);
if (lean_obj_tag(v___x_3033_) == 0)
{
uint32_t v___x_3034_; 
lean_dec_ref_known(v___x_3032_, 3);
v___x_3034_ = 65;
v___y_3022_ = v_str_3028_;
v___y_3023_ = v___x_3031_;
v___y_3024_ = v___x_3034_;
goto v___jp_3021_;
}
else
{
lean_object* v_val_3035_; lean_object* v___x_3036_; 
v_val_3035_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3036_ = l_String_Slice_Pos_get_x3f(v___x_3032_, v_val_3035_);
lean_dec(v_val_3035_);
lean_dec_ref_known(v___x_3032_, 3);
if (lean_obj_tag(v___x_3036_) == 0)
{
uint32_t v___x_3037_; 
v___x_3037_ = 65;
v___y_3022_ = v_str_3028_;
v___y_3023_ = v___x_3031_;
v___y_3024_ = v___x_3037_;
goto v___jp_3021_;
}
else
{
lean_object* v_val_3038_; uint32_t v___x_3039_; 
v_val_3038_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v___x_3036_, 1);
v___x_3039_ = lean_unbox_uint32(v_val_3038_);
lean_dec(v_val_3038_);
v___y_3022_ = v_str_3028_;
v___y_3023_ = v___x_3031_;
v___y_3024_ = v___x_3039_;
goto v___jp_3021_;
}
}
}
else
{
v___y_3018_ = v_str_3028_;
goto v___jp_3017_;
}
}
v___jp_3048_:
{
switch(v_severity_3045_)
{
case 0:
{
lean_dec(v___y_3049_);
lean_dec_ref(v_pos_3043_);
lean_dec_ref(v_fileName_3042_);
lean_dec(v_kind_3041_);
v_str_3028_ = v_str_3050_;
goto v___jp_3027_;
}
case 1:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_str_3053_; 
v___x_3051_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3052_ = l_Lean_errorNameOfKind_x3f(v_kind_3041_);
lean_dec(v_kind_3041_);
v_str_3053_ = l_Lean_mkErrorStringWithPos(v_fileName_3042_, v_pos_3043_, v_str_3050_, v___y_3049_, v___x_3051_, v___x_3052_);
lean_dec_ref(v_str_3050_);
v_str_3028_ = v_str_3053_;
goto v___jp_3027_;
}
default: 
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_str_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3055_ = l_Lean_errorNameOfKind_x3f(v_kind_3041_);
lean_dec(v_kind_3041_);
v_str_3056_ = l_Lean_mkErrorStringWithPos(v_fileName_3042_, v_pos_3043_, v_str_3050_, v___y_3049_, v___x_3054_, v___x_3055_);
lean_dec_ref(v_str_3050_);
v_str_3028_ = v_str_3056_;
goto v___jp_3027_;
}
}
}
v___jp_3057_:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3060_ = lean_string_dec_eq(v_caption_3046_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v_str_3063_; 
v___x_3061_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3062_ = lean_string_append(v_caption_3046_, v___x_3061_);
v_str_3063_ = lean_string_append(v___x_3062_, v_data_3047_);
lean_dec(v_data_3047_);
v___y_3049_ = v___y_3058_;
v_str_3050_ = v_str_3063_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v_caption_3046_);
v___y_3049_ = v___y_3058_;
v_str_3050_ = v_data_3047_;
goto v___jp_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3065_, lean_object* v_includeEndPos_3066_){
_start:
{
uint8_t v_includeEndPos_boxed_3067_; lean_object* v_res_3068_; 
v_includeEndPos_boxed_3067_ = lean_unbox(v_includeEndPos_3066_);
v_res_3068_ = l_Lean_SerialMessage_toString(v_msg_3065_, v_includeEndPos_boxed_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3069_){
_start:
{
uint8_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = 0;
v___x_3071_ = l_Lean_SerialMessage_toString(v_msg_3069_, v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3074_){
_start:
{
lean_object* v_data_3075_; lean_object* v___x_3076_; 
v_data_3075_ = lean_ctor_get(v_msg_3074_, 4);
v___x_3076_ = l_Lean_MessageData_kind(v_data_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Message_kind(v_msg_3077_);
lean_dec_ref(v_msg_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3079_){
_start:
{
lean_object* v_data_3080_; uint8_t v___x_3081_; 
v_data_3080_ = lean_ctor_get(v_msg_3079_, 4);
v___x_3081_ = l_Lean_MessageData_isTrace(v_data_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3082_){
_start:
{
uint8_t v_res_3083_; lean_object* v_r_3084_; 
v_res_3083_ = l_Lean_Message_isTrace(v_msg_3082_);
lean_dec_ref(v_msg_3082_);
v_r_3084_ = lean_box(v_res_3083_);
return v_r_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3085_){
_start:
{
lean_object* v_fileName_3087_; lean_object* v_pos_3088_; lean_object* v_endPos_3089_; uint8_t v_keepFullRange_3090_; uint8_t v_severity_3091_; uint8_t v_isSilent_3092_; lean_object* v_caption_3093_; lean_object* v_data_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3104_; 
v_fileName_3087_ = lean_ctor_get(v_msg_3085_, 0);
v_pos_3088_ = lean_ctor_get(v_msg_3085_, 1);
v_endPos_3089_ = lean_ctor_get(v_msg_3085_, 2);
v_keepFullRange_3090_ = lean_ctor_get_uint8(v_msg_3085_, sizeof(void*)*5);
v_severity_3091_ = lean_ctor_get_uint8(v_msg_3085_, sizeof(void*)*5 + 1);
v_isSilent_3092_ = lean_ctor_get_uint8(v_msg_3085_, sizeof(void*)*5 + 2);
v_caption_3093_ = lean_ctor_get(v_msg_3085_, 3);
v_data_3094_ = lean_ctor_get(v_msg_3085_, 4);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_msg_3085_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3096_ = v_msg_3085_;
v_isShared_3097_ = v_isSharedCheck_3104_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_data_3094_);
lean_inc(v_caption_3093_);
lean_inc(v_endPos_3089_);
lean_inc(v_pos_3088_);
lean_inc(v_fileName_3087_);
lean_dec(v_msg_3085_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3104_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
lean_inc(v_data_3094_);
v___x_3098_ = l_Lean_MessageData_toString(v_data_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 4, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_fileName_3087_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_pos_3088_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_endPos_3089_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_caption_3093_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v___x_3098_);
lean_ctor_set_uint8(v_reuseFailAlloc_3103_, sizeof(void*)*5, v_keepFullRange_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3103_, sizeof(void*)*5 + 1, v_severity_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3103_, sizeof(void*)*5 + 2, v_isSilent_3092_);
v___x_3100_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = l_Lean_MessageData_kind(v_data_3094_);
lean_dec(v_data_3094_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Message_serialize(v_msg_3105_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3108_, uint8_t v_includeEndPos_3109_){
_start:
{
lean_object* v_fileName_3111_; lean_object* v_pos_3112_; lean_object* v_endPos_3113_; uint8_t v_severity_3114_; lean_object* v_caption_3115_; lean_object* v_data_3116_; lean_object* v___x_3117_; lean_object* v___y_3119_; uint8_t v___y_3123_; lean_object* v___y_3124_; uint32_t v___y_3125_; lean_object* v_str_3129_; lean_object* v___x_3141_; lean_object* v___y_3143_; lean_object* v_str_3144_; lean_object* v___y_3152_; 
v_fileName_3111_ = lean_ctor_get(v_msg_3108_, 0);
lean_inc_ref(v_fileName_3111_);
v_pos_3112_ = lean_ctor_get(v_msg_3108_, 1);
lean_inc_ref(v_pos_3112_);
v_endPos_3113_ = lean_ctor_get(v_msg_3108_, 2);
lean_inc(v_endPos_3113_);
v_severity_3114_ = lean_ctor_get_uint8(v_msg_3108_, sizeof(void*)*5 + 1);
v_caption_3115_ = lean_ctor_get(v_msg_3108_, 3);
lean_inc_ref(v_caption_3115_);
v_data_3116_ = lean_ctor_get(v_msg_3108_, 4);
lean_inc_n(v_data_3116_, 2);
lean_dec_ref(v_msg_3108_);
v___x_3117_ = l_Lean_MessageData_toString(v_data_3116_);
v___x_3141_ = l_Lean_MessageData_kind(v_data_3116_);
lean_dec(v_data_3116_);
if (v_includeEndPos_3109_ == 0)
{
lean_object* v___x_3158_; 
lean_dec(v_endPos_3113_);
v___x_3158_ = lean_box(0);
v___y_3152_ = v___x_3158_;
goto v___jp_3151_;
}
else
{
v___y_3152_ = v_endPos_3113_;
goto v___jp_3151_;
}
v___jp_3118_:
{
lean_object* v___x_3120_; lean_object* v_str_3121_; 
v___x_3120_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3121_ = lean_string_append(v___y_3119_, v___x_3120_);
return v_str_3121_;
}
v___jp_3122_:
{
uint32_t v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = 10;
v___x_3127_ = lean_uint32_dec_eq(v___y_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
v___y_3119_ = v___y_3124_;
goto v___jp_3118_;
}
else
{
if (v___y_3123_ == 0)
{
return v___y_3124_;
}
else
{
v___y_3119_ = v___y_3124_;
goto v___jp_3118_;
}
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
v___y_3123_ = v___x_3132_;
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3135_;
goto v___jp_3122_;
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
v___y_3123_ = v___x_3132_;
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3138_;
goto v___jp_3122_;
}
else
{
lean_object* v_val_3139_; uint32_t v___x_3140_; 
v_val_3139_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3140_ = lean_unbox_uint32(v_val_3139_);
lean_dec(v_val_3139_);
v___y_3123_ = v___x_3132_;
v___y_3124_ = v_str_3129_;
v___y_3125_ = v___x_3140_;
goto v___jp_3122_;
}
}
}
else
{
v___y_3119_ = v_str_3129_;
goto v___jp_3118_;
}
}
v___jp_3142_:
{
switch(v_severity_3114_)
{
case 0:
{
lean_dec(v___y_3143_);
lean_dec(v___x_3141_);
lean_dec_ref(v_pos_3112_);
lean_dec_ref(v_fileName_3111_);
v_str_3129_ = v_str_3144_;
goto v___jp_3128_;
}
case 1:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_str_3147_; 
v___x_3145_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3146_ = l_Lean_errorNameOfKind_x3f(v___x_3141_);
lean_dec(v___x_3141_);
v_str_3147_ = l_Lean_mkErrorStringWithPos(v_fileName_3111_, v_pos_3112_, v_str_3144_, v___y_3143_, v___x_3145_, v___x_3146_);
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
v_str_3150_ = l_Lean_mkErrorStringWithPos(v_fileName_3111_, v_pos_3112_, v_str_3144_, v___y_3143_, v___x_3148_, v___x_3149_);
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
v___x_3154_ = lean_string_dec_eq(v_caption_3115_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v_str_3157_; 
v___x_3155_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3156_ = lean_string_append(v_caption_3115_, v___x_3155_);
v_str_3157_ = lean_string_append(v___x_3156_, v___x_3117_);
lean_dec_ref(v___x_3117_);
v___y_3143_ = v___y_3152_;
v_str_3144_ = v_str_3157_;
goto v___jp_3142_;
}
else
{
lean_dec_ref(v_caption_3115_);
v___y_3143_ = v___y_3152_;
v_str_3144_ = v___x_3117_;
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
lean_object* v___x_3354_; uint8_t v_severity_3355_; uint8_t v___x_3356_; 
v___x_3354_ = lean_array_uget_borrowed(v_as_3350_, v_i_3351_);
v_severity_3355_ = lean_ctor_get_uint8(v___x_3354_, sizeof(void*)*5 + 1);
v___x_3356_ = 1;
if (v_severity_3355_ == 2)
{
return v___x_3356_;
}
else
{
if (v___x_3353_ == 0)
{
size_t v___x_3357_; size_t v___x_3358_; 
v___x_3357_ = ((size_t)1ULL);
v___x_3358_ = lean_usize_add(v_i_3351_, v___x_3357_);
v_i_3351_ = v___x_3358_;
goto _start;
}
else
{
return v___x_3356_;
}
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
return v___x_3406_;
}
else
{
if (v___x_3409_ == 0)
{
return v___x_3406_;
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
uint8_t v___x_1876__boxed_3432_; size_t v_i_boxed_3433_; size_t v_stop_boxed_3434_; uint8_t v_res_3435_; lean_object* v_r_3436_; 
v___x_1876__boxed_3432_ = lean_unbox(v___x_3428_);
v_i_boxed_3433_ = lean_unbox_usize(v_i_3430_);
lean_dec(v_i_3430_);
v_stop_boxed_3434_ = lean_unbox_usize(v_stop_3431_);
lean_dec(v_stop_3431_);
v_res_3435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1876__boxed_3432_, v_as_3429_, v_i_boxed_3433_, v_stop_boxed_3434_);
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
uint8_t v___x_1893__boxed_3468_; size_t v_i_boxed_3469_; size_t v_stop_boxed_3470_; uint8_t v_res_3471_; lean_object* v_r_3472_; 
v___x_1893__boxed_3468_ = lean_unbox(v___x_3464_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_stop_boxed_3470_ = lean_unbox_usize(v_stop_3467_);
lean_dec(v_stop_3467_);
v_res_3471_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1893__boxed_3468_, v_as_3465_, v_i_boxed_3469_, v_stop_boxed_3470_);
lean_dec_ref(v_as_3465_);
v_r_3472_ = lean_box(v_res_3471_);
return v_r_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3473_, lean_object* v_x_3474_){
_start:
{
uint8_t v___x_1901__boxed_3475_; uint8_t v_res_3476_; lean_object* v_r_3477_; 
v___x_1901__boxed_3475_ = lean_unbox(v___x_3473_);
v_res_3476_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1901__boxed_3475_, v_x_3474_);
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
return v___x_3482_;
}
else
{
if (v___x_3485_ == 0)
{
return v___x_3482_;
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
uint8_t v___x_1944__boxed_3491_; uint8_t v_res_3492_; lean_object* v_r_3493_; 
v___x_1944__boxed_3491_ = lean_unbox(v___x_3489_);
v_res_3492_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1944__boxed_3491_, v_t_3490_);
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
uint8_t v___x_3771_; 
v___x_3771_ = lean_nat_dec_le(v___x_3769_, v___x_3769_);
if (v___x_3771_ == 0)
{
if (v___x_3770_ == 0)
{
return v_x_3766_;
}
else
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = ((size_t)0ULL);
v___x_3773_ = lean_usize_of_nat(v___x_3769_);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3767_, v___x_3772_, v___x_3773_, v_x_3766_);
return v___x_3774_;
}
}
else
{
size_t v___x_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v___x_3775_ = ((size_t)0ULL);
v___x_3776_ = lean_usize_of_nat(v___x_3769_);
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3767_, v___x_3775_, v___x_3776_, v_x_3766_);
return v___x_3777_;
}
}
}
else
{
lean_object* v_vs_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_vs_3778_ = lean_ctor_get(v_x_3765_, 0);
v___x_3779_ = lean_unsigned_to_nat(0u);
v___x_3780_ = lean_array_get_size(v_vs_3778_);
v___x_3781_ = lean_nat_dec_lt(v___x_3779_, v___x_3780_);
if (v___x_3781_ == 0)
{
return v_x_3766_;
}
else
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_nat_dec_le(v___x_3780_, v___x_3780_);
if (v___x_3782_ == 0)
{
if (v___x_3781_ == 0)
{
return v_x_3766_;
}
else
{
size_t v___x_3783_; size_t v___x_3784_; lean_object* v___x_3785_; 
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = lean_usize_of_nat(v___x_3780_);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3778_, v___x_3783_, v___x_3784_, v_x_3766_);
return v___x_3785_;
}
}
else
{
size_t v___x_3786_; size_t v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = lean_usize_of_nat(v___x_3780_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3778_, v___x_3786_, v___x_3787_, v_x_3766_);
return v___x_3788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3789_, size_t v_i_3790_, size_t v_stop_3791_, lean_object* v_b_3792_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_eq(v_i_3790_, v_stop_3791_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; size_t v___x_3796_; size_t v___x_3797_; 
v___x_3794_ = lean_array_uget_borrowed(v_as_3789_, v_i_3790_);
v___x_3795_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3794_, v_b_3792_);
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3790_, v___x_3796_);
v_i_3790_ = v___x_3797_;
v_b_3792_ = v___x_3795_;
goto _start;
}
else
{
return v_b_3792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3799_, lean_object* v_i_3800_, lean_object* v_stop_3801_, lean_object* v_b_3802_){
_start:
{
size_t v_i_boxed_3803_; size_t v_stop_boxed_3804_; lean_object* v_res_3805_; 
v_i_boxed_3803_ = lean_unbox_usize(v_i_3800_);
lean_dec(v_i_3800_);
v_stop_boxed_3804_ = lean_unbox_usize(v_stop_3801_);
lean_dec(v_stop_3801_);
v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3799_, v_i_boxed_3803_, v_stop_boxed_3804_, v_b_3802_);
lean_dec_ref(v_as_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3806_, lean_object* v_x_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3806_, v_x_3807_);
lean_dec_ref(v_x_3806_);
return v_res_3808_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3810_, size_t v_x_3811_, size_t v_x_3812_, lean_object* v_x_3813_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 0)
{
lean_object* v_cs_3814_; lean_object* v___x_3815_; size_t v___x_3816_; lean_object* v_j_3817_; lean_object* v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; size_t v___x_3823_; size_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_cs_3814_ = lean_ctor_get(v_x_3810_, 0);
v___x_3815_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3816_ = lean_usize_shift_right(v_x_3811_, v_x_3812_);
v_j_3817_ = lean_usize_to_nat(v___x_3816_);
v___x_3818_ = lean_array_get_borrowed(v___x_3815_, v_cs_3814_, v_j_3817_);
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_shift_left(v___x_3819_, v_x_3812_);
v___x_3821_ = lean_usize_sub(v___x_3820_, v___x_3819_);
v___x_3822_ = lean_usize_land(v_x_3811_, v___x_3821_);
v___x_3823_ = ((size_t)5ULL);
v___x_3824_ = lean_usize_sub(v_x_3812_, v___x_3823_);
v___x_3825_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3818_, v___x_3822_, v___x_3824_, v_x_3813_);
v___x_3826_ = lean_unsigned_to_nat(1u);
v___x_3827_ = lean_nat_add(v_j_3817_, v___x_3826_);
lean_dec(v_j_3817_);
v___x_3828_ = lean_array_get_size(v_cs_3814_);
v___x_3829_ = lean_nat_dec_lt(v___x_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_dec(v___x_3827_);
return v___x_3825_;
}
else
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_nat_dec_le(v___x_3828_, v___x_3828_);
if (v___x_3830_ == 0)
{
if (v___x_3829_ == 0)
{
lean_dec(v___x_3827_);
return v___x_3825_;
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_usize_of_nat(v___x_3827_);
lean_dec(v___x_3827_);
v___x_3832_ = lean_usize_of_nat(v___x_3828_);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3814_, v___x_3831_, v___x_3832_, v___x_3825_);
return v___x_3833_;
}
}
else
{
size_t v___x_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = lean_usize_of_nat(v___x_3827_);
lean_dec(v___x_3827_);
v___x_3835_ = lean_usize_of_nat(v___x_3828_);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3814_, v___x_3834_, v___x_3835_, v___x_3825_);
return v___x_3836_;
}
}
}
else
{
lean_object* v_vs_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_vs_3837_ = lean_ctor_get(v_x_3810_, 0);
v___x_3838_ = lean_usize_to_nat(v_x_3811_);
v___x_3839_ = lean_array_get_size(v_vs_3837_);
v___x_3840_ = lean_nat_dec_lt(v___x_3838_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_dec(v___x_3838_);
return v_x_3813_;
}
else
{
uint8_t v___x_3841_; 
v___x_3841_ = lean_nat_dec_le(v___x_3839_, v___x_3839_);
if (v___x_3841_ == 0)
{
if (v___x_3840_ == 0)
{
lean_dec(v___x_3838_);
return v_x_3813_;
}
else
{
size_t v___x_3842_; size_t v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = lean_usize_of_nat(v___x_3838_);
lean_dec(v___x_3838_);
v___x_3843_ = lean_usize_of_nat(v___x_3839_);
v___x_3844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3837_, v___x_3842_, v___x_3843_, v_x_3813_);
return v___x_3844_;
}
}
else
{
size_t v___x_3845_; size_t v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = lean_usize_of_nat(v___x_3838_);
lean_dec(v___x_3838_);
v___x_3846_ = lean_usize_of_nat(v___x_3839_);
v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3837_, v___x_3845_, v___x_3846_, v_x_3813_);
return v___x_3847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3848_, lean_object* v_x_3849_, lean_object* v_x_3850_, lean_object* v_x_3851_){
_start:
{
size_t v_x_1524__boxed_3852_; size_t v_x_1525__boxed_3853_; lean_object* v_res_3854_; 
v_x_1524__boxed_3852_ = lean_unbox_usize(v_x_3849_);
lean_dec(v_x_3849_);
v_x_1525__boxed_3853_ = lean_unbox_usize(v_x_3850_);
lean_dec(v_x_3850_);
v_res_3854_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3848_, v_x_1524__boxed_3852_, v_x_1525__boxed_3853_, v_x_3851_);
lean_dec_ref(v_x_3848_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3855_, lean_object* v_init_3856_, lean_object* v_start_3857_){
_start:
{
lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3858_ = lean_unsigned_to_nat(0u);
v___x_3859_ = lean_nat_dec_eq(v_start_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v_root_3860_; lean_object* v_tail_3861_; size_t v_shift_3862_; lean_object* v_tailOff_3863_; uint8_t v___x_3864_; 
v_root_3860_ = lean_ctor_get(v_t_3855_, 0);
v_tail_3861_ = lean_ctor_get(v_t_3855_, 1);
v_shift_3862_ = lean_ctor_get_usize(v_t_3855_, 4);
v_tailOff_3863_ = lean_ctor_get(v_t_3855_, 3);
v___x_3864_ = lean_nat_dec_le(v_tailOff_3863_, v_start_3857_);
if (v___x_3864_ == 0)
{
size_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3865_ = lean_usize_of_nat(v_start_3857_);
v___x_3866_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3860_, v___x_3865_, v_shift_3862_, v_init_3856_);
v___x_3867_ = lean_array_get_size(v_tail_3861_);
v___x_3868_ = lean_nat_dec_lt(v___x_3858_, v___x_3867_);
if (v___x_3868_ == 0)
{
return v___x_3866_;
}
else
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_nat_dec_le(v___x_3867_, v___x_3867_);
if (v___x_3869_ == 0)
{
if (v___x_3868_ == 0)
{
return v___x_3866_;
}
else
{
size_t v___x_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = ((size_t)0ULL);
v___x_3871_ = lean_usize_of_nat(v___x_3867_);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3861_, v___x_3870_, v___x_3871_, v___x_3866_);
return v___x_3872_;
}
}
else
{
size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = lean_usize_of_nat(v___x_3867_);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3861_, v___x_3873_, v___x_3874_, v___x_3866_);
return v___x_3875_;
}
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3876_ = lean_nat_sub(v_start_3857_, v_tailOff_3863_);
v___x_3877_ = lean_array_get_size(v_tail_3861_);
v___x_3878_ = lean_nat_dec_lt(v___x_3876_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_dec(v___x_3876_);
return v_init_3856_;
}
else
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_nat_dec_le(v___x_3877_, v___x_3877_);
if (v___x_3879_ == 0)
{
if (v___x_3878_ == 0)
{
lean_dec(v___x_3876_);
return v_init_3856_;
}
else
{
size_t v___x_3880_; size_t v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_usize_of_nat(v___x_3876_);
lean_dec(v___x_3876_);
v___x_3881_ = lean_usize_of_nat(v___x_3877_);
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3861_, v___x_3880_, v___x_3881_, v_init_3856_);
return v___x_3882_;
}
}
else
{
size_t v___x_3883_; size_t v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = lean_usize_of_nat(v___x_3876_);
lean_dec(v___x_3876_);
v___x_3884_ = lean_usize_of_nat(v___x_3877_);
v___x_3885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3861_, v___x_3883_, v___x_3884_, v_init_3856_);
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_root_3886_; lean_object* v_tail_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v_root_3886_ = lean_ctor_get(v_t_3855_, 0);
v_tail_3887_ = lean_ctor_get(v_t_3855_, 1);
v___x_3888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3886_, v_init_3856_);
v___x_3889_ = lean_array_get_size(v_tail_3887_);
v___x_3890_ = lean_nat_dec_lt(v___x_3858_, v___x_3889_);
if (v___x_3890_ == 0)
{
return v___x_3888_;
}
else
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_nat_dec_le(v___x_3889_, v___x_3889_);
if (v___x_3891_ == 0)
{
if (v___x_3890_ == 0)
{
return v___x_3888_;
}
else
{
size_t v___x_3892_; size_t v___x_3893_; lean_object* v___x_3894_; 
v___x_3892_ = ((size_t)0ULL);
v___x_3893_ = lean_usize_of_nat(v___x_3889_);
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3887_, v___x_3892_, v___x_3893_, v___x_3888_);
return v___x_3894_;
}
}
else
{
size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = ((size_t)0ULL);
v___x_3896_ = lean_usize_of_nat(v___x_3889_);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3887_, v___x_3895_, v___x_3896_, v___x_3888_);
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3898_, lean_object* v_init_3899_, lean_object* v_start_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3898_, v_init_3899_, v_start_3900_);
lean_dec(v_start_3900_);
lean_dec_ref(v_t_3898_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3902_){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v_unreported_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3916_; 
v___x_3903_ = lean_unsigned_to_nat(32u);
v___x_3904_ = lean_mk_empty_array_with_capacity(v___x_3903_);
lean_dec_ref(v___x_3904_);
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3907_ = lean_ctor_get(v_log_3902_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_log_3902_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; lean_object* v_unused_3918_; 
v_unused_3917_ = lean_ctor_get(v_log_3902_, 2);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_log_3902_, 0);
lean_dec(v_unused_3918_);
v___x_3909_ = v_log_3902_;
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_unreported_3907_);
lean_dec(v_log_3902_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3911_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3907_, v___x_3906_, v___x_3905_);
lean_dec_ref(v_unreported_3907_);
v___x_3912_ = l_Lean_NameSet_empty;
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 2, v___x_3912_);
lean_ctor_set(v___x_3909_, 1, v___x_3911_);
lean_ctor_set(v___x_3909_, 0, v___x_3906_);
v___x_3914_ = v___x_3909_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3919_, size_t v_i_3920_, size_t v_stop_3921_, lean_object* v_b_3922_){
_start:
{
lean_object* v___y_3924_; uint8_t v___x_3928_; 
v___x_3928_ = lean_usize_dec_eq(v_i_3920_, v_stop_3921_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; uint8_t v_severity_3930_; 
v___x_3929_ = lean_array_uget_borrowed(v_as_3919_, v_i_3920_);
v_severity_3930_ = lean_ctor_get_uint8(v___x_3929_, sizeof(void*)*5 + 1);
if (v_severity_3930_ == 1)
{
lean_object* v___x_3931_; 
lean_inc(v___x_3929_);
v___x_3931_ = l_Lean_PersistentArray_push___redArg(v_b_3922_, v___x_3929_);
v___y_3924_ = v___x_3931_;
goto v___jp_3923_;
}
else
{
v___y_3924_ = v_b_3922_;
goto v___jp_3923_;
}
}
else
{
return v_b_3922_;
}
v___jp_3923_:
{
size_t v___x_3925_; size_t v___x_3926_; 
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3920_, v___x_3925_);
v_i_3920_ = v___x_3926_;
v_b_3922_ = v___y_3924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3932_, lean_object* v_i_3933_, lean_object* v_stop_3934_, lean_object* v_b_3935_){
_start:
{
size_t v_i_boxed_3936_; size_t v_stop_boxed_3937_; lean_object* v_res_3938_; 
v_i_boxed_3936_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_stop_boxed_3937_ = lean_unbox_usize(v_stop_3934_);
lean_dec(v_stop_3934_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3932_, v_i_boxed_3936_, v_stop_boxed_3937_, v_b_3935_);
lean_dec_ref(v_as_3932_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3939_, lean_object* v_x_3940_){
_start:
{
if (lean_obj_tag(v_x_3939_) == 0)
{
lean_object* v_cs_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v_cs_3941_ = lean_ctor_get(v_x_3939_, 0);
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3943_ = lean_array_get_size(v_cs_3941_);
v___x_3944_ = lean_nat_dec_lt(v___x_3942_, v___x_3943_);
if (v___x_3944_ == 0)
{
return v_x_3940_;
}
else
{
uint8_t v___x_3945_; 
v___x_3945_ = lean_nat_dec_le(v___x_3943_, v___x_3943_);
if (v___x_3945_ == 0)
{
if (v___x_3944_ == 0)
{
return v_x_3940_;
}
else
{
size_t v___x_3946_; size_t v___x_3947_; lean_object* v___x_3948_; 
v___x_3946_ = ((size_t)0ULL);
v___x_3947_ = lean_usize_of_nat(v___x_3943_);
v___x_3948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3941_, v___x_3946_, v___x_3947_, v_x_3940_);
return v___x_3948_;
}
}
else
{
size_t v___x_3949_; size_t v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = ((size_t)0ULL);
v___x_3950_ = lean_usize_of_nat(v___x_3943_);
v___x_3951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3941_, v___x_3949_, v___x_3950_, v_x_3940_);
return v___x_3951_;
}
}
}
else
{
lean_object* v_vs_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v_vs_3952_ = lean_ctor_get(v_x_3939_, 0);
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = lean_array_get_size(v_vs_3952_);
v___x_3955_ = lean_nat_dec_lt(v___x_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
return v_x_3940_;
}
else
{
uint8_t v___x_3956_; 
v___x_3956_ = lean_nat_dec_le(v___x_3954_, v___x_3954_);
if (v___x_3956_ == 0)
{
if (v___x_3955_ == 0)
{
return v_x_3940_;
}
else
{
size_t v___x_3957_; size_t v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = ((size_t)0ULL);
v___x_3958_ = lean_usize_of_nat(v___x_3954_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3952_, v___x_3957_, v___x_3958_, v_x_3940_);
return v___x_3959_;
}
}
else
{
size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = lean_usize_of_nat(v___x_3954_);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3952_, v___x_3960_, v___x_3961_, v_x_3940_);
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3963_, size_t v_i_3964_, size_t v_stop_3965_, lean_object* v_b_3966_){
_start:
{
uint8_t v___x_3967_; 
v___x_3967_ = lean_usize_dec_eq(v_i_3964_, v_stop_3965_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; size_t v___x_3970_; size_t v___x_3971_; 
v___x_3968_ = lean_array_uget_borrowed(v_as_3963_, v_i_3964_);
v___x_3969_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3968_, v_b_3966_);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3964_, v___x_3970_);
v_i_3964_ = v___x_3971_;
v_b_3966_ = v___x_3969_;
goto _start;
}
else
{
return v_b_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3973_, lean_object* v_i_3974_, lean_object* v_stop_3975_, lean_object* v_b_3976_){
_start:
{
size_t v_i_boxed_3977_; size_t v_stop_boxed_3978_; lean_object* v_res_3979_; 
v_i_boxed_3977_ = lean_unbox_usize(v_i_3974_);
lean_dec(v_i_3974_);
v_stop_boxed_3978_ = lean_unbox_usize(v_stop_3975_);
lean_dec(v_stop_3975_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3973_, v_i_boxed_3977_, v_stop_boxed_3978_, v_b_3976_);
lean_dec_ref(v_as_3973_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3980_, lean_object* v_x_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3980_, v_x_3981_);
lean_dec_ref(v_x_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3983_, size_t v_x_3984_, size_t v_x_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3983_) == 0)
{
lean_object* v_cs_3987_; lean_object* v___x_3988_; size_t v___x_3989_; lean_object* v_j_3990_; lean_object* v___x_3991_; size_t v___x_3992_; size_t v___x_3993_; size_t v___x_3994_; size_t v___x_3995_; size_t v___x_3996_; size_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v_cs_3987_ = lean_ctor_get(v_x_3983_, 0);
v___x_3988_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3989_ = lean_usize_shift_right(v_x_3984_, v_x_3985_);
v_j_3990_ = lean_usize_to_nat(v___x_3989_);
v___x_3991_ = lean_array_get_borrowed(v___x_3988_, v_cs_3987_, v_j_3990_);
v___x_3992_ = ((size_t)1ULL);
v___x_3993_ = lean_usize_shift_left(v___x_3992_, v_x_3985_);
v___x_3994_ = lean_usize_sub(v___x_3993_, v___x_3992_);
v___x_3995_ = lean_usize_land(v_x_3984_, v___x_3994_);
v___x_3996_ = ((size_t)5ULL);
v___x_3997_ = lean_usize_sub(v_x_3985_, v___x_3996_);
v___x_3998_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3991_, v___x_3995_, v___x_3997_, v_x_3986_);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_nat_add(v_j_3990_, v___x_3999_);
lean_dec(v_j_3990_);
v___x_4001_ = lean_array_get_size(v_cs_3987_);
v___x_4002_ = lean_nat_dec_lt(v___x_4000_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_dec(v___x_4000_);
return v___x_3998_;
}
else
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_nat_dec_le(v___x_4001_, v___x_4001_);
if (v___x_4003_ == 0)
{
if (v___x_4002_ == 0)
{
lean_dec(v___x_4000_);
return v___x_3998_;
}
else
{
size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_usize_of_nat(v___x_4000_);
lean_dec(v___x_4000_);
v___x_4005_ = lean_usize_of_nat(v___x_4001_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3987_, v___x_4004_, v___x_4005_, v___x_3998_);
return v___x_4006_;
}
}
else
{
size_t v___x_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = lean_usize_of_nat(v___x_4000_);
lean_dec(v___x_4000_);
v___x_4008_ = lean_usize_of_nat(v___x_4001_);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3987_, v___x_4007_, v___x_4008_, v___x_3998_);
return v___x_4009_;
}
}
}
else
{
lean_object* v_vs_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_vs_4010_ = lean_ctor_get(v_x_3983_, 0);
v___x_4011_ = lean_usize_to_nat(v_x_3984_);
v___x_4012_ = lean_array_get_size(v_vs_4010_);
v___x_4013_ = lean_nat_dec_lt(v___x_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
lean_dec(v___x_4011_);
return v_x_3986_;
}
else
{
uint8_t v___x_4014_; 
v___x_4014_ = lean_nat_dec_le(v___x_4012_, v___x_4012_);
if (v___x_4014_ == 0)
{
if (v___x_4013_ == 0)
{
lean_dec(v___x_4011_);
return v_x_3986_;
}
else
{
size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_usize_of_nat(v___x_4011_);
lean_dec(v___x_4011_);
v___x_4016_ = lean_usize_of_nat(v___x_4012_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_4010_, v___x_4015_, v___x_4016_, v_x_3986_);
return v___x_4017_;
}
}
else
{
size_t v___x_4018_; size_t v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = lean_usize_of_nat(v___x_4011_);
lean_dec(v___x_4011_);
v___x_4019_ = lean_usize_of_nat(v___x_4012_);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_4010_, v___x_4018_, v___x_4019_, v_x_3986_);
return v___x_4020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_){
_start:
{
size_t v_x_1523__boxed_4025_; size_t v_x_1524__boxed_4026_; lean_object* v_res_4027_; 
v_x_1523__boxed_4025_ = lean_unbox_usize(v_x_4022_);
lean_dec(v_x_4022_);
v_x_1524__boxed_4026_ = lean_unbox_usize(v_x_4023_);
lean_dec(v_x_4023_);
v_res_4027_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_4021_, v_x_1523__boxed_4025_, v_x_1524__boxed_4026_, v_x_4024_);
lean_dec_ref(v_x_4021_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_4028_, lean_object* v_init_4029_, lean_object* v_start_4030_){
_start:
{
lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4031_ = lean_unsigned_to_nat(0u);
v___x_4032_ = lean_nat_dec_eq(v_start_4030_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v_root_4033_; lean_object* v_tail_4034_; size_t v_shift_4035_; lean_object* v_tailOff_4036_; uint8_t v___x_4037_; 
v_root_4033_ = lean_ctor_get(v_t_4028_, 0);
v_tail_4034_ = lean_ctor_get(v_t_4028_, 1);
v_shift_4035_ = lean_ctor_get_usize(v_t_4028_, 4);
v_tailOff_4036_ = lean_ctor_get(v_t_4028_, 3);
v___x_4037_ = lean_nat_dec_le(v_tailOff_4036_, v_start_4030_);
if (v___x_4037_ == 0)
{
size_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4038_ = lean_usize_of_nat(v_start_4030_);
v___x_4039_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_4033_, v___x_4038_, v_shift_4035_, v_init_4029_);
v___x_4040_ = lean_array_get_size(v_tail_4034_);
v___x_4041_ = lean_nat_dec_lt(v___x_4031_, v___x_4040_);
if (v___x_4041_ == 0)
{
return v___x_4039_;
}
else
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_nat_dec_le(v___x_4040_, v___x_4040_);
if (v___x_4042_ == 0)
{
if (v___x_4041_ == 0)
{
return v___x_4039_;
}
else
{
size_t v___x_4043_; size_t v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = ((size_t)0ULL);
v___x_4044_ = lean_usize_of_nat(v___x_4040_);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4034_, v___x_4043_, v___x_4044_, v___x_4039_);
return v___x_4045_;
}
}
else
{
size_t v___x_4046_; size_t v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = ((size_t)0ULL);
v___x_4047_ = lean_usize_of_nat(v___x_4040_);
v___x_4048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4034_, v___x_4046_, v___x_4047_, v___x_4039_);
return v___x_4048_;
}
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4049_ = lean_nat_sub(v_start_4030_, v_tailOff_4036_);
v___x_4050_ = lean_array_get_size(v_tail_4034_);
v___x_4051_ = lean_nat_dec_lt(v___x_4049_, v___x_4050_);
if (v___x_4051_ == 0)
{
lean_dec(v___x_4049_);
return v_init_4029_;
}
else
{
uint8_t v___x_4052_; 
v___x_4052_ = lean_nat_dec_le(v___x_4050_, v___x_4050_);
if (v___x_4052_ == 0)
{
if (v___x_4051_ == 0)
{
lean_dec(v___x_4049_);
return v_init_4029_;
}
else
{
size_t v___x_4053_; size_t v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = lean_usize_of_nat(v___x_4049_);
lean_dec(v___x_4049_);
v___x_4054_ = lean_usize_of_nat(v___x_4050_);
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4034_, v___x_4053_, v___x_4054_, v_init_4029_);
return v___x_4055_;
}
}
else
{
size_t v___x_4056_; size_t v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = lean_usize_of_nat(v___x_4049_);
lean_dec(v___x_4049_);
v___x_4057_ = lean_usize_of_nat(v___x_4050_);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4034_, v___x_4056_, v___x_4057_, v_init_4029_);
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_root_4059_; lean_object* v_tail_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; 
v_root_4059_ = lean_ctor_get(v_t_4028_, 0);
v_tail_4060_ = lean_ctor_get(v_t_4028_, 1);
v___x_4061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_4059_, v_init_4029_);
v___x_4062_ = lean_array_get_size(v_tail_4060_);
v___x_4063_ = lean_nat_dec_lt(v___x_4031_, v___x_4062_);
if (v___x_4063_ == 0)
{
return v___x_4061_;
}
else
{
uint8_t v___x_4064_; 
v___x_4064_ = lean_nat_dec_le(v___x_4062_, v___x_4062_);
if (v___x_4064_ == 0)
{
if (v___x_4063_ == 0)
{
return v___x_4061_;
}
else
{
size_t v___x_4065_; size_t v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((size_t)0ULL);
v___x_4066_ = lean_usize_of_nat(v___x_4062_);
v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4060_, v___x_4065_, v___x_4066_, v___x_4061_);
return v___x_4067_;
}
}
else
{
size_t v___x_4068_; size_t v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = ((size_t)0ULL);
v___x_4069_ = lean_usize_of_nat(v___x_4062_);
v___x_4070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4060_, v___x_4068_, v___x_4069_, v___x_4061_);
return v___x_4070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_4071_, lean_object* v_init_4072_, lean_object* v_start_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_4071_, v_init_4072_, v_start_4073_);
lean_dec(v_start_4073_);
lean_dec_ref(v_t_4071_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_4075_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v_unreported_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4089_; 
v___x_4076_ = lean_unsigned_to_nat(32u);
v___x_4077_ = lean_mk_empty_array_with_capacity(v___x_4076_);
lean_dec_ref(v___x_4077_);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_4080_ = lean_ctor_get(v_log_4075_, 1);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_log_4075_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; lean_object* v_unused_4091_; 
v_unused_4090_ = lean_ctor_get(v_log_4075_, 2);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_log_4075_, 0);
lean_dec(v_unused_4091_);
v___x_4082_ = v_log_4075_;
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_unreported_4080_);
lean_dec(v_log_4075_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_4080_, v___x_4079_, v___x_4078_);
lean_dec_ref(v_unreported_4080_);
v___x_4085_ = l_Lean_NameSet_empty;
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 2, v___x_4085_);
lean_ctor_set(v___x_4082_, 1, v___x_4084_);
lean_ctor_set(v___x_4082_, 0, v___x_4079_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4079_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_4092_, lean_object* v_log_4093_, lean_object* v_f_4094_){
_start:
{
lean_object* v_unreported_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_unreported_4095_ = lean_ctor_get(v_log_4093_, 1);
lean_inc_ref(v_unreported_4095_);
lean_dec_ref(v_log_4093_);
v___x_4096_ = lean_unsigned_to_nat(0u);
v___x_4097_ = l_Lean_PersistentArray_forM___redArg(v_inst_4092_, v_unreported_4095_, v_f_4094_, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_4098_, lean_object* v_inst_4099_, lean_object* v_log_4100_, lean_object* v_f_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_MessageLog_forM___redArg(v_inst_4099_, v_log_4100_, v_f_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_4103_){
_start:
{
lean_object* v_unreported_4104_; lean_object* v___x_4105_; 
v_unreported_4104_ = lean_ctor_get(v_log_4103_, 1);
v___x_4105_ = l_Lean_PersistentArray_toList___redArg(v_unreported_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_MessageLog_toList(v_log_4106_);
lean_dec_ref(v_log_4106_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4108_){
_start:
{
lean_object* v_unreported_4109_; lean_object* v___x_4110_; 
v_unreported_4109_ = lean_ctor_get(v_log_4108_, 1);
v___x_4110_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_MessageLog_toArray(v_log_4111_);
lean_dec_ref(v_log_4111_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4113_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_unsigned_to_nat(2u);
v___x_4115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v_msg_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4116_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v_msg_4116_);
v___x_4119_ = l_Lean_MessageData_nestD(v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4120_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = l_Lean_MessageData_ofExpr(v_e_4120_);
v___x_4122_ = l_Lean_indentD(v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4123_, lean_object* v_msg_4124_){
_start:
{
lean_object* v_env_4126_; lean_object* v_mctx_4127_; lean_object* v_lctx_4128_; lean_object* v_opts_4129_; lean_object* v_currNamespace_4130_; lean_object* v_openDecls_4131_; lean_object* v___x_4132_; lean_object* v_msg_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v_env_4126_ = lean_ctor_get(v_ctx_4123_, 0);
v_mctx_4127_ = lean_ctor_get(v_ctx_4123_, 1);
v_lctx_4128_ = lean_ctor_get(v_ctx_4123_, 2);
v_opts_4129_ = lean_ctor_get(v_ctx_4123_, 3);
v_currNamespace_4130_ = lean_ctor_get(v_ctx_4123_, 4);
v_openDecls_4131_ = lean_ctor_get(v_ctx_4123_, 5);
lean_inc(v_openDecls_4131_);
lean_inc(v_currNamespace_4130_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_currNamespace_4130_);
lean_ctor_set(v___x_4132_, 1, v_openDecls_4131_);
v_msg_4133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4133_, 0, v___x_4132_);
lean_ctor_set(v_msg_4133_, 1, v_msg_4124_);
lean_inc_ref(v_opts_4129_);
lean_inc_ref(v_lctx_4128_);
lean_inc_ref(v_mctx_4127_);
lean_inc_ref(v_env_4126_);
v___x_4134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4134_, 0, v_env_4126_);
lean_ctor_set(v___x_4134_, 1, v_mctx_4127_);
lean_ctor_set(v___x_4134_, 2, v_lctx_4128_);
lean_ctor_set(v___x_4134_, 3, v_opts_4129_);
v___x_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
v___x_4136_ = l_Lean_MessageData_format(v_msg_4133_, v___x_4135_);
v___x_4137_ = l_Std_Format_defWidth;
v___x_4138_ = lean_unsigned_to_nat(0u);
v___x_4139_ = l_Std_Format_pretty(v___x_4136_, v___x_4137_, v___x_4138_, v___x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4140_, lean_object* v_msg_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4140_, v_msg_4141_);
lean_dec_ref(v_ctx_4140_);
return v_res_4143_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4144_, lean_object* v_a_4145_, uint8_t v_b_4146_){
_start:
{
lean_object* v_str_4147_; lean_object* v_startInclusive_4148_; lean_object* v_endExclusive_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_str_4147_ = lean_ctor_get(v_s_4144_, 0);
v_startInclusive_4148_ = lean_ctor_get(v_s_4144_, 1);
v_endExclusive_4149_ = lean_ctor_get(v_s_4144_, 2);
v___x_4150_ = lean_nat_sub(v_endExclusive_4149_, v_startInclusive_4148_);
v___x_4151_ = lean_nat_dec_eq(v_a_4145_, v___x_4150_);
lean_dec(v___x_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; uint32_t v___x_4153_; uint32_t v___x_4154_; uint8_t v___x_4155_; 
v___x_4152_ = lean_nat_add(v_startInclusive_4148_, v_a_4145_);
lean_dec(v_a_4145_);
v___x_4153_ = lean_string_utf8_get_fast(v_str_4147_, v___x_4152_);
v___x_4154_ = 10;
v___x_4155_ = lean_uint32_dec_eq(v___x_4153_, v___x_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_string_utf8_next_fast(v_str_4147_, v___x_4152_);
lean_dec(v___x_4152_);
v___x_4157_ = lean_nat_sub(v___x_4156_, v_startInclusive_4148_);
v_a_4145_ = v___x_4157_;
v_b_4146_ = v___x_4155_;
goto _start;
}
else
{
lean_dec(v___x_4152_);
return v___x_4155_;
}
}
else
{
lean_dec(v_a_4145_);
return v_b_4146_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4159_, lean_object* v_a_4160_, lean_object* v_b_4161_){
_start:
{
uint8_t v_b_boxed_4162_; uint8_t v_res_4163_; lean_object* v_r_4164_; 
v_b_boxed_4162_ = lean_unbox(v_b_4161_);
v_res_4163_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4159_, v_a_4160_, v_b_boxed_4162_);
lean_dec_ref(v_s_4159_);
v_r_4164_ = lean_box(v_res_4163_);
return v_r_4164_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4165_){
_start:
{
lean_object* v_searcher_4166_; uint8_t v___x_4167_; uint8_t v___x_4168_; 
v_searcher_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = 0;
v___x_4168_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4165_, v_searcher_4166_, v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4169_){
_start:
{
uint8_t v_res_4170_; lean_object* v_r_4171_; 
v_res_4170_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4169_);
lean_dec_ref(v_s_4169_);
v_r_4171_ = lean_box(v_res_4170_);
return v_r_4171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4172_, lean_object* v_val_4173_, lean_object* v_a_4174_, lean_object* v_b_4175_){
_start:
{
lean_object* v_startInclusive_4176_; lean_object* v_endExclusive_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_startInclusive_4176_ = lean_ctor_get(v___x_4172_, 1);
v_endExclusive_4177_ = lean_ctor_get(v___x_4172_, 2);
v___x_4178_ = lean_nat_sub(v_endExclusive_4177_, v_startInclusive_4176_);
v___x_4179_ = lean_nat_dec_eq(v_a_4174_, v___x_4178_);
lean_dec(v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4180_ = lean_string_utf8_next_fast(v_val_4173_, v_a_4174_);
lean_dec(v_a_4174_);
v___x_4181_ = lean_unsigned_to_nat(1u);
v___x_4182_ = lean_nat_add(v_b_4175_, v___x_4181_);
lean_dec(v_b_4175_);
v_a_4174_ = v___x_4180_;
v_b_4175_ = v___x_4182_;
goto _start;
}
else
{
lean_dec(v_a_4174_);
return v_b_4175_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4184_, lean_object* v_val_4185_, lean_object* v_a_4186_, lean_object* v_b_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4184_, v_val_4185_, v_a_4186_, v_b_4187_);
lean_dec_ref(v_val_4185_);
lean_dec_ref(v___x_4184_);
return v_res_4188_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__1));
v___x_4193_ = l_Lean_MessageData_ofFormat(v___x_4192_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__4));
v___x_4198_ = l_Lean_MessageData_ofFormat(v___x_4197_);
return v___x_4198_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4200_ = l_Lean_MessageData_ofFormat(v___x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4201_, lean_object* v_maxInlineLength_4202_, lean_object* v_ctx_4203_){
_start:
{
lean_object* v_msg_4205_; lean_object* v___x_4206_; uint8_t v___y_4208_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v_msg_4205_ = l_Lean_MessageData_ofExpr(v_e_4201_);
lean_inc_ref(v_msg_4205_);
v___x_4206_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4203_, v_msg_4205_);
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = lean_string_utf8_byte_size(v___x_4206_);
lean_inc_ref(v___x_4206_);
v___x_4218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4206_);
lean_ctor_set(v___x_4218_, 1, v___x_4216_);
lean_ctor_set(v___x_4218_, 2, v___x_4217_);
v___x_4219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4218_, v___x_4206_, v___x_4216_, v___x_4216_);
lean_dec_ref(v___x_4206_);
v___x_4220_ = lean_nat_dec_lt(v_maxInlineLength_4202_, v___x_4219_);
lean_dec(v___x_4219_);
if (v___x_4220_ == 0)
{
uint8_t v___x_4221_; 
v___x_4221_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4218_);
lean_dec_ref_known(v___x_4218_, 3);
v___y_4208_ = v___x_4221_;
goto v___jp_4207_;
}
else
{
lean_dec_ref_known(v___x_4218_, 3);
v___y_4208_ = v___x_4220_;
goto v___jp_4207_;
}
v___jp_4207_:
{
if (v___y_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4209_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
lean_ctor_set(v___x_4210_, 1, v_msg_4205_);
v___x_4211_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4210_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = l_Lean_indentD(v_msg_4205_);
v___x_4214_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
return v___x_4215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4222_, lean_object* v_maxInlineLength_4223_, lean_object* v_ctx_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_inlineExpr___lam__0(v_e_4222_, v_maxInlineLength_4223_, v_ctx_4224_);
lean_dec_ref(v_ctx_4224_);
lean_dec(v_maxInlineLength_4223_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4227_, lean_object* v_x_4228_){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4230_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4231_ = l_Lean_MessageData_ofExpr(v_e_4227_);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__5, &l_Lean_inlineExpr___lam__0___closed__5_once, _init_l_Lean_inlineExpr___lam__0___closed__5);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4235_, lean_object* v_x_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_inlineExpr___lam__2(v_e_4235_, v_x_4236_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4239_, lean_object* v_maxInlineLength_4240_){
_start:
{
lean_object* v___f_4241_; lean_object* v___f_4242_; lean_object* v___f_4243_; lean_object* v___x_4244_; 
lean_inc_ref_n(v_e_4239_, 2);
v___f_4241_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4241_, 0, v_e_4239_);
lean_closure_set(v___f_4241_, 1, v_maxInlineLength_4240_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4242_, 0, v_e_4239_);
v___f_4243_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4243_, 0, v_e_4239_);
v___x_4244_ = l_Lean_MessageData_lazy(v___f_4241_, v___f_4242_, v___f_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4245_, lean_object* v_val_4246_, lean_object* v_inst_4247_, lean_object* v_R_4248_, lean_object* v_a_4249_, lean_object* v_b_4250_, lean_object* v_c_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4245_, v_val_4246_, v_a_4249_, v_b_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4253_, lean_object* v_val_4254_, lean_object* v_inst_4255_, lean_object* v_R_4256_, lean_object* v_a_4257_, lean_object* v_b_4258_, lean_object* v_c_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4253_, v_val_4254_, v_inst_4255_, v_R_4256_, v_a_4257_, v_b_4258_, v_c_4259_);
lean_dec_ref(v_val_4254_);
lean_dec_ref(v___x_4253_);
return v_res_4260_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4261_, lean_object* v_inst_4262_, lean_object* v_R_4263_, lean_object* v_a_4264_, uint8_t v_b_4265_, lean_object* v_c_4266_){
_start:
{
uint8_t v___x_4267_; 
v___x_4267_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4261_, v_a_4264_, v_b_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4268_, lean_object* v_inst_4269_, lean_object* v_R_4270_, lean_object* v_a_4271_, lean_object* v_b_4272_, lean_object* v_c_4273_){
_start:
{
uint8_t v_b_boxed_4274_; uint8_t v_res_4275_; lean_object* v_r_4276_; 
v_b_boxed_4274_ = lean_unbox(v_b_4272_);
v_res_4275_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4268_, v_inst_4269_, v_R_4270_, v_a_4271_, v_b_boxed_4274_, v_c_4273_);
lean_dec_ref(v_s_4268_);
v_r_4276_ = lean_box(v_res_4275_);
return v_r_4276_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4281_ = l_Lean_MessageData_ofFormat(v___x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4282_, lean_object* v_maxInlineLength_4283_, lean_object* v_ctx_4284_){
_start:
{
lean_object* v_msg_4286_; lean_object* v___x_4287_; uint8_t v___y_4289_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_msg_4286_ = l_Lean_MessageData_ofExpr(v_e_4282_);
lean_inc_ref(v_msg_4286_);
v___x_4287_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4284_, v_msg_4286_);
v___x_4295_ = lean_unsigned_to_nat(0u);
v___x_4296_ = lean_string_utf8_byte_size(v___x_4287_);
lean_inc_ref(v___x_4287_);
v___x_4297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4287_);
lean_ctor_set(v___x_4297_, 1, v___x_4295_);
lean_ctor_set(v___x_4297_, 2, v___x_4296_);
v___x_4298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4297_, v___x_4287_, v___x_4295_, v___x_4295_);
lean_dec_ref(v___x_4287_);
v___x_4299_ = lean_nat_dec_lt(v_maxInlineLength_4283_, v___x_4298_);
lean_dec(v___x_4298_);
if (v___x_4299_ == 0)
{
uint8_t v___x_4300_; 
v___x_4300_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4297_);
lean_dec_ref_known(v___x_4297_, 3);
v___y_4289_ = v___x_4300_;
goto v___jp_4288_;
}
else
{
lean_dec_ref_known(v___x_4297_, 3);
v___y_4289_ = v___x_4299_;
goto v___jp_4288_;
}
v___jp_4288_:
{
if (v___y_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4290_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v_msg_4286_);
v___x_4292_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_indentD(v_msg_4286_);
return v___x_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4301_, lean_object* v_maxInlineLength_4302_, lean_object* v_ctx_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_inlineExprTrailing___lam__0(v_e_4301_, v_maxInlineLength_4302_, v_ctx_4303_);
lean_dec_ref(v_ctx_4303_);
lean_dec(v_maxInlineLength_4302_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4306_, lean_object* v_x_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4309_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__2, &l_Lean_inlineExpr___lam__0___closed__2_once, _init_l_Lean_inlineExpr___lam__0___closed__2);
v___x_4310_ = l_Lean_MessageData_ofExpr(v_e_4306_);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4314_, lean_object* v_x_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_inlineExprTrailing___lam__2(v_e_4314_, v_x_4315_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4318_, lean_object* v_maxInlineLength_4319_){
_start:
{
lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
lean_inc_ref_n(v_e_4318_, 2);
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4320_, 0, v_e_4318_);
lean_closure_set(v___f_4320_, 1, v_maxInlineLength_4319_);
v___f_4321_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4321_, 0, v_e_4318_);
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4322_, 0, v_e_4318_);
v___x_4323_ = l_Lean_MessageData_lazy(v___f_4320_, v___f_4321_, v___f_4322_);
return v___x_4323_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4328_ = l_Lean_MessageData_ofFormat(v___x_4327_);
return v___x_4328_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4333_ = l_Lean_MessageData_ofFormat(v___x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4334_){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4335_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v_msg_4334_);
v___x_4337_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4339_, lean_object* v_inst_4340_, lean_object* v_msg_4341_){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_apply_1(v_inst_4339_, v_msg_4341_);
v___x_4343_ = lean_apply_2(v_inst_4340_, lean_box(0), v___x_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4344_, lean_object* v_inst_4345_){
_start:
{
lean_object* v___f_4346_; 
v___f_4346_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4346_, 0, v_inst_4345_);
lean_closure_set(v___f_4346_, 1, v_inst_4344_);
return v___f_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4347_, lean_object* v_n_4348_, lean_object* v_inst_4349_, lean_object* v_inst_4350_){
_start:
{
lean_object* v___f_4351_; 
v___f_4351_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4351_, 0, v_inst_4350_);
lean_closure_set(v___f_4351_, 1, v_inst_4349_);
return v___f_4351_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_unsigned_to_nat(32u);
v___x_4353_ = lean_mk_empty_array_with_capacity(v___x_4352_);
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4355_ = ((size_t)5ULL);
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_unsigned_to_nat(32u);
v___x_4358_ = lean_mk_empty_array_with_capacity(v___x_4357_);
v___x_4359_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4360_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
lean_ctor_set(v___x_4360_, 1, v___x_4358_);
lean_ctor_set(v___x_4360_, 2, v___x_4356_);
lean_ctor_set(v___x_4360_, 3, v___x_4356_);
lean_ctor_set_usize(v___x_4360_, 4, v___x_4355_);
return v___x_4360_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4361_ = lean_box(1);
v___x_4362_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4363_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
lean_ctor_set(v___x_4364_, 1, v___x_4362_);
lean_ctor_set(v___x_4364_, 2, v___x_4361_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4365_, lean_object* v_msgData_4366_, lean_object* v_toPure_4367_, lean_object* v_opts_4368_){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4369_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4370_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4371_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4371_, 0, v_env_4365_);
lean_ctor_set(v___x_4371_, 1, v___x_4369_);
lean_ctor_set(v___x_4371_, 2, v___x_4370_);
lean_ctor_set(v___x_4371_, 3, v_opts_4368_);
v___x_4372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4371_);
lean_ctor_set(v___x_4372_, 1, v_msgData_4366_);
v___x_4373_ = lean_apply_2(v_toPure_4367_, lean_box(0), v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_msgData_4374_, lean_object* v_toPure_4375_, lean_object* v_toBind_4376_, lean_object* v_inst_4377_, lean_object* v_env_4378_){
_start:
{
lean_object* v___f_4379_; lean_object* v___x_4380_; 
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4379_, 0, v_env_4378_);
lean_closure_set(v___f_4379_, 1, v_msgData_4374_);
lean_closure_set(v___f_4379_, 2, v_toPure_4375_);
v___x_4380_ = lean_apply_4(v_toBind_4376_, lean_box(0), lean_box(0), v_inst_4377_, v___f_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4381_, lean_object* v_inst_4382_, lean_object* v_inst_4383_, lean_object* v_msgData_4384_){
_start:
{
lean_object* v_toApplicative_4385_; lean_object* v_toBind_4386_; lean_object* v_getEnv_4387_; lean_object* v_toPure_4388_; lean_object* v___f_4389_; lean_object* v___x_4390_; 
v_toApplicative_4385_ = lean_ctor_get(v_inst_4381_, 0);
lean_inc_ref(v_toApplicative_4385_);
v_toBind_4386_ = lean_ctor_get(v_inst_4381_, 1);
lean_inc_n(v_toBind_4386_, 2);
lean_dec_ref(v_inst_4381_);
v_getEnv_4387_ = lean_ctor_get(v_inst_4382_, 0);
lean_inc(v_getEnv_4387_);
lean_dec_ref(v_inst_4382_);
v_toPure_4388_ = lean_ctor_get(v_toApplicative_4385_, 1);
lean_inc(v_toPure_4388_);
lean_dec_ref(v_toApplicative_4385_);
v___f_4389_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4389_, 0, v_msgData_4384_);
lean_closure_set(v___f_4389_, 1, v_toPure_4388_);
lean_closure_set(v___f_4389_, 2, v_toBind_4386_);
lean_closure_set(v___f_4389_, 3, v_inst_4383_);
v___x_4390_ = lean_apply_4(v_toBind_4386_, lean_box(0), lean_box(0), v_getEnv_4387_, v___f_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4391_, lean_object* v_inst_4392_, lean_object* v_inst_4393_, lean_object* v_inst_4394_, lean_object* v_msgData_4395_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_Lean_addMessageContextPartial___redArg(v_inst_4392_, v_inst_4393_, v_inst_4394_, v_msgData_4395_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4397_, lean_object* v_mctx_4398_, lean_object* v_lctx_4399_, lean_object* v_msgData_4400_, lean_object* v_toPure_4401_, lean_object* v_opts_4402_){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4403_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4403_, 0, v_env_4397_);
lean_ctor_set(v___x_4403_, 1, v_mctx_4398_);
lean_ctor_set(v___x_4403_, 2, v_lctx_4399_);
lean_ctor_set(v___x_4403_, 3, v_opts_4402_);
v___x_4404_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v_msgData_4400_);
v___x_4405_ = lean_apply_2(v_toPure_4401_, lean_box(0), v___x_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_env_4406_, lean_object* v_mctx_4407_, lean_object* v_msgData_4408_, lean_object* v_toPure_4409_, lean_object* v_toBind_4410_, lean_object* v_inst_4411_, lean_object* v_lctx_4412_){
_start:
{
lean_object* v___f_4413_; lean_object* v___x_4414_; 
v___f_4413_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4413_, 0, v_env_4406_);
lean_closure_set(v___f_4413_, 1, v_mctx_4407_);
lean_closure_set(v___f_4413_, 2, v_lctx_4412_);
lean_closure_set(v___f_4413_, 3, v_msgData_4408_);
lean_closure_set(v___f_4413_, 4, v_toPure_4409_);
v___x_4414_ = lean_apply_4(v_toBind_4410_, lean_box(0), lean_box(0), v_inst_4411_, v___f_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_env_4415_, lean_object* v_msgData_4416_, lean_object* v_toPure_4417_, lean_object* v_toBind_4418_, lean_object* v_inst_4419_, lean_object* v_inst_4420_, lean_object* v_mctx_4421_){
_start:
{
lean_object* v___f_4422_; lean_object* v___x_4423_; 
lean_inc(v_toBind_4418_);
v___f_4422_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4422_, 0, v_env_4415_);
lean_closure_set(v___f_4422_, 1, v_mctx_4421_);
lean_closure_set(v___f_4422_, 2, v_msgData_4416_);
lean_closure_set(v___f_4422_, 3, v_toPure_4417_);
lean_closure_set(v___f_4422_, 4, v_toBind_4418_);
lean_closure_set(v___f_4422_, 5, v_inst_4419_);
v___x_4423_ = lean_apply_4(v_toBind_4418_, lean_box(0), lean_box(0), v_inst_4420_, v___f_4422_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4424_, lean_object* v_msgData_4425_, lean_object* v_toPure_4426_, lean_object* v_toBind_4427_, lean_object* v_inst_4428_, lean_object* v_inst_4429_, lean_object* v_env_4430_){
_start:
{
lean_object* v_getMCtx_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; 
v_getMCtx_4431_ = lean_ctor_get(v_inst_4424_, 0);
lean_inc(v_getMCtx_4431_);
lean_dec_ref(v_inst_4424_);
lean_inc(v_toBind_4427_);
v___f_4432_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4432_, 0, v_env_4430_);
lean_closure_set(v___f_4432_, 1, v_msgData_4425_);
lean_closure_set(v___f_4432_, 2, v_toPure_4426_);
lean_closure_set(v___f_4432_, 3, v_toBind_4427_);
lean_closure_set(v___f_4432_, 4, v_inst_4428_);
lean_closure_set(v___f_4432_, 5, v_inst_4429_);
v___x_4433_ = lean_apply_4(v_toBind_4427_, lean_box(0), lean_box(0), v_getMCtx_4431_, v___f_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4434_, lean_object* v_inst_4435_, lean_object* v_inst_4436_, lean_object* v_inst_4437_, lean_object* v_inst_4438_, lean_object* v_msgData_4439_){
_start:
{
lean_object* v_toApplicative_4440_; lean_object* v_toBind_4441_; lean_object* v_getEnv_4442_; lean_object* v_toPure_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; 
v_toApplicative_4440_ = lean_ctor_get(v_inst_4434_, 0);
lean_inc_ref(v_toApplicative_4440_);
v_toBind_4441_ = lean_ctor_get(v_inst_4434_, 1);
lean_inc_n(v_toBind_4441_, 2);
lean_dec_ref(v_inst_4434_);
v_getEnv_4442_ = lean_ctor_get(v_inst_4435_, 0);
lean_inc(v_getEnv_4442_);
lean_dec_ref(v_inst_4435_);
v_toPure_4443_ = lean_ctor_get(v_toApplicative_4440_, 1);
lean_inc(v_toPure_4443_);
lean_dec_ref(v_toApplicative_4440_);
v___f_4444_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4444_, 0, v_inst_4436_);
lean_closure_set(v___f_4444_, 1, v_msgData_4439_);
lean_closure_set(v___f_4444_, 2, v_toPure_4443_);
lean_closure_set(v___f_4444_, 3, v_toBind_4441_);
lean_closure_set(v___f_4444_, 4, v_inst_4438_);
lean_closure_set(v___f_4444_, 5, v_inst_4437_);
v___x_4445_ = lean_apply_4(v_toBind_4441_, lean_box(0), lean_box(0), v_getEnv_4442_, v___f_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4446_, lean_object* v_inst_4447_, lean_object* v_inst_4448_, lean_object* v_inst_4449_, lean_object* v_inst_4450_, lean_object* v_inst_4451_, lean_object* v_msgData_4452_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_addMessageContextFull___redArg(v_inst_4447_, v_inst_4448_, v_inst_4449_, v_inst_4450_, v_inst_4451_, v_msgData_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4456_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0));
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4458_);
lean_dec_ref(v_s_4458_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4460_, lean_object* v___x_4461_, lean_object* v___x_4462_, lean_object* v_a_4463_, lean_object* v_b_4464_){
_start:
{
lean_object* v_it_4466_; lean_object* v_startInclusive_4467_; lean_object* v_endExclusive_4468_; 
if (lean_obj_tag(v_a_4463_) == 0)
{
lean_object* v_currPos_4474_; lean_object* v_searcher_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4501_; 
v_currPos_4474_ = lean_ctor_get(v_a_4463_, 0);
v_searcher_4475_ = lean_ctor_get(v_a_4463_, 1);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_a_4463_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4477_ = v_a_4463_;
v_isShared_4478_ = v_isSharedCheck_4501_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_searcher_4475_);
lean_inc(v_currPos_4474_);
lean_dec(v_a_4463_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4501_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v_startInclusive_4479_; lean_object* v_endExclusive_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v_startInclusive_4479_ = lean_ctor_get(v___x_4461_, 1);
v_endExclusive_4480_ = lean_ctor_get(v___x_4461_, 2);
v___x_4481_ = lean_nat_sub(v_endExclusive_4480_, v_startInclusive_4479_);
v___x_4482_ = lean_nat_dec_eq(v_searcher_4475_, v___x_4481_);
lean_dec(v___x_4481_);
if (v___x_4482_ == 0)
{
uint32_t v___x_4483_; uint32_t v___x_4484_; uint8_t v___x_4485_; 
v___x_4483_ = 10;
v___x_4484_ = lean_string_utf8_get_fast(v_str_4460_, v_searcher_4475_);
v___x_4485_ = lean_uint32_dec_eq(v___x_4484_, v___x_4483_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4486_ = lean_string_utf8_next_fast(v_str_4460_, v_searcher_4475_);
lean_dec(v_searcher_4475_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 1, v___x_4486_);
v___x_4488_ = v___x_4477_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_currPos_4474_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v___x_4486_);
v___x_4488_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
v_a_4463_ = v___x_4488_;
goto _start;
}
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v_slice_4494_; lean_object* v_nextIt_4496_; 
v___x_4491_ = lean_string_utf8_next_fast(v_str_4460_, v_searcher_4475_);
v___x_4492_ = lean_nat_sub(v___x_4491_, v_searcher_4475_);
v___x_4493_ = lean_nat_add(v_searcher_4475_, v___x_4492_);
lean_dec(v___x_4492_);
v_slice_4494_ = l_String_Slice_subslice_x21(v___x_4461_, v_currPos_4474_, v_searcher_4475_);
lean_inc(v___x_4493_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 1, v___x_4493_);
lean_ctor_set(v___x_4477_, 0, v___x_4493_);
v_nextIt_4496_ = v___x_4477_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4493_);
v_nextIt_4496_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v_startInclusive_4497_; lean_object* v_endExclusive_4498_; 
v_startInclusive_4497_ = lean_ctor_get(v_slice_4494_, 0);
lean_inc(v_startInclusive_4497_);
v_endExclusive_4498_ = lean_ctor_get(v_slice_4494_, 1);
lean_inc(v_endExclusive_4498_);
lean_dec_ref(v_slice_4494_);
v_it_4466_ = v_nextIt_4496_;
v_startInclusive_4467_ = v_startInclusive_4497_;
v_endExclusive_4468_ = v_endExclusive_4498_;
goto v___jp_4465_;
}
}
}
else
{
lean_object* v___x_4500_; 
lean_del_object(v___x_4477_);
lean_dec(v_searcher_4475_);
v___x_4500_ = lean_box(1);
lean_inc(v___x_4462_);
v_it_4466_ = v___x_4500_;
v_startInclusive_4467_ = v_currPos_4474_;
v_endExclusive_4468_ = v___x_4462_;
goto v___jp_4465_;
}
}
}
else
{
lean_dec(v___x_4462_);
return v_b_4464_;
}
v___jp_4465_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = lean_string_utf8_extract_fast(v_str_4460_, v_startInclusive_4467_, v_endExclusive_4468_);
lean_dec(v_endExclusive_4468_);
lean_dec(v_startInclusive_4467_);
v___x_4470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
v___x_4471_ = l_Lean_MessageData_ofFormat(v___x_4470_);
v___x_4472_ = lean_array_push(v_b_4464_, v___x_4471_);
v_a_4463_ = v_it_4466_;
v_b_4464_ = v___x_4472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4502_, lean_object* v___x_4503_, lean_object* v___x_4504_, lean_object* v_a_4505_, lean_object* v_b_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4502_, v___x_4503_, v___x_4504_, v_a_4505_, v_b_4506_);
lean_dec_ref(v___x_4503_);
lean_dec_ref(v_str_4502_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4510_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v_lines_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = lean_string_utf8_byte_size(v_str_4510_);
lean_inc_ref(v_str_4510_);
v___x_4513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4513_, 0, v_str_4510_);
lean_ctor_set(v___x_4513_, 1, v___x_4511_);
lean_ctor_set(v___x_4513_, 2, v___x_4512_);
v_lines_4514_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v___x_4513_);
v___x_4515_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4516_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4510_, v___x_4513_, v___x_4512_, v_lines_4514_, v___x_4515_);
lean_dec_ref_known(v___x_4513_, 3);
lean_dec_ref(v_str_4510_);
v___x_4517_ = lean_array_to_list(v___x_4516_);
v___x_4518_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4519_ = l_Lean_MessageData_joinSep(v___x_4517_, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4520_, lean_object* v___x_4521_, lean_object* v___x_4522_, lean_object* v_inst_4523_, lean_object* v_R_4524_, lean_object* v_a_4525_, lean_object* v_b_4526_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4520_, v___x_4521_, v___x_4522_, v_a_4525_, v_b_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4528_, lean_object* v___x_4529_, lean_object* v___x_4530_, lean_object* v_inst_4531_, lean_object* v_R_4532_, lean_object* v_a_4533_, lean_object* v_b_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4528_, v___x_4529_, v___x_4530_, v_inst_4531_, v_R_4532_, v_a_4533_, v_b_4534_);
lean_dec_ref(v___x_4529_);
lean_dec_ref(v_str_4528_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4536_){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4538_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4538_, 0, lean_box(0));
lean_closure_set(v___x_4538_, 1, lean_box(0));
lean_closure_set(v___x_4538_, 2, lean_box(0));
lean_closure_set(v___x_4538_, 3, v___x_4537_);
lean_closure_set(v___x_4538_, 4, v_inst_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4539_, lean_object* v_inst_4540_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4548_){
_start:
{
lean_object* v___f_4549_; 
v___f_4549_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_instToMessageDataTSyntax(v_k_4550_);
lean_dec(v_k_4550_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4556_, lean_object* v_as_4557_){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = lean_box(0);
v___x_4559_ = l_List_mapTR_loop___redArg(v_inst_4556_, v_as_4557_, v___x_4558_);
v___x_4560_ = l_Lean_MessageData_ofList(v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4561_){
_start:
{
lean_object* v___f_4562_; 
v___f_4562_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4562_, 0, v_inst_4561_);
return v___f_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4563_, lean_object* v_inst_4564_){
_start:
{
lean_object* v___f_4565_; 
v___f_4565_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4565_, 0, v_inst_4564_);
return v___f_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4566_, lean_object* v_as_4567_){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4568_ = lean_array_to_list(v_as_4567_);
v___x_4569_ = lean_box(0);
v___x_4570_ = l_List_mapTR_loop___redArg(v_inst_4566_, v___x_4568_, v___x_4569_);
v___x_4571_ = l_Lean_MessageData_ofList(v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4572_){
_start:
{
lean_object* v___f_4573_; 
v___f_4573_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4573_, 0, v_inst_4572_);
return v___f_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4574_, lean_object* v_inst_4575_){
_start:
{
lean_object* v___f_4576_; 
v___f_4576_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4576_, 0, v_inst_4575_);
return v___f_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4577_, lean_object* v_acc_4578_, lean_object* v_recur_4579_){
_start:
{
lean_object* v_array_4580_; lean_object* v_start_4581_; lean_object* v_stop_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4595_; 
v_array_4580_ = lean_ctor_get(v_it_4577_, 0);
v_start_4581_ = lean_ctor_get(v_it_4577_, 1);
v_stop_4582_ = lean_ctor_get(v_it_4577_, 2);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_it_4577_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4584_ = v_it_4577_;
v_isShared_4585_ = v_isSharedCheck_4595_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_stop_4582_);
lean_inc(v_start_4581_);
lean_inc(v_array_4580_);
lean_dec(v_it_4577_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4595_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
uint8_t v___x_4586_; 
v___x_4586_ = lean_nat_dec_lt(v_start_4581_, v_stop_4582_);
if (v___x_4586_ == 0)
{
lean_del_object(v___x_4584_);
lean_dec(v_stop_4582_);
lean_dec(v_start_4581_);
lean_dec_ref(v_array_4580_);
lean_dec_ref(v_recur_4579_);
return v_acc_4578_;
}
else
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4587_ = lean_unsigned_to_nat(1u);
v___x_4588_ = lean_nat_add(v_start_4581_, v___x_4587_);
lean_inc_ref(v_array_4580_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 1, v___x_4588_);
v___x_4590_ = v___x_4584_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_array_4580_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4588_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_stop_4582_);
v___x_4590_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4591_ = lean_array_fget(v_array_4580_, v_start_4581_);
lean_dec(v_start_4581_);
lean_dec_ref(v_array_4580_);
v___x_4592_ = lean_array_push(v_acc_4578_, v___x_4591_);
v___x_4593_ = lean_apply_3(v_recur_4579_, v___x_4590_, v___x_4592_, lean_box(0));
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4598_, lean_object* v_inst_4599_, lean_object* v_as_4600_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4601_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4598_, v_as_4600_, v___x_4601_);
v___x_4603_ = lean_array_to_list(v___x_4602_);
v___x_4604_ = lean_box(0);
v___x_4605_ = l_List_mapTR_loop___redArg(v_inst_4599_, v___x_4603_, v___x_4604_);
v___x_4606_ = l_Lean_MessageData_ofList(v___x_4605_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4608_){
_start:
{
lean_object* v___f_4609_; lean_object* v___f_4610_; 
v___f_4609_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4610_, 0, v___f_4609_);
lean_closure_set(v___f_4610_, 1, v_inst_4608_);
return v___f_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4611_, lean_object* v_inst_4612_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4612_);
return v___x_4613_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4618_ = l_Lean_MessageData_ofFormat(v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4623_, lean_object* v_x_4624_){
_start:
{
if (lean_obj_tag(v_x_4624_) == 0)
{
lean_object* v___x_4625_; 
lean_dec_ref(v_inst_4623_);
v___x_4625_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4625_;
}
else
{
lean_object* v_val_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v_val_4626_ = lean_ctor_get(v_x_4624_, 0);
lean_inc(v_val_4626_);
lean_dec_ref_known(v_x_4624_, 1);
v___x_4627_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4628_ = lean_apply_1(v_inst_4623_, v_val_4626_);
v___x_4629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4627_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
v___x_4630_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
return v___x_4631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4632_){
_start:
{
lean_object* v___f_4633_; 
v___f_4633_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4633_, 0, v_inst_4632_);
return v___f_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4634_, lean_object* v_inst_4635_){
_start:
{
lean_object* v___f_4636_; 
v___f_4636_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4636_, 0, v_inst_4635_);
return v___f_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4637_, lean_object* v_inst_4638_, lean_object* v_x_4639_){
_start:
{
lean_object* v_fst_4640_; lean_object* v_snd_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4655_; 
v_fst_4640_ = lean_ctor_get(v_x_4639_, 0);
v_snd_4641_ = lean_ctor_get(v_x_4639_, 1);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_x_4639_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4643_ = v_x_4639_;
v_isShared_4644_ = v_isSharedCheck_4655_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_snd_4641_);
lean_inc(v_fst_4640_);
lean_dec(v_x_4639_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4655_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
v___x_4645_ = lean_apply_1(v_inst_4637_, v_fst_4640_);
v___x_4646_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4644_ == 0)
{
lean_ctor_set_tag(v___x_4643_, 7);
lean_ctor_set(v___x_4643_, 1, v___x_4646_);
lean_ctor_set(v___x_4643_, 0, v___x_4645_);
v___x_4648_ = v___x_4643_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4654_, 1, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4649_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
v___x_4651_ = lean_apply_1(v_inst_4638_, v_snd_4641_);
v___x_4652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = l_Lean_MessageData_paren(v___x_4652_);
return v___x_4653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4656_, lean_object* v_inst_4657_){
_start:
{
lean_object* v___f_4658_; 
v___f_4658_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4658_, 0, v_inst_4656_);
lean_closure_set(v___f_4658_, 1, v_inst_4657_);
return v___f_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4659_, lean_object* v_00_u03b2_4660_, lean_object* v_inst_4661_, lean_object* v_inst_4662_){
_start:
{
lean_object* v___f_4663_; 
v___f_4663_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4663_, 0, v_inst_4661_);
lean_closure_set(v___f_4663_, 1, v_inst_4662_);
return v___f_4663_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4667_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4668_ = l_Lean_MessageData_ofFormat(v___x_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4669_){
_start:
{
if (lean_obj_tag(v_x_4669_) == 0)
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4670_;
}
else
{
lean_object* v_val_4671_; lean_object* v___x_4672_; 
v_val_4671_ = lean_ctor_get(v_x_4669_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v_x_4669_, 1);
v___x_4672_ = l_Lean_MessageData_ofExpr(v_val_4671_);
return v___x_4672_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_150_));
v___x_4707_ = l_String_toRawSubstring_x27(v___x_4706_);
return v___x_4707_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4723_ = l_String_toRawSubstring_x27(v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4740_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4737_);
v___x_4741_ = l_Lean_Syntax_isOfKind(v_x_4737_, v___x_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_dec(v_x_4737_);
v___x_4742_ = lean_box(1);
v___x_4743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
lean_ctor_set(v___x_4743_, 1, v_a_4739_);
return v___x_4743_;
}
else
{
lean_object* v_quotContext_4744_; lean_object* v_currMacroScope_4745_; lean_object* v_ref_4746_; lean_object* v___x_4747_; lean_object* v_interpStr_4748_; uint8_t v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v_quotContext_4744_ = lean_ctor_get(v_a_4738_, 1);
v_currMacroScope_4745_ = lean_ctor_get(v_a_4738_, 2);
v_ref_4746_ = lean_ctor_get(v_a_4738_, 5);
v___x_4747_ = lean_unsigned_to_nat(1u);
v_interpStr_4748_ = l_Lean_Syntax_getArg(v_x_4737_, v___x_4747_);
lean_dec(v_x_4737_);
v___x_4749_ = 0;
v___x_4750_ = l_Lean_SourceInfo_fromRef(v_ref_4746_, v___x_4749_);
v___x_4751_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4752_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4745_, 2);
lean_inc_n(v_quotContext_4744_, 2);
v___x_4753_ = l_Lean_addMacroScope(v_quotContext_4744_, v___x_4752_, v_currMacroScope_4745_);
v___x_4754_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4750_);
v___x_4755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4750_);
lean_ctor_set(v___x_4755_, 1, v___x_4751_);
lean_ctor_set(v___x_4755_, 2, v___x_4753_);
lean_ctor_set(v___x_4755_, 3, v___x_4754_);
v___x_4756_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4757_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4758_ = l_Lean_addMacroScope(v_quotContext_4744_, v___x_4757_, v_currMacroScope_4745_);
v___x_4759_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4760_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4750_);
lean_ctor_set(v___x_4760_, 1, v___x_4756_);
lean_ctor_set(v___x_4760_, 2, v___x_4758_);
lean_ctor_set(v___x_4760_, 3, v___x_4759_);
lean_inc_ref(v___x_4760_);
v___x_4761_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4748_, v___x_4755_, v___x_4760_, v___x_4760_, v_a_4738_, v_a_4739_);
lean_dec(v_interpStr_4748_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_a_4763_ = lean_ctor_get(v___x_4761_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4761_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4762_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4779_; 
v_a_4771_ = lean_ctor_get(v___x_4761_, 0);
v_a_4772_ = lean_ctor_get(v___x_4761_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4774_ = v___x_4761_;
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_inc(v_a_4771_);
lean_dec(v___x_4761_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4771_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_a_4772_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4780_, v_a_4781_, v_a_4782_);
lean_dec_ref(v_a_4781_);
return v_res_4783_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4786_ = l_Lean_stringToMessageData(v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4787_){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4788_ = lean_array_to_list(v_msgs_4787_);
v___x_4789_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4790_ = l_Lean_MessageData_joinSep(v___x_4788_, v___x_4789_);
v___x_4791_ = l_Lean_indentD(v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4792_, lean_object* v_lctx_4793_, lean_object* v_opts_4794_, lean_object* v_msg_4795_){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4796_ = lean_elab_environment_of_kernel_env(v_env_4792_);
v___x_4797_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4798_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4796_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
lean_ctor_set(v___x_4798_, 2, v_lctx_4793_);
lean_ctor_set(v___x_4798_, 3, v_opts_4794_);
v___x_4799_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
lean_ctor_set(v___x_4799_, 1, v_msg_4795_);
return v___x_4799_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4802_ = l_Lean_stringToMessageData(v___x_4801_);
return v___x_4802_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4805_ = l_Lean_stringToMessageData(v___x_4804_);
return v___x_4805_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4808_ = l_Lean_stringToMessageData(v___x_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4809_, lean_object* v_n_4810_, lean_object* v_expectedType_4811_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4812_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4813_ = l_Lean_MessageData_ofName(v_n_4810_);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4814_);
lean_ctor_set(v___x_4816_, 1, v___x_4815_);
v___x_4817_ = l_Lean_indentExpr(v_givenType_4809_);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = l_Lean_indentExpr(v_expectedType_4811_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
return v___x_4822_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4823_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4824_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4826_ = lean_box(1);
v___x_4827_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4828_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
lean_ctor_set(v___x_4829_, 1, v___x_4827_);
lean_ctor_set(v___x_4829_, 2, v___x_4826_);
return v___x_4829_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__3));
v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
return v___x_4832_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__5));
v___x_4835_ = l_Lean_stringToMessageData(v___x_4834_);
return v___x_4835_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__7));
v___x_4838_ = l_Lean_stringToMessageData(v___x_4837_);
return v___x_4838_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__10));
v___x_4843_ = l_Lean_MessageData_ofFormat(v___x_4842_);
return v___x_4843_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__12));
v___x_4846_ = l_Lean_stringToMessageData(v___x_4845_);
return v___x_4846_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__14));
v___x_4849_ = l_Lean_stringToMessageData(v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__17(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__16));
v___x_4852_ = l_Lean_stringToMessageData(v___x_4851_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__19(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__18));
v___x_4855_ = l_Lean_stringToMessageData(v___x_4854_);
return v___x_4855_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__21(void){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4857_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__20));
v___x_4858_ = l_Lean_stringToMessageData(v___x_4857_);
return v___x_4858_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__23(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__22));
v___x_4861_ = l_Lean_stringToMessageData(v___x_4860_);
return v___x_4861_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__25(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__24));
v___x_4864_ = l_Lean_stringToMessageData(v___x_4863_);
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__27(void){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__26));
v___x_4867_ = l_Lean_stringToMessageData(v___x_4866_);
return v___x_4867_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__29(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__28));
v___x_4870_ = l_Lean_stringToMessageData(v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__31(void){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__30));
v___x_4873_ = l_Lean_stringToMessageData(v___x_4872_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__33(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__32));
v___x_4876_ = l_Lean_stringToMessageData(v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__35(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__34));
v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__37(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__36));
v___x_4882_ = l_Lean_stringToMessageData(v___x_4881_);
return v___x_4882_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__39(void){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__38));
v___x_4885_ = l_Lean_stringToMessageData(v___x_4884_);
return v___x_4885_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__42(void){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__41));
v___x_4890_ = l_Lean_MessageData_ofFormat(v___x_4889_);
return v___x_4890_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__45(void){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__44));
v___x_4895_ = l_Lean_MessageData_ofFormat(v___x_4894_);
return v___x_4895_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__48(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__47));
v___x_4900_ = l_Lean_MessageData_ofFormat(v___x_4899_);
return v___x_4900_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__51(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__50));
v___x_4905_ = l_Lean_MessageData_ofFormat(v___x_4904_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4906_, lean_object* v_opts_4907_){
_start:
{
switch(lean_obj_tag(v_e_4906_))
{
case 0:
{
lean_object* v_env_4908_; lean_object* v_name_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4922_; 
v_env_4908_ = lean_ctor_get(v_e_4906_, 0);
v_name_4909_ = lean_ctor_get(v_e_4906_, 1);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_e_4906_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4911_ = v_e_4906_;
v_isShared_4912_ = v_isSharedCheck_4922_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_name_4909_);
lean_inc(v_env_4908_);
lean_dec(v_e_4906_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4922_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4917_; 
v___x_4913_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4914_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__4, &l_Lean_Kernel_Exception_toMessageData___closed__4_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__4);
v___x_4915_ = l_Lean_MessageData_ofName(v_name_4909_);
if (v_isShared_4912_ == 0)
{
lean_ctor_set_tag(v___x_4911_, 7);
lean_ctor_set(v___x_4911_, 1, v___x_4915_);
lean_ctor_set(v___x_4911_, 0, v___x_4914_);
v___x_4917_ = v___x_4911_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4918_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4917_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4908_, v___x_4913_, v_opts_4907_, v___x_4919_);
return v___x_4920_;
}
}
}
case 1:
{
lean_object* v_env_4923_; lean_object* v_name_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4938_; 
v_env_4923_ = lean_ctor_get(v_e_4906_, 0);
v_name_4924_ = lean_ctor_get(v_e_4906_, 1);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_e_4906_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4926_ = v_e_4906_;
v_isShared_4927_ = v_isSharedCheck_4938_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_name_4924_);
lean_inc(v_env_4923_);
lean_dec(v_e_4906_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4938_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4928_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4929_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__8, &l_Lean_Kernel_Exception_toMessageData___closed__8_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__8);
v___x_4930_ = 1;
v___x_4931_ = l_Lean_MessageData_ofConstName(v_name_4924_, v___x_4930_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set_tag(v___x_4926_, 7);
lean_ctor_set(v___x_4926_, 1, v___x_4931_);
lean_ctor_set(v___x_4926_, 0, v___x_4929_);
v___x_4933_ = v___x_4926_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4934_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4933_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4923_, v___x_4928_, v_opts_4907_, v___x_4935_);
return v___x_4936_;
}
}
}
case 2:
{
lean_object* v_env_4939_; lean_object* v_decl_4940_; lean_object* v_givenType_4941_; lean_object* v___x_4942_; 
v_env_4939_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4939_);
v_decl_4940_ = lean_ctor_get(v_e_4906_, 1);
lean_inc(v_decl_4940_);
v_givenType_4941_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_givenType_4941_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_4942_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
switch(lean_obj_tag(v_decl_4940_))
{
case 1:
{
lean_object* v_val_4943_; lean_object* v_toConstantVal_4944_; lean_object* v_name_4945_; lean_object* v_type_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v_val_4943_ = lean_ctor_get(v_decl_4940_, 0);
lean_inc_ref(v_val_4943_);
lean_dec_ref_known(v_decl_4940_, 1);
v_toConstantVal_4944_ = lean_ctor_get(v_val_4943_, 0);
lean_inc_ref(v_toConstantVal_4944_);
lean_dec_ref(v_val_4943_);
v_name_4945_ = lean_ctor_get(v_toConstantVal_4944_, 0);
lean_inc(v_name_4945_);
v_type_4946_ = lean_ctor_get(v_toConstantVal_4944_, 2);
lean_inc_ref(v_type_4946_);
lean_dec_ref(v_toConstantVal_4944_);
v___x_4947_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4941_, v_name_4945_, v_type_4946_);
v___x_4948_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4939_, v___x_4942_, v_opts_4907_, v___x_4947_);
return v___x_4948_;
}
case 2:
{
lean_object* v_val_4949_; lean_object* v_toConstantVal_4950_; lean_object* v_name_4951_; lean_object* v_type_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v_val_4949_ = lean_ctor_get(v_decl_4940_, 0);
lean_inc_ref(v_val_4949_);
lean_dec_ref_known(v_decl_4940_, 1);
v_toConstantVal_4950_ = lean_ctor_get(v_val_4949_, 0);
lean_inc_ref(v_toConstantVal_4950_);
lean_dec_ref(v_val_4949_);
v_name_4951_ = lean_ctor_get(v_toConstantVal_4950_, 0);
lean_inc(v_name_4951_);
v_type_4952_ = lean_ctor_get(v_toConstantVal_4950_, 2);
lean_inc_ref(v_type_4952_);
lean_dec_ref(v_toConstantVal_4950_);
v___x_4953_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4941_, v_name_4951_, v_type_4952_);
v___x_4954_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4939_, v___x_4942_, v_opts_4907_, v___x_4953_);
return v___x_4954_;
}
default: 
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec_ref(v_givenType_4941_);
lean_dec(v_decl_4940_);
v___x_4955_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__11, &l_Lean_Kernel_Exception_toMessageData___closed__11_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__11);
v___x_4956_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4939_, v___x_4942_, v_opts_4907_, v___x_4955_);
return v___x_4956_;
}
}
}
case 3:
{
lean_object* v_env_4957_; lean_object* v_name_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; uint8_t v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_env_4957_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4957_);
v_name_4958_ = lean_ctor_get(v_e_4906_, 1);
lean_inc(v_name_4958_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_4959_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4960_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__13, &l_Lean_Kernel_Exception_toMessageData___closed__13_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__13);
v___x_4961_ = 1;
v___x_4962_ = l_Lean_MessageData_ofConstName(v_name_4958_, v___x_4961_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4960_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_4965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4963_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4957_, v___x_4959_, v_opts_4907_, v___x_4965_);
return v___x_4966_;
}
case 4:
{
lean_object* v_env_4967_; lean_object* v_name_4968_; lean_object* v_expr_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; uint8_t v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v_env_4967_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4967_);
v_name_4968_ = lean_ctor_get(v_e_4906_, 1);
lean_inc(v_name_4968_);
v_expr_4969_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_expr_4969_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_4970_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_4971_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__15, &l_Lean_Kernel_Exception_toMessageData___closed__15_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__15);
v___x_4972_ = 1;
v___x_4973_ = l_Lean_MessageData_ofConstName(v_name_4968_, v___x_4972_);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4971_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__17, &l_Lean_Kernel_Exception_toMessageData___closed__17_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__17);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = l_Lean_indentExpr(v_expr_4969_);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4967_, v___x_4970_, v_opts_4907_, v___x_4978_);
return v___x_4979_;
}
case 5:
{
lean_object* v_env_4980_; lean_object* v_lctx_4981_; lean_object* v_expr_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v_env_4980_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4980_);
v_lctx_4981_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_4981_);
v_expr_4982_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_expr_4982_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_4983_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__19, &l_Lean_Kernel_Exception_toMessageData___closed__19_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__19);
v___x_4984_ = l_Lean_indentExpr(v_expr_4982_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4983_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
v___x_4986_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4980_, v_lctx_4981_, v_opts_4907_, v___x_4985_);
return v___x_4986_;
}
case 6:
{
lean_object* v_env_4987_; lean_object* v_lctx_4988_; lean_object* v_expr_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v_env_4987_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4987_);
v_lctx_4988_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_4988_);
v_expr_4989_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_expr_4989_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_4990_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__21, &l_Lean_Kernel_Exception_toMessageData___closed__21_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__21);
v___x_4991_ = l_Lean_indentExpr(v_expr_4989_);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4987_, v_lctx_4988_, v_opts_4907_, v___x_4992_);
return v___x_4993_;
}
case 7:
{
lean_object* v_env_4994_; lean_object* v_lctx_4995_; lean_object* v_name_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v_env_4994_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_4994_);
v_lctx_4995_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_4995_);
v_name_4996_ = lean_ctor_get(v_e_4906_, 2);
lean_inc(v_name_4996_);
lean_dec_ref_known(v_e_4906_, 5);
v___x_4997_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__23, &l_Lean_Kernel_Exception_toMessageData___closed__23_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__23);
v___x_4998_ = l_Lean_MessageData_ofName(v_name_4996_);
v___x_4999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__6, &l_Lean_Kernel_Exception_toMessageData___closed__6_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__6);
v___x_5001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4994_, v_lctx_4995_, v_opts_4907_, v___x_5001_);
return v___x_5002_;
}
case 8:
{
lean_object* v_env_5003_; lean_object* v_lctx_5004_; lean_object* v_expr_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v_env_5003_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_5003_);
v_lctx_5004_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_5004_);
v_expr_5005_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_expr_5005_);
lean_dec_ref_known(v_e_4906_, 4);
v___x_5006_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__25, &l_Lean_Kernel_Exception_toMessageData___closed__25_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__25);
v___x_5007_ = l_Lean_indentExpr(v_expr_5005_);
v___x_5008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5006_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
v___x_5009_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5003_, v_lctx_5004_, v_opts_4907_, v___x_5008_);
return v___x_5009_;
}
case 9:
{
lean_object* v_env_5010_; lean_object* v_lctx_5011_; lean_object* v_app_5012_; lean_object* v_funType_5013_; lean_object* v_argType_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v_env_5010_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_5010_);
v_lctx_5011_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_5011_);
v_app_5012_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_app_5012_);
v_funType_5013_ = lean_ctor_get(v_e_4906_, 3);
lean_inc_ref(v_funType_5013_);
v_argType_5014_ = lean_ctor_get(v_e_4906_, 4);
lean_inc_ref(v_argType_5014_);
lean_dec_ref_known(v_e_4906_, 5);
v___x_5015_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__27, &l_Lean_Kernel_Exception_toMessageData___closed__27_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__27);
v___x_5016_ = l_Lean_indentExpr(v_app_5012_);
v___x_5017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5015_);
lean_ctor_set(v___x_5017_, 1, v___x_5016_);
v___x_5018_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__29, &l_Lean_Kernel_Exception_toMessageData___closed__29_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__29);
v___x_5019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5017_);
lean_ctor_set(v___x_5019_, 1, v___x_5018_);
v___x_5020_ = l_Lean_indentExpr(v_argType_5014_);
v___x_5021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5019_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__31, &l_Lean_Kernel_Exception_toMessageData___closed__31_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__31);
v___x_5023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5021_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
v___x_5024_ = l_Lean_indentExpr(v_funType_5013_);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5023_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5010_, v_lctx_5011_, v_opts_4907_, v___x_5025_);
return v___x_5026_;
}
case 10:
{
lean_object* v_env_5027_; lean_object* v_lctx_5028_; lean_object* v_proj_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v_env_5027_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_5027_);
v_lctx_5028_ = lean_ctor_get(v_e_4906_, 1);
lean_inc_ref(v_lctx_5028_);
v_proj_5029_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_proj_5029_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_5030_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__33, &l_Lean_Kernel_Exception_toMessageData___closed__33_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__33);
v___x_5031_ = l_Lean_indentExpr(v_proj_5029_);
v___x_5032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5030_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
v___x_5033_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5027_, v_lctx_5028_, v_opts_4907_, v___x_5032_);
return v___x_5033_;
}
case 11:
{
lean_object* v_env_5034_; lean_object* v_name_5035_; lean_object* v_type_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v_env_5034_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_env_5034_);
v_name_5035_ = lean_ctor_get(v_e_4906_, 1);
lean_inc(v_name_5035_);
v_type_5036_ = lean_ctor_get(v_e_4906_, 2);
lean_inc_ref(v_type_5036_);
lean_dec_ref_known(v_e_4906_, 3);
v___x_5037_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__2, &l_Lean_Kernel_Exception_toMessageData___closed__2_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__2);
v___x_5038_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__35, &l_Lean_Kernel_Exception_toMessageData___closed__35_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__35);
v___x_5039_ = 1;
v___x_5040_ = l_Lean_MessageData_ofConstName(v_name_5035_, v___x_5039_);
v___x_5041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5038_);
lean_ctor_set(v___x_5041_, 1, v___x_5040_);
v___x_5042_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__37, &l_Lean_Kernel_Exception_toMessageData___closed__37_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__37);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5041_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = l_Lean_indentExpr(v_type_5036_);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5034_, v___x_5037_, v_opts_4907_, v___x_5045_);
return v___x_5046_;
}
case 12:
{
lean_object* v_msg_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
lean_dec_ref(v_opts_4907_);
v_msg_5047_ = lean_ctor_get(v_e_4906_, 0);
lean_inc_ref(v_msg_5047_);
lean_dec_ref_known(v_e_4906_, 1);
v___x_5048_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__39, &l_Lean_Kernel_Exception_toMessageData___closed__39_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__39);
v___x_5049_ = l_Lean_stringToMessageData(v_msg_5047_);
v___x_5050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5048_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
return v___x_5050_;
}
case 13:
{
lean_object* v___x_5051_; 
lean_dec_ref(v_opts_4907_);
v___x_5051_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__42, &l_Lean_Kernel_Exception_toMessageData___closed__42_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__42);
return v___x_5051_;
}
case 14:
{
lean_object* v___x_5052_; 
lean_dec_ref(v_opts_4907_);
v___x_5052_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__45, &l_Lean_Kernel_Exception_toMessageData___closed__45_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__45);
return v___x_5052_;
}
case 15:
{
lean_object* v___x_5053_; 
lean_dec_ref(v_opts_4907_);
v___x_5053_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__48, &l_Lean_Kernel_Exception_toMessageData___closed__48_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__48);
return v___x_5053_;
}
default: 
{
lean_object* v___x_5054_; 
lean_dec_ref(v_opts_4907_);
v___x_5054_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__51, &l_Lean_Kernel_Exception_toMessageData___closed__51_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__51);
return v___x_5054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_5055_, lean_object* v_e_5056_, lean_object* v_cls_5057_){
_start:
{
lean_object* v___x_5058_; double v___x_5059_; uint8_t v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5058_ = lean_box(0);
v___x_5059_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_5060_ = 1;
v___x_5061_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_5062_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5062_, 0, v_cls_5057_);
lean_ctor_set(v___x_5062_, 1, v___x_5058_);
lean_ctor_set(v___x_5062_, 2, v___x_5061_);
lean_ctor_set_float(v___x_5062_, sizeof(void*)*3, v___x_5059_);
lean_ctor_set_float(v___x_5062_, sizeof(void*)*3 + 8, v___x_5059_);
lean_ctor_set_uint8(v___x_5062_, sizeof(void*)*3 + 16, v___x_5060_);
v___x_5063_ = lean_apply_1(v_inst_5055_, v_e_5056_);
v___x_5064_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_5065_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5062_);
lean_ctor_set(v___x_5065_, 1, v___x_5063_);
lean_ctor_set(v___x_5065_, 2, v___x_5064_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_5066_, lean_object* v_inst_5067_, lean_object* v_e_5068_, lean_object* v_cls_5069_){
_start:
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Lean_toTraceElem___redArg(v_inst_5067_, v_e_5068_, v_cls_5069_);
return v___x_5070_;
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
