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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
double lean_float_sub(double, double);
lean_object* lean_float_to_string(double);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_ofKernelEnv(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_formatAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_MessageData_formatAux___closed__0 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__0_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__1 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__1_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_mkErrorStringWithPos___closed__1_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__2 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__2_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = " more entries... (increase `maxTraceChildren` to see more)"};
static const lean_object* l_Lean_MessageData_formatAux___closed__3 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__3_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__3_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__4 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__4_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_MessageData_formatAux___closed__5 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__5_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__5_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__6 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__6_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_MessageData_formatAux___closed__7 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__7_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__7_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__8 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__8_value;
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_MessageData_formatAux___closed__9;
static const lean_string_object l_Lean_MessageData_formatAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_MessageData_formatAux___closed__10 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__10_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__10_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__11 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__11_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.Message"};
static const lean_object* l_Lean_MessageData_formatAux___closed__12 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__12_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.MessageData.formatAux"};
static const lean_object* l_Lean_MessageData_formatAux___closed__13 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__13_value;
static const lean_string_object l_Lean_MessageData_formatAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "MessageData.ofLazy: expected MessageData in Dynamic, got "};
static const lean_object* l_Lean_MessageData_formatAux___closed__14 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__14_value;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object*);
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
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) unknown constant '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__2 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__3;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__4 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__4_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__5;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "(kernel) constant has already been declared '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__6 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__6_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__7;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) declaration type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__8 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__8_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__8_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__9 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__9_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__10;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) declaration has metavariables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__11 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__11_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__12;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "(kernel) declaration has free variables '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__13 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__13_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__14;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', expression: "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__15 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__15_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__16;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) function expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__17 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__17_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__18;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "(kernel) type expected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__19 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__19_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__20;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(kernel) let-declaration type mismatch '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__21 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__21_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__22;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "(kernel) type mismatch at"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__23 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__23_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__24;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) application type mismatch"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__25 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__25_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__26;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nargument has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__27 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__27_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__28;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nbut function has type"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__29 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__29_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__30;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "(kernel) invalid projection"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__31 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__31_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__32;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(kernel) type of theorem '"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__33 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__33_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__34;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "' is not a proposition"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__35 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__35_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__36;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "(kernel) "};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__37 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__37_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__38;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "(kernel) deterministic timeout"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__39 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__39_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__39_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__40 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__40_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__41;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "(kernel) excessive memory consumption detected"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__42 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__42_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__42_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__43 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__43_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__44;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "(kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__45 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__45_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__45_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__46 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__46_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__47;
static const lean_string_object l_Lean_Kernel_Exception_toMessageData___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "(kernel) interrupted"};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__48 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__48_value;
static const lean_ctor_object l_Lean_Kernel_Exception_toMessageData___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__48_value)}};
static const lean_object* l_Lean_Kernel_Exception_toMessageData___closed__49 = (const lean_object*)&l_Lean_Kernel_Exception_toMessageData___closed__49_value;
static lean_once_cell_t l_Lean_Kernel_Exception_toMessageData___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Exception_toMessageData___closed__50;
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
lean_inc_ref(v___y_40_);
v___x_43_ = lean_string_append(v___y_40_, v___y_42_);
if (lean_obj_tag(v___y_41_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___y_32_ = v___y_39_;
v___y_33_ = v___x_43_;
v___y_34_ = v___x_44_;
goto v___jp_31_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___y_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_41_, 1);
v___y_32_ = v___y_39_;
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
v___y_39_ = v___y_47_;
v___y_40_ = v___x_49_;
v___y_41_ = v___y_48_;
v___y_42_ = v___x_50_;
goto v___jp_38_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v_kind_11_, 0);
v___y_39_ = v___y_47_;
v___y_40_ = v___x_49_;
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
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl(uint8_t v_x_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(v_x_92_);
v___x_94_ = lean_obj_tag_nat(v___x_93_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl___boxed(lean_object* v_x_95_){
_start:
{
uint8_t v_x_4__boxed_96_; lean_object* v_res_97_; 
v_x_4__boxed_96_ = lean_unbox(v_x_95_);
v_res_97_ = l_Lean_MessageSeverity_ctorIdx___impl(v_x_4__boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg(lean_object* v_k_98_){
_start:
{
lean_inc(v_k_98_);
return v_k_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___redArg___boxed(lean_object* v_k_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_MessageSeverity_ctorElim___redArg(v_k_99_);
lean_dec(v_k_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_101_, lean_object* v_ctorIdx_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_inc(v_k_105_);
return v_k_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_106_, lean_object* v_ctorIdx_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_k_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l_Lean_MessageSeverity_ctorElim(v_motive_106_, v_ctorIdx_107_, v_t_boxed_111_, v_h_109_, v_k_110_);
lean_dec(v_k_110_);
lean_dec(v_ctorIdx_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_113_){
_start:
{
lean_inc(v_information_113_);
return v_information_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_114_);
lean_dec(v_information_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_information_119_){
_start:
{
lean_inc(v_information_119_);
return v_information_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_information_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l_Lean_MessageSeverity_information_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_information_123_);
lean_dec(v_information_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_126_){
_start:
{
lean_inc(v_warning_126_);
return v_warning_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_127_);
lean_dec(v_warning_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_129_, uint8_t v_t_130_, lean_object* v_h_131_, lean_object* v_warning_132_){
_start:
{
lean_inc(v_warning_132_);
return v_warning_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_warning_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l_Lean_MessageSeverity_warning_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_warning_136_);
lean_dec(v_warning_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg(lean_object* v_error_139_){
_start:
{
lean_inc(v_error_139_);
return v_error_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___redArg___boxed(lean_object* v_error_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MessageSeverity_error_elim___redArg(v_error_140_);
lean_dec(v_error_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_142_, uint8_t v_t_143_, lean_object* v_h_144_, lean_object* v_error_145_){
_start:
{
lean_inc(v_error_145_);
return v_error_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_error_149_){
_start:
{
uint8_t v_t_boxed_150_; lean_object* v_res_151_; 
v_t_boxed_150_ = lean_unbox(v_t_147_);
v_res_151_ = l_Lean_MessageSeverity_error_elim(v_motive_146_, v_t_boxed_150_, v_h_148_, v_error_149_);
lean_dec(v_error_149_);
return v_res_151_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_154_, uint8_t v_y_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_156_ = lean_box(v_x_154_);
v___x_157_ = lean_obj_tag_nat(v___x_156_);
lean_dec(v___x_156_);
v___x_158_ = lean_box(v_y_155_);
v___x_159_ = lean_obj_tag_nat(v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_nat_dec_eq(v___x_157_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_161_, lean_object* v_y_162_){
_start:
{
uint8_t v_x_24__boxed_163_; uint8_t v_y_25__boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_x_24__boxed_163_ = lean_unbox(v_x_161_);
v_y_25__boxed_164_ = lean_unbox(v_y_162_);
v_res_165_ = l_Lean_instBEqMessageSeverity_beq(v_x_24__boxed_163_, v_y_25__boxed_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_178_){
_start:
{
switch(v_x_178_)
{
case 0:
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_179_;
}
case 1:
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_180_;
}
default: 
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_x_67__boxed_183_; lean_object* v_res_184_; 
v_x_67__boxed_183_ = lean_unbox(v_x_182_);
v_res_184_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Json_getTag_x3f(v_json_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
v___x_206_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_207_ = lean_string_dec_eq(v_val_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_209_ = lean_string_dec_eq(v_val_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_211_ = lean_string_dec_eq(v_val_205_, v___x_210_);
lean_dec(v_val_205_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_212_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_val_205_);
v___x_214_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v_val_205_);
v___x_215_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_218_){
_start:
{
switch(v_x_218_)
{
case 0:
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_219_;
}
case 1:
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_220_;
}
default: 
{
lean_object* v___x_221_; 
v___x_221_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_222_){
_start:
{
uint8_t v_x_28__boxed_223_; lean_object* v_res_224_; 
v_x_28__boxed_223_ = lean_unbox(v_x_222_);
v_res_224_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl(uint8_t v_x_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(v_x_227_);
v___x_229_ = lean_obj_tag_nat(v___x_228_);
lean_dec(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl___boxed(lean_object* v_x_230_){
_start:
{
uint8_t v_x_4__boxed_231_; lean_object* v_res_232_; 
v_x_4__boxed_231_ = lean_unbox(v_x_230_);
v_res_232_ = l_Lean_TraceResult_ctorIdx___impl(v_x_4__boxed_231_);
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
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_291_ = lean_box(v_x_289_);
v___x_292_ = lean_obj_tag_nat(v___x_291_);
lean_dec(v___x_291_);
v___x_293_ = lean_box(v_y_290_);
v___x_294_ = lean_obj_tag_nat(v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_nat_dec_eq(v___x_292_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_296_, lean_object* v_y_297_){
_start:
{
uint8_t v_x_24__boxed_298_; uint8_t v_y_25__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_x_24__boxed_298_ = lean_unbox(v_x_296_);
v_y_25__boxed_299_ = lean_unbox(v_y_297_);
v_res_300_ = l_Lean_instBEqTraceResult_beq(v_x_24__boxed_298_, v_y_25__boxed_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_317_, lean_object* v_prec_318_){
_start:
{
lean_object* v___y_320_; lean_object* v___y_327_; lean_object* v___y_334_; 
switch(v_x_317_)
{
case 0:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v_prec_318_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_320_ = v___x_342_;
goto v___jp_319_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_320_ = v___x_343_;
goto v___jp_319_;
}
}
case 1:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_318_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_327_ = v___x_346_;
goto v___jp_326_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_327_ = v___x_347_;
goto v___jp_326_;
}
}
default: 
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1024u);
v___x_349_ = lean_nat_dec_le(v___x_348_, v_prec_318_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_334_ = v___x_350_;
goto v___jp_333_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_334_ = v___x_351_;
goto v___jp_333_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_320_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = 0;
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_323_);
v___x_325_ = l_Repr_addAppParen(v___x_324_, v_prec_318_);
return v___x_325_;
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___y_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v_prec_318_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_318_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_352_, lean_object* v_prec_353_){
_start:
{
uint8_t v_x_171__boxed_354_; lean_object* v_res_355_; 
v_x_171__boxed_354_ = lean_unbox(v_x_352_);
v_res_355_ = l_Lean_instReprTraceResult_repr(v_x_171__boxed_354_, v_prec_353_);
lean_dec(v_prec_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_361_){
_start:
{
switch(v_x_361_)
{
case 0:
{
lean_object* v___x_362_; 
v___x_362_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_362_;
}
case 1:
{
lean_object* v___x_363_; 
v___x_363_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_363_;
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_365_){
_start:
{
uint8_t v_x_31__boxed_366_; lean_object* v_res_367_; 
v_x_31__boxed_366_ = lean_unbox(v_x_365_);
v_res_367_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl(lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_tag_nat(v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl___boxed(lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MessageData_ctorIdx___impl(v_x_370_);
lean_dec_ref(v_x_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_372_, lean_object* v_k_373_){
_start:
{
switch(lean_obj_tag(v_t_372_))
{
case 0:
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_374_);
lean_dec_ref_known(v_t_372_, 1);
v___x_375_ = lean_apply_1(v_k_373_, v_a_374_);
return v___x_375_;
}
case 1:
{
lean_object* v_a_376_; lean_object* v___x_377_; 
v_a_376_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_t_372_, 1);
v___x_377_ = lean_apply_1(v_k_373_, v_a_376_);
return v___x_377_;
}
case 5:
{
lean_object* v_a_378_; lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_378_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_378_);
v_a_379_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_379_);
lean_dec_ref_known(v_t_372_, 2);
v___x_380_ = lean_apply_2(v_k_373_, v_a_378_, v_a_379_);
return v___x_380_;
}
case 6:
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_381_);
lean_dec_ref_known(v_t_372_, 1);
v___x_382_ = lean_apply_1(v_k_373_, v_a_381_);
return v___x_382_;
}
case 8:
{
lean_object* v_a_383_; lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_383_);
v_a_384_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_t_372_, 2);
v___x_385_ = lean_apply_2(v_k_373_, v_a_383_, v_a_384_);
return v___x_385_;
}
case 9:
{
lean_object* v_data_386_; lean_object* v_msg_387_; lean_object* v_children_388_; lean_object* v___x_389_; 
v_data_386_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_data_386_);
v_msg_387_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_msg_387_);
v_children_388_ = lean_ctor_get(v_t_372_, 2);
lean_inc_ref(v_children_388_);
lean_dec_ref_known(v_t_372_, 3);
v___x_389_ = lean_apply_3(v_k_373_, v_data_386_, v_msg_387_, v_children_388_);
return v___x_389_;
}
case 11:
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_390_ = lean_ctor_get(v_t_372_, 0);
lean_inc(v_a_390_);
v_a_391_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_391_);
lean_dec_ref_known(v_t_372_, 2);
v___x_392_ = lean_apply_2(v_k_373_, v_a_390_, v_a_391_);
return v___x_392_;
}
default: 
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v_t_372_, 0);
lean_inc_ref(v_a_393_);
v_a_394_ = lean_ctor_get(v_t_372_, 1);
lean_inc_ref(v_a_394_);
lean_dec_ref(v_t_372_);
v___x_395_ = lean_apply_2(v_k_373_, v_a_393_, v_a_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_396_, lean_object* v_ctorIdx_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_MessageData_ctorElim___redArg(v_t_398_, v_k_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_MessageData_ctorElim(v_motive__1_402_, v_ctorIdx_403_, v_t_404_, v_h_405_, v_k_406_);
lean_dec(v_ctorIdx_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_408_, lean_object* v_ofFormatWithInfos_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_MessageData_ctorElim___redArg(v_t_408_, v_ofFormatWithInfos_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_ofFormatWithInfos_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_MessageData_ctorElim___redArg(v_t_412_, v_ofFormatWithInfos_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_416_, lean_object* v_ofGoal_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MessageData_ctorElim___redArg(v_t_416_, v_ofGoal_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_ofGoal_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_MessageData_ctorElim___redArg(v_t_420_, v_ofGoal_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_424_, lean_object* v_ofWidget_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_MessageData_ctorElim___redArg(v_t_424_, v_ofWidget_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_ofWidget_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MessageData_ctorElim___redArg(v_t_428_, v_ofWidget_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_432_, lean_object* v_withContext_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MessageData_ctorElim___redArg(v_t_432_, v_withContext_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_withContext_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MessageData_ctorElim___redArg(v_t_436_, v_withContext_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_440_, lean_object* v_withNamingContext_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_MessageData_ctorElim___redArg(v_t_440_, v_withNamingContext_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_withNamingContext_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_MessageData_ctorElim___redArg(v_t_444_, v_withNamingContext_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_448_, lean_object* v_nest_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_MessageData_ctorElim___redArg(v_t_448_, v_nest_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_nest_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MessageData_ctorElim___redArg(v_t_452_, v_nest_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_456_, lean_object* v_group_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MessageData_ctorElim___redArg(v_t_456_, v_group_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_group_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_MessageData_ctorElim___redArg(v_t_460_, v_group_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_464_, lean_object* v_compose_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_MessageData_ctorElim___redArg(v_t_464_, v_compose_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_compose_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MessageData_ctorElim___redArg(v_t_468_, v_compose_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_472_, lean_object* v_tagged_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_MessageData_ctorElim___redArg(v_t_472_, v_tagged_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_tagged_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MessageData_ctorElim___redArg(v_t_476_, v_tagged_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_480_, lean_object* v_trace_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MessageData_ctorElim___redArg(v_t_480_, v_trace_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_trace_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MessageData_ctorElim___redArg(v_t_484_, v_trace_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_488_, lean_object* v_ofLazy_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_MessageData_ctorElim___redArg(v_t_488_, v_ofLazy_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_ofLazy_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MessageData_ctorElim___redArg(v_t_492_, v_ofLazy_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_496_, lean_object* v_ofOriginatingSyntax_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_MessageData_ctorElim___redArg(v_t_496_, v_ofOriginatingSyntax_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_ofOriginatingSyntax_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_MessageData_ctorElim___redArg(v_t_500_, v_ofOriginatingSyntax_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormat(lean_object* v_fmt_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_box(1);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_fmt_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_519_, lean_object* v_onMissingContext_520_, lean_object* v_f_521_, lean_object* v_ctx_x3f_522_){
_start:
{
lean_object* v_msg_525_; 
if (lean_obj_tag(v_ctx_x3f_522_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_f_521_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_2(v_onMissingContext_520_, v___x_527_, lean_box(0));
v_msg_525_ = v___x_528_;
goto v___jp_524_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; 
lean_dec_ref(v_onMissingContext_520_);
v_val_529_ = lean_ctor_get(v_ctx_x3f_522_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v_ctx_x3f_522_, 1);
v___x_530_ = lean_apply_2(v_f_521_, v_val_529_, lean_box(0));
v_msg_525_ = v___x_530_;
goto v___jp_524_;
}
v___jp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_519_);
lean_ctor_set(v___x_526_, 1, v_msg_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy___lam__0___boxed(lean_object* v___x_531_, lean_object* v_onMissingContext_532_, lean_object* v_f_533_, lean_object* v_ctx_x3f_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_MessageData_lazy___lam__0(v___x_531_, v_onMissingContext_532_, v_f_533_, v_ctx_x3f_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_lazy(lean_object* v_f_537_, lean_object* v_hasSyntheticSorry_538_, lean_object* v_onMissingContext_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_541_ = lean_alloc_closure((void*)(l_Lean_MessageData_lazy___lam__0___boxed), 5, 3);
lean_closure_set(v___f_541_, 0, v___x_540_);
lean_closure_set(v___f_541_, 1, v_onMissingContext_539_);
lean_closure_set(v___f_541_, 2, v_f_537_);
v___x_542_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_542_, 0, v___f_541_);
lean_ctor_set(v___x_542_, 1, v_hasSyntheticSorry_538_);
return v___x_542_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_543_, lean_object* v_x_544_){
_start:
{
switch(lean_obj_tag(v_x_544_))
{
case 3:
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_545_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_545_;
goto _start;
}
case 4:
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_547_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_547_;
goto _start;
}
case 5:
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_549_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_549_;
goto _start;
}
case 6:
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_a_551_);
lean_dec_ref_known(v_x_544_, 1);
v_x_544_ = v_a_551_;
goto _start;
}
case 7:
{
lean_object* v_a_553_; lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_553_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_a_553_);
v_a_554_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_554_);
lean_dec_ref_known(v_x_544_, 2);
lean_inc_ref(v_p_543_);
v___x_555_ = l_Lean_MessageData_hasTag(v_p_543_, v_a_553_);
if (v___x_555_ == 0)
{
v_x_544_ = v_a_554_;
goto _start;
}
else
{
lean_dec_ref(v_a_554_);
lean_dec_ref(v_p_543_);
return v___x_555_;
}
}
case 8:
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_a_557_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_a_557_);
v_a_558_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_558_);
lean_dec_ref_known(v_x_544_, 2);
lean_inc_ref(v_p_543_);
v___x_559_ = lean_apply_1(v_p_543_, v_a_557_);
v___x_560_ = lean_unbox(v___x_559_);
if (v___x_560_ == 0)
{
v_x_544_ = v_a_558_;
goto _start;
}
else
{
uint8_t v___x_562_; 
lean_dec_ref(v_a_558_);
lean_dec_ref(v_p_543_);
v___x_562_ = lean_unbox(v___x_559_);
return v___x_562_;
}
}
case 9:
{
lean_object* v_data_563_; lean_object* v_msg_564_; lean_object* v_children_565_; lean_object* v_cls_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_data_563_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_data_563_);
v_msg_564_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_msg_564_);
v_children_565_ = lean_ctor_get(v_x_544_, 2);
lean_inc_ref(v_children_565_);
lean_dec_ref_known(v_x_544_, 3);
v_cls_566_ = lean_ctor_get(v_data_563_, 0);
lean_inc(v_cls_566_);
lean_dec_ref(v_data_563_);
lean_inc_ref(v_p_543_);
v___x_567_ = lean_apply_1(v_p_543_, v_cls_566_);
v___x_568_ = lean_unbox(v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; 
lean_inc_ref(v_p_543_);
v___x_569_ = l_Lean_MessageData_hasTag(v_p_543_, v_msg_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_size(v_children_565_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_572_;
}
else
{
if (v___x_572_ == 0)
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_572_;
}
else
{
size_t v___x_573_; size_t v___x_574_; uint8_t v___x_575_; 
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_571_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_543_, v_children_565_, v___x_573_, v___x_574_);
lean_dec_ref(v_children_565_);
return v___x_575_;
}
}
}
else
{
lean_dec_ref(v_children_565_);
lean_dec_ref(v_p_543_);
return v___x_569_;
}
}
else
{
uint8_t v___x_576_; 
lean_dec_ref(v_children_565_);
lean_dec_ref(v_msg_564_);
lean_dec_ref(v_p_543_);
v___x_576_ = lean_unbox(v___x_567_);
return v___x_576_;
}
}
case 11:
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_a_577_);
lean_dec_ref_known(v_x_544_, 2);
v_x_544_ = v_a_577_;
goto _start;
}
default: 
{
uint8_t v___x_579_; 
lean_dec_ref(v_x_544_);
lean_dec_ref(v_p_543_);
v___x_579_ = 0;
return v___x_579_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_580_, lean_object* v_as_581_, size_t v_i_582_, size_t v_stop_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_usize_dec_eq(v_i_582_, v_stop_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_array_uget_borrowed(v_as_581_, v_i_582_);
lean_inc(v___x_585_);
lean_inc_ref(v_p_580_);
v___x_586_ = l_Lean_MessageData_hasTag(v_p_580_, v___x_585_);
if (v___x_586_ == 0)
{
size_t v___x_587_; size_t v___x_588_; 
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_582_, v___x_587_);
v_i_582_ = v___x_588_;
goto _start;
}
else
{
lean_dec_ref(v_p_580_);
return v___x_586_;
}
}
else
{
uint8_t v___x_590_; 
lean_dec_ref(v_p_580_);
v___x_590_ = 0;
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_stop_594_){
_start:
{
size_t v_i_boxed_595_; size_t v_stop_boxed_596_; uint8_t v_res_597_; lean_object* v_r_598_; 
v_i_boxed_595_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_stop_boxed_596_ = lean_unbox_usize(v_stop_594_);
lean_dec(v_stop_594_);
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_591_, v_as_592_, v_i_boxed_595_, v_stop_boxed_596_);
lean_dec_ref(v_as_592_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_MessageData_hasTag(v_p_599_, v_x_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 3:
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_604_;
goto _start;
}
case 4:
{
lean_object* v_a_606_; 
v_a_606_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_606_;
goto _start;
}
case 8:
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_608_);
return v_a_608_;
}
case 9:
{
lean_object* v_data_609_; lean_object* v_cls_610_; 
v_data_609_ = lean_ctor_get(v_x_603_, 0);
v_cls_610_ = lean_ctor_get(v_data_609_, 0);
lean_inc(v_cls_610_);
return v_cls_610_;
}
case 11:
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v_x_603_, 1);
v_x_603_ = v_a_611_;
goto _start;
}
default: 
{
lean_object* v___x_613_; 
v___x_613_ = lean_box(0);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_MessageData_kind(v_x_614_);
lean_dec_ref(v_x_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 11)
{
lean_object* v_a_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_a_617_ = lean_ctor_get(v_x_616_, 0);
v_a_618_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_inc(v_a_617_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_a_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 0);
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_a_618_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_x_616_);
return v___x_628_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_629_){
_start:
{
switch(lean_obj_tag(v_x_629_))
{
case 3:
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_630_;
goto _start;
}
case 4:
{
lean_object* v_a_632_; 
v_a_632_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_632_;
goto _start;
}
case 8:
{
lean_object* v_a_634_; 
v_a_634_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_634_;
goto _start;
}
case 9:
{
uint8_t v___x_636_; 
v___x_636_ = 1;
return v___x_636_;
}
case 11:
{
lean_object* v_a_637_; 
v_a_637_ = lean_ctor_get(v_x_629_, 1);
v_x_629_ = v_a_637_;
goto _start;
}
default: 
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_MessageData_isTrace(v_x_640_);
lean_dec_ref(v_x_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
switch(lean_obj_tag(v_x_643_))
{
case 3:
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_a_645_ = lean_ctor_get(v_x_643_, 0);
v_a_646_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_x_643_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_inc(v_a_645_);
lean_dec(v_x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_MessageData_composePreservingKind(v_a_646_, v_x_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
case 4:
{
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_655_ = lean_ctor_get(v_x_643_, 0);
v_a_656_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_x_643_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v_x_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_MessageData_composePreservingKind(v_a_656_, v_x_644_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
case 8:
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v_x_643_, 0);
v_a_666_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_x_643_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v_x_643_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 7);
lean_ctor_set(v___x_668_, 1, v_x_644_);
lean_ctor_set(v___x_668_, 0, v_a_666_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_x_644_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_672_, 0, v_a_665_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
return v___x_672_;
}
}
}
case 11:
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_a_675_ = lean_ctor_get(v_x_643_, 0);
v_a_676_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_643_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v_x_643_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_MessageData_composePreservingKind(v_a_676_, v_x_644_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
default: 
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v_x_643_);
lean_ctor_set(v___x_685_, 1, v_x_644_);
return v___x_685_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(0);
v___x_687_ = l_Lean_MessageData_ofFormat(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_689_, lean_object* v_ctx_690_){
_start:
{
lean_object* v_env_691_; lean_object* v_mctx_692_; lean_object* v_lctx_693_; lean_object* v_opts_694_; lean_object* v_currNamespace_695_; lean_object* v_openDecls_696_; lean_object* v___x_697_; 
v_env_691_ = lean_ctor_get(v_ctx_690_, 0);
v_mctx_692_ = lean_ctor_get(v_ctx_690_, 1);
v_lctx_693_ = lean_ctor_get(v_ctx_690_, 2);
v_opts_694_ = lean_ctor_get(v_ctx_690_, 3);
v_currNamespace_695_ = lean_ctor_get(v_nCtx_689_, 0);
v_openDecls_696_ = lean_ctor_get(v_nCtx_689_, 1);
lean_inc(v_openDecls_696_);
lean_inc(v_currNamespace_695_);
lean_inc_ref(v_opts_694_);
lean_inc_ref(v_lctx_693_);
lean_inc_ref(v_mctx_692_);
lean_inc_ref(v_env_691_);
v___x_697_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_697_, 0, v_env_691_);
lean_ctor_set(v___x_697_, 1, v_mctx_692_);
lean_ctor_set(v___x_697_, 2, v_lctx_693_);
lean_ctor_set(v___x_697_, 3, v_opts_694_);
lean_ctor_set(v___x_697_, 4, v_currNamespace_695_);
lean_ctor_set(v___x_697_, 5, v_openDecls_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_698_, lean_object* v_ctx_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_MessageData_mkPPContext(v_nCtx_698_, v_ctx_699_);
lean_dec_ref(v_ctx_699_);
lean_dec_ref(v_nCtx_698_);
return v_res_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_703_);
lean_dec_ref(v_x_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_706_, lean_object* v_stx_707_, lean_object* v_ctx_x3f_708_){
_start:
{
lean_object* v_val_711_; 
if (lean_obj_tag(v_ctx_x3f_708_) == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
v___x_715_ = 0;
v___x_716_ = l_Lean_Syntax_formatStx(v_stx_707_, v___x_714_, v___x_715_);
v_val_711_ = v___x_716_;
goto v___jp_710_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_718_; 
v_val_717_ = lean_ctor_get(v_ctx_x3f_708_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_ctx_x3f_708_, 1);
v___x_718_ = l_Lean_ppTerm(v_val_717_, v_stx_707_);
v_val_711_ = v___x_718_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Lean_MessageData_ofFormat(v_val_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_706_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_719_, lean_object* v_stx_720_, lean_object* v_ctx_x3f_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_719_, v_stx_720_, v_ctx_x3f_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_725_){
_start:
{
lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_stx_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v___f_726_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_727_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_728_ = lean_box(0);
v_stx_729_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_725_, v___x_728_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_730_, 0, v___x_727_);
lean_closure_set(v___f_730_, 1, v_stx_729_);
v___x_731_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_731_, 0, v___f_730_);
lean_ctor_set(v___x_731_, 1, v___f_726_);
return v___x_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_732_, lean_object* v_mctx_733_){
_start:
{
lean_object* v___x_734_; lean_object* v_fst_735_; uint8_t v___x_736_; 
v___x_734_ = l_Lean_instantiateMVarsCore(v_mctx_733_, v_e_732_);
v_fst_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_fst_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_Lean_Expr_hasSyntheticSorry(v_fst_735_);
lean_dec(v_fst_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_737_, lean_object* v_mctx_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_MessageData_ofExpr___lam__0(v_e_737_, v_mctx_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_741_, lean_object* v_e_742_, lean_object* v_ctx_x3f_743_){
_start:
{
lean_object* v_val_746_; 
if (lean_obj_tag(v_ctx_x3f_743_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_expr_dbg_to_string(v_e_742_);
lean_dec_ref(v_e_742_);
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = lean_box(1);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v_val_746_ = v___x_752_;
goto v___jp_745_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
v_val_753_ = lean_ctor_get(v_ctx_x3f_743_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_ctx_x3f_743_, 1);
v___x_754_ = l_Lean_ppExprWithInfos(v_val_753_, v_e_742_);
v_val_746_ = v___x_754_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_val_746_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_741_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_755_, lean_object* v_e_756_, lean_object* v_ctx_x3f_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_MessageData_ofExpr___lam__1(v___x_755_, v_e_756_, v_ctx_x3f_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_760_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
lean_inc_ref(v_e_760_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_761_, 0, v_e_760_);
v___x_762_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_763_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_763_, 0, v___x_762_);
lean_closure_set(v___f_763_, 1, v_e_760_);
v___x_764_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_764_, 0, v___f_763_);
lean_ctor_set(v___x_764_, 1, v___f_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_box(0);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_MessageData_ofLevel___lam__0(v_x_767_);
lean_dec(v_x_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_769_, lean_object* v_l_770_, lean_object* v___f_771_, lean_object* v_ctx_x3f_772_){
_start:
{
lean_object* v_val_775_; 
if (lean_obj_tag(v_ctx_x3f_772_) == 0)
{
uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = 1;
v___x_779_ = l_Lean_Level_format(v_l_770_, v___x_778_, v___f_771_);
v_val_775_ = v___x_779_;
goto v___jp_774_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_781_; 
lean_dec_ref(v___f_771_);
v_val_780_ = lean_ctor_get(v_ctx_x3f_772_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_ctx_x3f_772_, 1);
v___x_781_ = l_Lean_ppLevel(v_val_780_, v_l_770_);
v_val_775_ = v___x_781_;
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Lean_MessageData_ofFormat(v_val_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_769_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_782_, lean_object* v_l_783_, lean_object* v___f_784_, lean_object* v_ctx_x3f_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_MessageData_ofLevel___lam__2(v___x_782_, v_l_783_, v___f_784_, v_ctx_x3f_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_789_){
_start:
{
lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_790_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_791_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_792_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_793_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_793_, 0, v___x_792_);
lean_closure_set(v___f_793_, 1, v_l_789_);
lean_closure_set(v___f_793_, 2, v___f_790_);
v___x_794_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_794_, 0, v___f_793_);
lean_ctor_set(v___x_794_, 1, v___f_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_795_){
_start:
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = 1;
v___x_797_ = l_Lean_Name_toString(v_n_795_, v___x_796_);
v___x_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = l_Lean_MessageData_ofFormat(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_803_, lean_object* v_k_804_, uint8_t v_v_805_){
_start:
{
lean_object* v_map_806_; uint8_t v_hasTrace_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_821_; 
v_map_806_ = lean_ctor_get(v_o_803_, 0);
v_hasTrace_807_ = lean_ctor_get_uint8(v_o_803_, sizeof(void*)*1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_o_803_);
if (v_isSharedCheck_821_ == 0)
{
v___x_809_ = v_o_803_;
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_map_806_);
lean_dec(v_o_803_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_811_, 0, v_v_805_);
lean_inc(v_k_804_);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_804_, v___x_811_, v_map_806_);
if (v_hasTrace_807_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_816_; 
v___x_813_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_814_ = l_Lean_Name_isPrefixOf(v___x_813_, v_k_804_);
lean_dec(v_k_804_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_812_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_814_);
return v___x_816_;
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v_k_804_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_819_ = v___x_809_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_812_);
lean_ctor_set_uint8(v_reuseFailAlloc_820_, sizeof(void*)*1, v_hasTrace_807_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_822_, lean_object* v_k_823_, lean_object* v_v_824_){
_start:
{
uint8_t v_v_boxed_825_; lean_object* v_res_826_; 
v_v_boxed_825_ = lean_unbox(v_v_824_);
v_res_826_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_822_, v_k_823_, v_v_boxed_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_832_, lean_object* v_constName_833_, uint8_t v_fullNames_834_, lean_object* v_ctx_x3f_835_){
_start:
{
lean_object* v_val_838_; lean_object* v___y_842_; 
if (lean_obj_tag(v_ctx_x3f_835_) == 0)
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = 1;
v___x_844_ = l_Lean_Name_toString(v_constName_833_, v___x_843_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_box(1);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v_val_838_ = v___x_847_;
goto v___jp_837_;
}
else
{
if (v_fullNames_834_ == 0)
{
lean_object* v_val_848_; lean_object* v___x_849_; 
v_val_848_ = lean_ctor_get(v_ctx_x3f_835_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_ctx_x3f_835_, 1);
v___x_849_ = l_Lean_ppConstNameWithInfos(v_val_848_, v_constName_833_);
v___y_842_ = v___x_849_;
goto v___jp_841_;
}
else
{
lean_object* v_val_850_; lean_object* v_env_851_; lean_object* v_mctx_852_; lean_object* v_lctx_853_; lean_object* v_opts_854_; lean_object* v_currNamespace_855_; lean_object* v_openDecls_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_val_850_ = lean_ctor_get(v_ctx_x3f_835_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_ctx_x3f_835_, 1);
v_env_851_ = lean_ctor_get(v_val_850_, 0);
v_mctx_852_ = lean_ctor_get(v_val_850_, 1);
v_lctx_853_ = lean_ctor_get(v_val_850_, 2);
v_opts_854_ = lean_ctor_get(v_val_850_, 3);
v_currNamespace_855_ = lean_ctor_get(v_val_850_, 4);
v_openDecls_856_ = lean_ctor_get(v_val_850_, 5);
v_isSharedCheck_866_ = !lean_is_exclusive(v_val_850_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v_val_850_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_openDecls_856_);
lean_inc(v_currNamespace_855_);
lean_inc(v_opts_854_);
lean_inc(v_lctx_853_);
lean_inc(v_mctx_852_);
lean_inc(v_env_851_);
lean_dec(v_val_850_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_861_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_854_, v___x_860_, v_fullNames_834_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 3, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_env_851_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_mctx_852_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_lctx_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_currNamespace_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v_openDecls_856_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_ppConstNameWithInfos(v___x_863_, v_constName_833_);
v___y_842_ = v___x_864_;
goto v___jp_841_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_val_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_832_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
v___jp_841_:
{
v_val_838_ = v___y_842_;
goto v___jp_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_867_, lean_object* v_constName_868_, lean_object* v_fullNames_869_, lean_object* v_ctx_x3f_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_fullNames_boxed_872_; lean_object* v_res_873_; 
v_fullNames_boxed_872_ = lean_unbox(v_fullNames_869_);
v_res_873_ = l_Lean_MessageData_ofConstName___lam__1(v___x_867_, v_constName_868_, v_fullNames_boxed_872_, v_ctx_x3f_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_874_, uint8_t v_fullNames_875_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; 
v___f_876_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_877_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_878_ = lean_box(v_fullNames_875_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_879_, 0, v___x_877_);
lean_closure_set(v___f_879_, 1, v_constName_874_);
lean_closure_set(v___f_879_, 2, v___x_878_);
v___x_880_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_880_, 0, v___f_879_);
lean_ctor_set(v___x_880_, 1, v___f_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_881_, lean_object* v_fullNames_882_){
_start:
{
uint8_t v_fullNames_boxed_883_; lean_object* v_res_884_; 
v_fullNames_boxed_883_ = lean_unbox(v_fullNames_882_);
v_res_884_ = l_Lean_MessageData_ofConstName(v_constName_881_, v_fullNames_boxed_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_val_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_MessageData_withExprHover___lam__0(v_val_889_, v___y_890_);
lean_dec_ref(v___y_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_893_, lean_object* v_v_894_, lean_object* v_t_895_){
_start:
{
if (lean_obj_tag(v_t_895_) == 0)
{
lean_object* v_size_896_; lean_object* v_k_897_; lean_object* v_v_898_; lean_object* v_l_899_; lean_object* v_r_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_1181_; 
v_size_896_ = lean_ctor_get(v_t_895_, 0);
v_k_897_ = lean_ctor_get(v_t_895_, 1);
v_v_898_ = lean_ctor_get(v_t_895_, 2);
v_l_899_ = lean_ctor_get(v_t_895_, 3);
v_r_900_ = lean_ctor_get(v_t_895_, 4);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_t_895_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_902_ = v_t_895_;
v_isShared_903_ = v_isSharedCheck_1181_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_r_900_);
lean_inc(v_l_899_);
lean_inc(v_v_898_);
lean_inc(v_k_897_);
lean_inc(v_size_896_);
lean_dec(v_t_895_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_1181_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_lt(v_k_893_, v_k_897_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_eq(v_k_893_, v_k_897_);
if (v___x_905_ == 0)
{
lean_object* v_impl_906_; lean_object* v___x_907_; 
lean_dec(v_size_896_);
v_impl_906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_893_, v_v_894_, v_r_900_);
v___x_907_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_899_) == 0)
{
lean_object* v_size_908_; lean_object* v_size_909_; lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_l_912_; lean_object* v_r_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_size_908_ = lean_ctor_get(v_l_899_, 0);
v_size_909_ = lean_ctor_get(v_impl_906_, 0);
v_k_910_ = lean_ctor_get(v_impl_906_, 1);
v_v_911_ = lean_ctor_get(v_impl_906_, 2);
v_l_912_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_912_);
v_r_913_ = lean_ctor_get(v_impl_906_, 4);
v___x_914_ = lean_unsigned_to_nat(3u);
v___x_915_ = lean_nat_mul(v___x_914_, v_size_908_);
v___x_916_ = lean_nat_dec_lt(v___x_915_, v_size_909_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec(v_l_912_);
v___x_917_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_918_ = lean_nat_add(v___x_917_, v_size_909_);
lean_dec(v___x_917_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_impl_906_);
lean_ctor_set(v___x_902_, 0, v___x_918_);
v___x_920_ = v___x_902_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_impl_906_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_985_; 
lean_inc(v_r_913_);
lean_inc(v_v_911_);
lean_inc(v_k_910_);
lean_inc(v_size_909_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_impl_906_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_impl_906_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_990_);
v___x_923_ = v_impl_906_;
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_impl_906_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_size_925_; lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_l_928_; lean_object* v_r_929_; lean_object* v_size_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_size_925_ = lean_ctor_get(v_l_912_, 0);
v_k_926_ = lean_ctor_get(v_l_912_, 1);
v_v_927_ = lean_ctor_get(v_l_912_, 2);
v_l_928_ = lean_ctor_get(v_l_912_, 3);
v_r_929_ = lean_ctor_get(v_l_912_, 4);
v_size_930_ = lean_ctor_get(v_r_913_, 0);
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = lean_nat_mul(v___x_931_, v_size_930_);
v___x_933_ = lean_nat_dec_lt(v_size_925_, v___x_932_);
lean_dec(v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_r_929_);
lean_inc(v_l_928_);
lean_inc(v_v_927_);
lean_inc(v_k_926_);
v_isSharedCheck_961_ = !lean_is_exclusive(v_l_912_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_962_ = lean_ctor_get(v_l_912_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_912_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_912_, 2);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_912_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_l_912_, 0);
lean_dec(v_unused_966_);
v___x_935_ = v_l_912_;
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_l_912_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_951_; 
v___x_937_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_938_ = lean_nat_add(v___x_937_, v_size_909_);
lean_dec(v_size_909_);
if (lean_obj_tag(v_l_928_) == 0)
{
lean_object* v_size_959_; 
v_size_959_ = lean_ctor_get(v_l_928_, 0);
lean_inc(v_size_959_);
v___y_951_ = v_size_959_;
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___y_951_ = v___x_960_;
goto v___jp_950_;
}
v___jp_939_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_nat_add(v___y_940_, v___y_942_);
lean_dec(v___y_942_);
lean_dec(v___y_940_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_r_913_);
lean_ctor_set(v___x_935_, 3, v_r_929_);
lean_ctor_set(v___x_935_, 2, v_v_911_);
lean_ctor_set(v___x_935_, 1, v_k_910_);
lean_ctor_set(v___x_935_, 0, v___x_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_r_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_r_913_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v___x_945_);
lean_ctor_set(v___x_923_, 3, v___y_941_);
lean_ctor_set(v___x_923_, 2, v_v_927_);
lean_ctor_set(v___x_923_, 1, v_k_926_);
lean_ctor_set(v___x_923_, 0, v___x_938_);
v___x_947_ = v___x_923_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v___y_941_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_950_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v___x_937_, v___y_951_);
lean_dec(v___y_951_);
lean_dec(v___x_937_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_l_928_);
lean_ctor_set(v___x_902_, 0, v___x_952_);
v___x_954_ = v___x_902_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_l_928_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = lean_nat_add(v___x_907_, v_size_930_);
if (lean_obj_tag(v_r_929_) == 0)
{
lean_object* v_size_956_; 
v_size_956_ = lean_ctor_get(v_r_929_, 0);
lean_inc(v_size_956_);
v___y_940_ = v___x_955_;
v___y_941_ = v___x_954_;
v___y_942_ = v_size_956_;
goto v___jp_939_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___y_940_ = v___x_955_;
v___y_941_ = v___x_954_;
v___y_942_ = v___x_957_;
goto v___jp_939_;
}
}
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_del_object(v___x_902_);
v___x_967_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_968_ = lean_nat_add(v___x_967_, v_size_909_);
lean_dec(v_size_909_);
v___x_969_ = lean_nat_add(v___x_967_, v_size_925_);
lean_dec(v___x_967_);
lean_inc_ref(v_l_899_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v_l_912_);
lean_ctor_set(v___x_923_, 3, v_l_899_);
lean_ctor_set(v___x_923_, 2, v_v_898_);
lean_ctor_set(v___x_923_, 1, v_k_897_);
lean_ctor_set(v___x_923_, 0, v___x_969_);
v___x_971_ = v___x_923_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_l_912_);
v___x_971_ = v_reuseFailAlloc_984_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_isSharedCheck_978_ = !lean_is_exclusive(v_l_899_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_979_ = lean_ctor_get(v_l_899_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_899_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_899_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_899_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_899_, 0);
lean_dec(v_unused_983_);
v___x_973_ = v_l_899_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_dec(v_l_899_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 4, v_r_913_);
lean_ctor_set(v___x_973_, 3, v___x_971_);
lean_ctor_set(v___x_973_, 2, v_v_911_);
lean_ctor_set(v___x_973_, 1, v_k_910_);
lean_ctor_set(v___x_973_, 0, v___x_968_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_r_913_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_991_; 
v_l_991_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_991_);
if (lean_obj_tag(v_l_991_) == 0)
{
lean_object* v_r_992_; lean_object* v_k_993_; lean_object* v_v_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1017_; 
v_r_992_ = lean_ctor_get(v_impl_906_, 4);
v_k_993_ = lean_ctor_get(v_impl_906_, 1);
v_v_994_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1019_);
v___x_996_ = v_impl_906_;
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_r_992_);
lean_inc(v_v_994_);
lean_inc(v_k_993_);
lean_dec(v_impl_906_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
v_k_998_ = lean_ctor_get(v_l_991_, 1);
v_v_999_ = lean_ctor_get(v_l_991_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_l_991_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1014_ = lean_ctor_get(v_l_991_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_l_991_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_l_991_, 0);
lean_dec(v_unused_1016_);
v___x_1001_ = v_l_991_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_v_999_);
lean_inc(v_k_998_);
lean_dec(v_l_991_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_992_, 2);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v_r_992_);
lean_ctor_set(v___x_1001_, 3, v_r_992_);
lean_ctor_set(v___x_1001_, 2, v_v_898_);
lean_ctor_set(v___x_1001_, 1, v_k_897_);
lean_ctor_set(v___x_1001_, 0, v___x_907_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_r_992_);
v___x_1005_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
lean_inc(v_r_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 3, v_r_992_);
lean_ctor_set(v___x_996_, 0, v___x_907_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_993_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_994_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_992_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1007_);
lean_ctor_set(v___x_902_, 3, v___x_1005_);
lean_ctor_set(v___x_902_, 2, v_v_999_);
lean_ctor_set(v___x_902_, 1, v_k_998_);
lean_ctor_set(v___x_902_, 0, v___x_1003_);
v___x_1009_ = v___x_902_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
else
{
lean_object* v_r_1020_; 
v_r_1020_ = lean_ctor_get(v_impl_906_, 4);
lean_inc(v_r_1020_);
if (lean_obj_tag(v_r_1020_) == 0)
{
lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1033_; 
v_k_1021_ = lean_ctor_get(v_impl_906_, 1);
v_v_1022_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1034_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1036_);
v___x_1024_ = v_impl_906_;
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
lean_dec(v_impl_906_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(3u);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_l_991_);
lean_ctor_set(v___x_1024_, 2, v_v_898_);
lean_ctor_set(v___x_1024_, 1, v_k_897_);
lean_ctor_set(v___x_1024_, 0, v___x_907_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_l_991_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_l_991_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_1020_);
lean_ctor_set(v___x_902_, 3, v___x_1028_);
lean_ctor_set(v___x_902_, 2, v_v_1022_);
lean_ctor_set(v___x_902_, 1, v_k_1021_);
lean_ctor_set(v___x_902_, 0, v___x_1026_);
v___x_1030_ = v___x_902_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_r_1020_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_unsigned_to_nat(2u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_impl_906_);
lean_ctor_set(v___x_902_, 3, v_r_1020_);
lean_ctor_set(v___x_902_, 0, v___x_1037_);
v___x_1039_ = v___x_902_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_1020_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_impl_906_);
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
}
else
{
lean_object* v___x_1042_; 
lean_dec(v_v_898_);
lean_dec(v_k_897_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v_v_894_);
lean_ctor_set(v___x_902_, 1, v_k_893_);
v___x_1042_ = v___x_902_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_896_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_893_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_894_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_l_899_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_r_900_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_impl_1044_; lean_object* v___x_1045_; 
lean_dec(v_size_896_);
v_impl_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_893_, v_v_894_, v_l_899_);
v___x_1045_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_900_) == 0)
{
lean_object* v_size_1046_; lean_object* v_size_1047_; lean_object* v_k_1048_; lean_object* v_v_1049_; lean_object* v_l_1050_; lean_object* v_r_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_size_1046_ = lean_ctor_get(v_r_900_, 0);
v_size_1047_ = lean_ctor_get(v_impl_1044_, 0);
v_k_1048_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1049_ = lean_ctor_get(v_impl_1044_, 2);
v_l_1050_ = lean_ctor_get(v_impl_1044_, 3);
v_r_1051_ = lean_ctor_get(v_impl_1044_, 4);
lean_inc(v_r_1051_);
v___x_1052_ = lean_unsigned_to_nat(3u);
v___x_1053_ = lean_nat_mul(v___x_1052_, v_size_1046_);
v___x_1054_ = lean_nat_dec_lt(v___x_1053_, v_size_1047_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec(v_r_1051_);
v___x_1055_ = lean_nat_add(v___x_1045_, v_size_1047_);
v___x_1056_ = lean_nat_add(v___x_1055_, v_size_1046_);
lean_dec(v___x_1055_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 3, v_impl_1044_);
lean_ctor_set(v___x_902_, 0, v___x_1056_);
v___x_1058_ = v___x_902_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_impl_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v_r_900_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1125_; 
lean_inc(v_l_1050_);
lean_inc(v_v_1049_);
lean_inc(v_k_1048_);
lean_inc(v_size_1047_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; 
v_unused_1126_ = lean_ctor_get(v_impl_1044_, 4);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_impl_1044_, 2);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_impl_1044_, 1);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1130_);
v___x_1061_ = v_impl_1044_;
v_isShared_1062_ = v_isSharedCheck_1125_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_impl_1044_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1125_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_size_1063_; lean_object* v_size_1064_; lean_object* v_k_1065_; lean_object* v_v_1066_; lean_object* v_l_1067_; lean_object* v_r_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_size_1063_ = lean_ctor_get(v_l_1050_, 0);
v_size_1064_ = lean_ctor_get(v_r_1051_, 0);
v_k_1065_ = lean_ctor_get(v_r_1051_, 1);
v_v_1066_ = lean_ctor_get(v_r_1051_, 2);
v_l_1067_ = lean_ctor_get(v_r_1051_, 3);
v_r_1068_ = lean_ctor_get(v_r_1051_, 4);
v___x_1069_ = lean_unsigned_to_nat(2u);
v___x_1070_ = lean_nat_mul(v___x_1069_, v_size_1063_);
v___x_1071_ = lean_nat_dec_lt(v_size_1064_, v___x_1070_);
lean_dec(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1100_; 
lean_inc(v_r_1068_);
lean_inc(v_l_1067_);
lean_inc(v_v_1066_);
lean_inc(v_k_1065_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_r_1051_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1101_ = lean_ctor_get(v_r_1051_, 4);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_r_1051_, 3);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_r_1051_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_1051_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_r_1051_, 0);
lean_dec(v_unused_1105_);
v___x_1073_ = v_r_1051_;
v_isShared_1074_ = v_isSharedCheck_1100_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_r_1051_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1100_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___x_1088_; lean_object* v___y_1090_; 
v___x_1075_ = lean_nat_add(v___x_1045_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1076_ = lean_nat_add(v___x_1075_, v_size_1046_);
lean_dec(v___x_1075_);
v___x_1088_ = lean_nat_add(v___x_1045_, v_size_1063_);
if (lean_obj_tag(v_l_1067_) == 0)
{
lean_object* v_size_1098_; 
v_size_1098_ = lean_ctor_get(v_l_1067_, 0);
lean_inc(v_size_1098_);
v___y_1090_ = v_size_1098_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___y_1090_ = v___x_1099_;
goto v___jp_1089_;
}
v___jp_1077_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_nat_add(v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v_r_900_);
lean_ctor_set(v___x_1073_, 3, v_r_1068_);
lean_ctor_set(v___x_1073_, 2, v_v_898_);
lean_ctor_set(v___x_1073_, 1, v_k_897_);
lean_ctor_set(v___x_1073_, 0, v___x_1081_);
v___x_1083_ = v___x_1073_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_r_1068_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_r_900_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v___x_1083_);
lean_ctor_set(v___x_1061_, 3, v___y_1078_);
lean_ctor_set(v___x_1061_, 2, v_v_1066_);
lean_ctor_set(v___x_1061_, 1, v_k_1065_);
lean_ctor_set(v___x_1061_, 0, v___x_1076_);
v___x_1085_ = v___x_1061_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_1065_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_1066_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___y_1078_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_nat_add(v___x_1088_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec(v___x_1088_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_l_1067_);
lean_ctor_set(v___x_902_, 3, v_l_1050_);
lean_ctor_set(v___x_902_, 2, v_v_1049_);
lean_ctor_set(v___x_902_, 1, v_k_1048_);
lean_ctor_set(v___x_902_, 0, v___x_1091_);
v___x_1093_ = v___x_902_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_l_1067_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_nat_add(v___x_1045_, v_size_1046_);
if (lean_obj_tag(v_r_1068_) == 0)
{
lean_object* v_size_1095_; 
v_size_1095_ = lean_ctor_get(v_r_1068_, 0);
lean_inc(v_size_1095_);
v___y_1078_ = v___x_1093_;
v___y_1079_ = v___x_1094_;
v___y_1080_ = v_size_1095_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___y_1078_ = v___x_1093_;
v___y_1079_ = v___x_1094_;
v___y_1080_ = v___x_1096_;
goto v___jp_1077_;
}
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_del_object(v___x_902_);
v___x_1106_ = lean_nat_add(v___x_1045_, v_size_1047_);
lean_dec(v_size_1047_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_size_1046_);
lean_dec(v___x_1106_);
v___x_1108_ = lean_nat_add(v___x_1045_, v_size_1046_);
v___x_1109_ = lean_nat_add(v___x_1108_, v_size_1064_);
lean_dec(v___x_1108_);
lean_inc_ref(v_r_900_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v_r_900_);
lean_ctor_set(v___x_1061_, 3, v_r_1051_);
lean_ctor_set(v___x_1061_, 2, v_v_898_);
lean_ctor_set(v___x_1061_, 1, v_k_897_);
lean_ctor_set(v___x_1061_, 0, v___x_1109_);
v___x_1111_ = v___x_1061_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_r_1051_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_r_900_);
v___x_1111_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_isSharedCheck_1118_ = !lean_is_exclusive(v_r_900_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1119_ = lean_ctor_get(v_r_900_, 4);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_900_, 3);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_r_900_, 2);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_r_900_, 1);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_r_900_, 0);
lean_dec(v_unused_1123_);
v___x_1113_ = v_r_900_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v_r_900_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 4, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v_l_1050_);
lean_ctor_set(v___x_1113_, 2, v_v_1049_);
lean_ctor_set(v___x_1113_, 1, v_k_1048_);
lean_ctor_set(v___x_1113_, 0, v___x_1107_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1048_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1049_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_l_1050_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___x_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1131_; 
v_l_1131_ = lean_ctor_get(v_impl_1044_, 3);
if (lean_obj_tag(v_l_1131_) == 0)
{
lean_object* v_r_1132_; lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1145_; 
lean_inc_ref(v_l_1131_);
v_r_1132_ = lean_ctor_get(v_impl_1044_, 4);
v_k_1133_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1134_ = lean_ctor_get(v_impl_1044_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1146_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1147_);
v___x_1136_ = v_impl_1044_;
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_r_1132_);
lean_inc(v_v_1134_);
lean_inc(v_k_1133_);
lean_dec(v_impl_1044_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1132_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 3, v_r_1132_);
lean_ctor_set(v___x_1136_, 2, v_v_898_);
lean_ctor_set(v___x_1136_, 1, v_k_897_);
lean_ctor_set(v___x_1136_, 0, v___x_1045_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_r_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1132_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1140_);
lean_ctor_set(v___x_902_, 3, v_l_1131_);
lean_ctor_set(v___x_902_, 2, v_v_1134_);
lean_ctor_set(v___x_902_, 1, v_k_1133_);
lean_ctor_set(v___x_902_, 0, v___x_1138_);
v___x_1142_ = v___x_902_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_r_1148_; 
v_r_1148_ = lean_ctor_get(v_impl_1044_, 4);
lean_inc(v_r_1148_);
if (lean_obj_tag(v_r_1148_) == 0)
{
lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1173_; 
lean_inc(v_l_1131_);
v_k_1149_ = lean_ctor_get(v_impl_1044_, 1);
v_v_1150_ = lean_ctor_get(v_impl_1044_, 2);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_impl_1044_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1174_ = lean_ctor_get(v_impl_1044_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1044_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1044_, 0);
lean_dec(v_unused_1176_);
v___x_1152_ = v_impl_1044_;
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
lean_dec(v_impl_1044_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_k_1154_; lean_object* v_v_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1169_; 
v_k_1154_ = lean_ctor_get(v_r_1148_, 1);
v_v_1155_ = lean_ctor_get(v_r_1148_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_r_1148_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1170_ = lean_ctor_get(v_r_1148_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_1148_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_r_1148_, 0);
lean_dec(v_unused_1172_);
v___x_1157_ = v_r_1148_;
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_v_1155_);
lean_inc(v_k_1154_);
lean_dec(v_r_1148_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(3u);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 4, v_l_1131_);
lean_ctor_set(v___x_1157_, 3, v_l_1131_);
lean_ctor_set(v___x_1157_, 2, v_v_1150_);
lean_ctor_set(v___x_1157_, 1, v_k_1149_);
lean_ctor_set(v___x_1157_, 0, v___x_1045_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_l_1131_);
v___x_1161_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 4, v_l_1131_);
lean_ctor_set(v___x_1152_, 2, v_v_898_);
lean_ctor_set(v___x_1152_, 1, v_k_897_);
lean_ctor_set(v___x_1152_, 0, v___x_1045_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_l_1131_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_l_1131_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_1163_);
lean_ctor_set(v___x_902_, 3, v___x_1161_);
lean_ctor_set(v___x_902_, 2, v_v_1155_);
lean_ctor_set(v___x_902_, 1, v_k_1154_);
lean_ctor_set(v___x_902_, 0, v___x_1159_);
v___x_1165_ = v___x_902_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(2u);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_1148_);
lean_ctor_set(v___x_902_, 3, v_impl_1044_);
lean_ctor_set(v___x_902_, 0, v___x_1177_);
v___x_1179_ = v___x_902_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_897_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_898_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_impl_1044_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_r_1148_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_k_893_);
lean_ctor_set(v___x_1183_, 2, v_v_894_);
lean_ctor_set(v___x_1183_, 3, v_t_895_);
lean_ctor_set(v___x_1183_, 4, v_t_895_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1184_, lean_object* v_b_1185_){
_start:
{
if (lean_obj_tag(v_as_x27_1184_) == 0)
{
return v_b_1185_;
}
else
{
lean_object* v_head_1186_; lean_object* v_tail_1187_; lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v_r_1190_; 
v_head_1186_ = lean_ctor_get(v_as_x27_1184_, 0);
v_tail_1187_ = lean_ctor_get(v_as_x27_1184_, 1);
v_fst_1188_ = lean_ctor_get(v_head_1186_, 0);
v_snd_1189_ = lean_ctor_get(v_head_1186_, 1);
lean_inc(v_snd_1189_);
lean_inc(v_fst_1188_);
v_r_1190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1188_, v_snd_1189_, v_b_1185_);
v_as_x27_1184_ = v_tail_1187_;
v_b_1185_ = v_r_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1192_, lean_object* v_b_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1192_, v_b_1193_);
lean_dec(v_as_x27_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1203_, lean_object* v_expr_1204_, lean_object* v_lctx_1205_, lean_object* v_location_x3f_1206_, lean_object* v_docString_x3f_1207_, lean_object* v_mkDocString_x3f_1208_, uint8_t v_explicit_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___y_1217_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_fmt_1203_);
v___x_1212_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1213_ = lean_box(0);
v___x_1214_ = 0;
v___x_1215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1215_, 0, v___x_1212_);
lean_ctor_set(v___x_1215_, 1, v_lctx_1205_);
lean_ctor_set(v___x_1215_, 2, v___x_1213_);
lean_ctor_set(v___x_1215_, 3, v_expr_1204_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*4, v___x_1214_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*4 + 1, v___x_1214_);
if (lean_obj_tag(v_mkDocString_x3f_1208_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1207_) == 0)
{
v___y_1217_ = v_mkDocString_x3f_1208_;
goto v___jp_1216_;
}
else
{
lean_object* v_val_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_val_1227_ = lean_ctor_get(v_docString_x3f_1207_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_docString_x3f_1207_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_docString_x3f_1207_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_val_1227_);
lean_dec(v_docString_x3f_1207_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___f_1231_; lean_object* v___x_1233_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1231_, 0, v_val_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___f_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___f_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v___y_1217_ = v___x_1233_;
goto v___jp_1216_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1207_);
v___y_1217_ = v_mkDocString_x3f_1208_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_r_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1218_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1218_, 0, v___x_1215_);
lean_ctor_set(v___x_1218_, 1, v_location_x3f_1206_);
lean_ctor_set(v___x_1218_, 2, v___y_1217_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*3, v_explicit_1209_);
v___x_1219_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1210_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v_r_1223_ = lean_box(1);
v___x_1224_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1222_, v_r_1223_);
lean_dec_ref_known(v___x_1222_, 2);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1211_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1236_, lean_object* v_expr_1237_, lean_object* v_lctx_1238_, lean_object* v_location_x3f_1239_, lean_object* v_docString_x3f_1240_, lean_object* v_mkDocString_x3f_1241_, lean_object* v_explicit_1242_){
_start:
{
uint8_t v_explicit_boxed_1243_; lean_object* v_res_1244_; 
v_explicit_boxed_1243_ = lean_unbox(v_explicit_1242_);
v_res_1244_ = l_Lean_MessageData_withExprHover(v_fmt_1236_, v_expr_1237_, v_lctx_1238_, v_location_x3f_1239_, v_docString_x3f_1240_, v_mkDocString_x3f_1241_, v_explicit_boxed_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1245_, lean_object* v_k_1246_, lean_object* v_v_1247_, lean_object* v_t_1248_, lean_object* v_hl_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1246_, v_v_1247_, v_t_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1251_, lean_object* v_as_x27_1252_, lean_object* v_b_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1252_, v_b_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1256_, lean_object* v_as_x27_1257_, lean_object* v_b_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1256_, v_as_x27_1257_, v_b_1258_, v_a_1259_);
lean_dec(v_as_x27_1257_);
lean_dec(v_as_1256_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1261_, lean_object* v_expr_1262_, lean_object* v_location_x3f_1263_, lean_object* v_docString_x3f_1264_, lean_object* v_mkDocString_x3f_1265_, uint8_t v_explicit_1266_, lean_object* v_toPure_1267_, lean_object* v_lctx_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_MessageData_withExprHover(v_fmt_1261_, v_expr_1262_, v_lctx_1268_, v_location_x3f_1263_, v_docString_x3f_1264_, v_mkDocString_x3f_1265_, v_explicit_1266_);
v___x_1270_ = lean_apply_2(v_toPure_1267_, lean_box(0), v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1271_, lean_object* v_expr_1272_, lean_object* v_location_x3f_1273_, lean_object* v_docString_x3f_1274_, lean_object* v_mkDocString_x3f_1275_, lean_object* v_explicit_1276_, lean_object* v_toPure_1277_, lean_object* v_lctx_1278_){
_start:
{
uint8_t v_explicit_boxed_1279_; lean_object* v_res_1280_; 
v_explicit_boxed_1279_ = lean_unbox(v_explicit_1276_);
v_res_1280_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1271_, v_expr_1272_, v_location_x3f_1273_, v_docString_x3f_1274_, v_mkDocString_x3f_1275_, v_explicit_boxed_1279_, v_toPure_1277_, v_lctx_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_fmt_1283_, lean_object* v_expr_1284_, lean_object* v_lctx_x3f_1285_, lean_object* v_location_x3f_1286_, lean_object* v_docString_x3f_1287_, lean_object* v_mkDocString_x3f_1288_, uint8_t v_explicit_1289_){
_start:
{
lean_object* v_toApplicative_1290_; lean_object* v_toBind_1291_; lean_object* v_toPure_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; 
v_toApplicative_1290_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1290_);
v_toBind_1291_ = lean_ctor_get(v_inst_1281_, 1);
lean_inc(v_toBind_1291_);
lean_dec_ref(v_inst_1281_);
v_toPure_1292_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_inc_n(v_toPure_1292_, 2);
lean_dec_ref(v_toApplicative_1290_);
v___x_1293_ = lean_box(v_explicit_1289_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1294_, 0, v_fmt_1283_);
lean_closure_set(v___f_1294_, 1, v_expr_1284_);
lean_closure_set(v___f_1294_, 2, v_location_x3f_1286_);
lean_closure_set(v___f_1294_, 3, v_docString_x3f_1287_);
lean_closure_set(v___f_1294_, 4, v_mkDocString_x3f_1288_);
lean_closure_set(v___f_1294_, 5, v___x_1293_);
lean_closure_set(v___f_1294_, 6, v_toPure_1292_);
if (lean_obj_tag(v_lctx_x3f_1285_) == 0)
{
lean_object* v___x_1295_; 
lean_dec(v_toPure_1292_);
v___x_1295_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v_inst_1282_, v___f_1294_);
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_inst_1282_);
v_val_1296_ = lean_ctor_get(v_lctx_x3f_1285_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_lctx_x3f_1285_, 1);
v___x_1297_ = lean_apply_2(v_toPure_1292_, lean_box(0), v_val_1296_);
v___x_1298_ = lean_apply_4(v_toBind_1291_, lean_box(0), lean_box(0), v___x_1297_, v___f_1294_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_fmt_1301_, lean_object* v_expr_1302_, lean_object* v_lctx_x3f_1303_, lean_object* v_location_x3f_1304_, lean_object* v_docString_x3f_1305_, lean_object* v_mkDocString_x3f_1306_, lean_object* v_explicit_1307_){
_start:
{
uint8_t v_explicit_boxed_1308_; lean_object* v_res_1309_; 
v_explicit_boxed_1308_ = lean_unbox(v_explicit_1307_);
v_res_1309_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1299_, v_inst_1300_, v_fmt_1301_, v_expr_1302_, v_lctx_x3f_1303_, v_location_x3f_1304_, v_docString_x3f_1305_, v_mkDocString_x3f_1306_, v_explicit_boxed_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_fmt_1313_, lean_object* v_expr_1314_, lean_object* v_lctx_x3f_1315_, lean_object* v_location_x3f_1316_, lean_object* v_docString_x3f_1317_, lean_object* v_mkDocString_x3f_1318_, uint8_t v_explicit_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1311_, v_inst_1312_, v_fmt_1313_, v_expr_1314_, v_lctx_x3f_1315_, v_location_x3f_1316_, v_docString_x3f_1317_, v_mkDocString_x3f_1318_, v_explicit_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_fmt_1324_, lean_object* v_expr_1325_, lean_object* v_lctx_x3f_1326_, lean_object* v_location_x3f_1327_, lean_object* v_docString_x3f_1328_, lean_object* v_mkDocString_x3f_1329_, lean_object* v_explicit_1330_){
_start:
{
uint8_t v_explicit_boxed_1331_; lean_object* v_res_1332_; 
v_explicit_boxed_1331_ = lean_unbox(v_explicit_1330_);
v_res_1332_ = l_Lean_MessageData_withExprHoverM(v_m_1321_, v_inst_1322_, v_inst_1323_, v_fmt_1324_, v_expr_1325_, v_lctx_x3f_1326_, v_location_x3f_1327_, v_docString_x3f_1328_, v_mkDocString_x3f_1329_, v_explicit_boxed_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1333_, lean_object* v_display_1334_, lean_object* v_toPure_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_____do__lift_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1338_, v_userName_1333_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec(v_inst_1337_);
lean_dec_ref(v_inst_1336_);
v___x_1340_ = l_Lean_MessageData_ofName(v_display_1334_);
v___x_1341_ = lean_apply_2(v_toPure_1335_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_toPure_1335_);
v_val_1342_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1344_ = v___x_1339_;
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v___x_1339_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = 1;
v___x_1347_ = l_Lean_Name_toString(v_display_1334_, v___x_1346_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 3);
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1350_ = l_Lean_LocalDecl_fvarId(v_val_1342_);
lean_dec(v_val_1342_);
v___x_1351_ = l_Lean_Expr_fvar___override(v___x_1350_);
v___x_1352_ = lean_box(0);
v___x_1353_ = 0;
v___x_1354_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1336_, v_inst_1337_, v___x_1349_, v___x_1351_, v___x_1352_, v___x_1352_, v___x_1352_, v___x_1352_, v___x_1353_);
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1357_, lean_object* v_display_1358_, lean_object* v_toPure_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_____do__lift_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1357_, v_display_1358_, v_toPure_1359_, v_inst_1360_, v_inst_1361_, v_____do__lift_1362_);
lean_dec_ref(v_____do__lift_1362_);
lean_dec(v_userName_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_userName_1366_){
_start:
{
lean_object* v_toApplicative_1367_; lean_object* v_toBind_1368_; lean_object* v_toPure_1369_; lean_object* v_display_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; 
v_toApplicative_1367_ = lean_ctor_get(v_inst_1364_, 0);
v_toBind_1368_ = lean_ctor_get(v_inst_1364_, 1);
lean_inc(v_toBind_1368_);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1367_, 1);
lean_inc(v_toPure_1369_);
lean_inc(v_userName_1366_);
v_display_1370_ = l_Lean_Name_simpMacroScopes(v_userName_1366_);
lean_inc(v_inst_1365_);
v___f_1371_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1371_, 0, v_userName_1366_);
lean_closure_set(v___f_1371_, 1, v_display_1370_);
lean_closure_set(v___f_1371_, 2, v_toPure_1369_);
lean_closure_set(v___f_1371_, 3, v_inst_1364_);
lean_closure_set(v___f_1371_, 4, v_inst_1365_);
v___x_1372_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v_inst_1365_, v___f_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_userName_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1374_, v_inst_1375_, v_userName_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1378_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
lean_ctor_set(v___x_1383_, 3, v___x_1382_);
lean_ctor_set(v___x_1383_, 4, v___x_1381_);
lean_ctor_set(v___x_1383_, 5, v___x_1381_);
lean_ctor_set(v___x_1383_, 6, v___x_1381_);
lean_ctor_set(v___x_1383_, 7, v___x_1381_);
lean_ctor_set(v___x_1383_, 8, v___x_1381_);
lean_ctor_set(v___x_1383_, 9, v___x_1381_);
lean_ctor_set(v___x_1383_, 10, v___x_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1384_, lean_object* v_a_1385_){
_start:
{
switch(lean_obj_tag(v_a_1385_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1384_) == 0)
{
lean_object* v_hasSyntheticSorry_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_hasSyntheticSorry_1386_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_hasSyntheticSorry_1386_);
lean_dec_ref_known(v_a_1385_, 2);
v___x_1387_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1388_ = lean_apply_1(v_hasSyntheticSorry_1386_, v___x_1387_);
v___x_1389_ = lean_unbox(v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v_hasSyntheticSorry_1390_; lean_object* v_val_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_hasSyntheticSorry_1390_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_hasSyntheticSorry_1390_);
lean_dec_ref_known(v_a_1385_, 2);
v_val_1391_ = lean_ctor_get(v_mctx_x3f_1384_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v_mctx_x3f_1384_, 1);
v___x_1392_ = lean_apply_1(v_hasSyntheticSorry_1390_, v_val_1391_);
v___x_1393_ = lean_unbox(v___x_1392_);
return v___x_1393_;
}
}
case 3:
{
lean_object* v_a_1394_; lean_object* v_a_1395_; lean_object* v_mctx_1396_; lean_object* v___x_1397_; 
lean_dec(v_mctx_x3f_1384_);
v_a_1394_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1394_);
v_a_1395_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1395_);
lean_dec_ref_known(v_a_1385_, 2);
v_mctx_1396_ = lean_ctor_get(v_a_1394_, 1);
lean_inc_ref(v_mctx_1396_);
lean_dec_ref(v_a_1394_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_mctx_1396_);
v_mctx_x3f_1384_ = v___x_1397_;
v_a_1385_ = v_a_1395_;
goto _start;
}
case 4:
{
lean_object* v_a_1399_; 
v_a_1399_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1399_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1399_;
goto _start;
}
case 5:
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1401_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1401_;
goto _start;
}
case 6:
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1403_);
lean_dec_ref_known(v_a_1385_, 1);
v_a_1385_ = v_a_1403_;
goto _start;
}
case 7:
{
lean_object* v_a_1405_; lean_object* v_a_1406_; uint8_t v___x_1407_; 
v_a_1405_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_a_1405_);
v_a_1406_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1406_);
lean_dec_ref_known(v_a_1385_, 2);
lean_inc(v_mctx_x3f_1384_);
v___x_1407_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1384_, v_a_1405_);
if (v___x_1407_ == 0)
{
v_a_1385_ = v_a_1406_;
goto _start;
}
else
{
lean_dec_ref(v_a_1406_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1407_;
}
}
case 8:
{
lean_object* v_a_1409_; 
v_a_1409_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1409_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1409_;
goto _start;
}
case 11:
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_a_1411_);
lean_dec_ref_known(v_a_1385_, 2);
v_a_1385_ = v_a_1411_;
goto _start;
}
case 9:
{
lean_object* v_msg_1413_; lean_object* v_children_1414_; uint8_t v___x_1415_; 
v_msg_1413_ = lean_ctor_get(v_a_1385_, 1);
lean_inc_ref(v_msg_1413_);
v_children_1414_ = lean_ctor_get(v_a_1385_, 2);
lean_inc_ref(v_children_1414_);
lean_dec_ref_known(v_a_1385_, 3);
lean_inc(v_mctx_x3f_1384_);
v___x_1415_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1384_, v_msg_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_children_1414_);
v___x_1418_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1418_;
}
else
{
if (v___x_1418_ == 0)
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1417_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1384_, v_children_1414_, v___x_1419_, v___x_1420_);
lean_dec_ref(v_children_1414_);
return v___x_1421_;
}
}
}
else
{
lean_dec_ref(v_children_1414_);
lean_dec(v_mctx_x3f_1384_);
return v___x_1415_;
}
}
default: 
{
uint8_t v___x_1422_; 
lean_dec_ref(v_a_1385_);
lean_dec(v_mctx_x3f_1384_);
v___x_1422_ = 0;
return v___x_1422_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1423_, lean_object* v_as_1424_, size_t v_i_1425_, size_t v_stop_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_eq(v_i_1425_, v_stop_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_array_uget_borrowed(v_as_1424_, v_i_1425_);
lean_inc(v___x_1428_);
lean_inc(v_mctx_x3f_1423_);
v___x_1429_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1423_, v___x_1428_);
if (v___x_1429_ == 0)
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1425_, v___x_1430_);
v_i_1425_ = v___x_1431_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1423_);
return v___x_1429_;
}
}
else
{
uint8_t v___x_1433_; 
lean_dec(v_mctx_x3f_1423_);
v___x_1433_ = 0;
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1434_, lean_object* v_as_1435_, lean_object* v_i_1436_, lean_object* v_stop_1437_){
_start:
{
size_t v_i_boxed_1438_; size_t v_stop_boxed_1439_; uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_stop_boxed_1439_ = lean_unbox_usize(v_stop_1437_);
lean_dec(v_stop_1437_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1434_, v_as_1435_, v_i_boxed_1438_, v_stop_boxed_1439_);
lean_dec_ref(v_as_1435_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1442_, lean_object* v_a_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1442_, v_a_1443_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_box(0);
v___x_1448_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1447_, v_msg_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1449_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object* v_name_1452_, lean_object* v_decl_1453_, lean_object* v_ref_1454_){
_start:
{
lean_object* v_defValue_1456_; lean_object* v_descr_1457_; lean_object* v_deprecation_x3f_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_defValue_1456_ = lean_ctor_get(v_decl_1453_, 0);
v_descr_1457_ = lean_ctor_get(v_decl_1453_, 1);
v_deprecation_x3f_1458_ = lean_ctor_get(v_decl_1453_, 2);
lean_inc(v_defValue_1456_);
v___x_1459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_defValue_1456_);
lean_inc(v_deprecation_x3f_1458_);
lean_inc_ref(v_descr_1457_);
lean_inc_n(v_name_1452_, 2);
v___x_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1460_, 0, v_name_1452_);
lean_ctor_set(v___x_1460_, 1, v_ref_1454_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
lean_ctor_set(v___x_1460_, 3, v_descr_1457_);
lean_ctor_set(v___x_1460_, 4, v_deprecation_x3f_1458_);
v___x_1461_ = lean_register_option(v_name_1452_, v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1470_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_inc(v_defValue_1456_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_name_1452_);
lean_ctor_set(v___x_1465_, 1, v_defValue_1456_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_name_1452_);
v_a_1471_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1461_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1461_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1479_, lean_object* v_decl_1480_, lean_object* v_ref_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1479_, v_decl_1480_, v_ref_1481_);
lean_dec_ref(v_decl_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1498_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1499_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1500_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v___x_1497_, v___x_1498_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_nat_to_int(v_a_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_opts_1505_, lean_object* v_opt_1506_){
_start:
{
lean_object* v_name_1507_; lean_object* v_defValue_1508_; lean_object* v_map_1509_; lean_object* v___x_1510_; 
v_name_1507_ = lean_ctor_get(v_opt_1506_, 0);
v_defValue_1508_ = lean_ctor_get(v_opt_1506_, 1);
v_map_1509_ = lean_ctor_get(v_opts_1505_, 0);
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1509_, v_name_1507_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_inc(v_defValue_1508_);
return v_defValue_1508_;
}
else
{
lean_object* v_val_1511_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1510_, 1);
if (lean_obj_tag(v_val_1511_) == 3)
{
lean_object* v_v_1512_; 
v_v_1512_ = lean_ctor_get(v_val_1511_, 0);
lean_inc(v_v_1512_);
lean_dec_ref_known(v_val_1511_, 1);
return v_v_1512_;
}
else
{
lean_dec(v_val_1511_);
lean_inc(v_defValue_1508_);
return v_defValue_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_opts_1513_, lean_object* v_opt_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3(v_opts_1513_, v_opt_1514_);
lean_dec_ref(v_opt_1514_);
lean_dec_ref(v_opts_1513_);
return v_res_1515_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = l_instMonadBaseIO;
v___x_1518_ = l_instInhabitedOfMonad___redArg(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__4(lean_object* v_msg_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1591__overap_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__4___closed__0);
v___x_1591__overap_1522_ = lean_panic_fn_borrowed(v___x_1521_, v_msg_1519_);
v___x_1523_ = lean_apply_1(v___x_1591__overap_1522_, lean_box(0));
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__4___boxed(lean_object* v_msg_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_panic___at___00Lean_MessageData_formatAux_spec__4(v_msg_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_dec(v_x_1527_);
return v_x_1528_;
}
else
{
lean_object* v_head_1530_; lean_object* v_tail_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1540_; 
v_head_1530_ = lean_ctor_get(v_x_1529_, 0);
v_tail_1531_ = lean_ctor_get(v_x_1529_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1533_ = v_x_1529_;
v_isShared_1534_ = v_isSharedCheck_1540_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_tail_1531_);
lean_inc(v_head_1530_);
lean_dec(v_x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1540_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
lean_inc(v_x_1527_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 5);
lean_ctor_set(v___x_1533_, 1, v_x_1527_);
lean_ctor_set(v___x_1533_, 0, v_x_1528_);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_x_1528_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_x_1527_);
v___x_1536_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v_head_1530_);
v_x_1528_ = v___x_1537_;
v_x_1529_ = v_tail_1531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1541_) == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_x_1542_);
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
else
{
lean_object* v_tail_1544_; 
v_tail_1544_ = lean_ctor_get(v_x_1541_, 1);
if (lean_obj_tag(v_tail_1544_) == 0)
{
lean_object* v_head_1545_; 
lean_dec(v_x_1542_);
v_head_1545_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_head_1545_);
lean_dec_ref_known(v_x_1541_, 2);
return v_head_1545_;
}
else
{
lean_object* v_head_1546_; lean_object* v___x_1547_; 
lean_inc(v_tail_1544_);
v_head_1546_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_head_1546_);
lean_dec_ref_known(v_x_1541_, 2);
v___x_1547_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1542_, v_head_1546_, v_tail_1544_);
return v___x_1547_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1562_; double v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = lean_float_of_nat(v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v_children_1577_; 
switch(lean_obj_tag(v_x_1572_))
{
case 0:
{
lean_object* v_a_1586_; lean_object* v_fmt_1587_; 
lean_dec(v_x_1571_);
lean_dec_ref(v_x_1570_);
v_a_1586_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_a_1586_);
lean_dec_ref_known(v_x_1572_, 1);
v_fmt_1587_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_fmt_1587_);
lean_dec_ref(v_a_1586_);
return v_fmt_1587_;
}
case 1:
{
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_x_1570_);
v_a_1588_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_x_1572_, 1);
v___x_1589_ = l_Lean_formatRawGoal(v_a_1588_);
return v___x_1589_;
}
else
{
lean_object* v_a_1590_; lean_object* v_val_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1590_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v_x_1572_, 1);
v_val_1591_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v_x_1571_, 1);
v___x_1592_ = l_Lean_MessageData_mkPPContext(v_x_1570_, v_val_1591_);
lean_dec(v_val_1591_);
lean_dec_ref(v_x_1570_);
v___x_1593_ = l_Lean_ppGoal(v___x_1592_, v_a_1590_);
return v___x_1593_;
}
}
case 3:
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; 
lean_dec(v_x_1571_);
v_a_1594_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_a_1594_);
v_a_1595_ = lean_ctor_get(v_x_1572_, 1);
lean_inc_ref(v_a_1595_);
lean_dec_ref_known(v_x_1572_, 2);
v___x_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1594_);
v_x_1571_ = v___x_1596_;
v_x_1572_ = v_a_1595_;
goto _start;
}
case 4:
{
lean_object* v_a_1598_; lean_object* v_a_1599_; 
lean_dec_ref(v_x_1570_);
v_a_1598_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_a_1598_);
v_a_1599_ = lean_ctor_get(v_x_1572_, 1);
lean_inc_ref(v_a_1599_);
lean_dec_ref_known(v_x_1572_, 2);
v_x_1570_ = v_a_1598_;
v_x_1572_ = v_a_1599_;
goto _start;
}
case 5:
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
v_a_1601_ = lean_ctor_get(v_x_1572_, 0);
v_a_1602_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1604_ = v_x_1572_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v_x_1572_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = l_Lean_MessageData_formatAux(v_x_1570_, v_x_1571_, v_a_1602_);
v___x_1607_ = lean_nat_to_int(v_a_1601_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 4);
lean_ctor_set(v___x_1604_, 1, v___x_1606_);
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1606_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
case 6:
{
lean_object* v_a_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v_a_1612_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_a_1612_);
lean_dec_ref_known(v_x_1572_, 1);
v___x_1613_ = l_Lean_MessageData_formatAux(v_x_1570_, v_x_1571_, v_a_1612_);
v___x_1614_ = 0;
v___x_1615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*1, v___x_1614_);
return v___x_1615_;
}
case 7:
{
lean_object* v_a_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1626_; 
v_a_1616_ = lean_ctor_get(v_x_1572_, 0);
v_a_1617_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1619_ = v_x_1572_;
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_inc(v_a_1616_);
lean_dec(v_x_1572_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
lean_inc(v_x_1571_);
lean_inc_ref(v_x_1570_);
v___x_1621_ = l_Lean_MessageData_formatAux(v_x_1570_, v_x_1571_, v_a_1616_);
v___x_1622_ = l_Lean_MessageData_formatAux(v_x_1570_, v_x_1571_, v_a_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 5);
lean_ctor_set(v___x_1619_, 1, v___x_1622_);
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
case 9:
{
lean_object* v_data_1627_; lean_object* v_msg_1628_; lean_object* v_children_1629_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v_cls_1654_; lean_object* v_result_x3f_1655_; double v_startTime_1656_; double v_stopTime_1657_; lean_object* v_msg_1659_; uint8_t v___x_1674_; 
v_data_1627_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_data_1627_);
v_msg_1628_ = lean_ctor_get(v_x_1572_, 1);
lean_inc_ref(v_msg_1628_);
v_children_1629_ = lean_ctor_get(v_x_1572_, 2);
lean_inc_ref(v_children_1629_);
lean_dec_ref_known(v_x_1572_, 3);
v_cls_1654_ = lean_ctor_get(v_data_1627_, 0);
lean_inc(v_cls_1654_);
v_result_x3f_1655_ = lean_ctor_get(v_data_1627_, 1);
lean_inc(v_result_x3f_1655_);
v_startTime_1656_ = lean_ctor_get_float(v_data_1627_, sizeof(void*)*3);
v_stopTime_1657_ = lean_ctor_get_float(v_data_1627_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1627_);
v___x_1674_ = l_Lean_Name_isAnonymous(v_cls_1654_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_msg_1681_; double v___x_1682_; uint8_t v___x_1683_; 
v___x_1675_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1676_ = 1;
v___x_1677_ = l_Lean_Name_toString(v_cls_1654_, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1675_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v_msg_1681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_msg_1681_, 0, v___x_1679_);
lean_ctor_set(v_msg_1681_, 1, v___x_1680_);
v___x_1682_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1683_ = lean_float_beq(v_startTime_1656_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; double v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_msg_1690_; 
v___x_1684_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_msg_1681_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_float_sub(v_stopTime_1657_, v_startTime_1656_);
v___x_1687_ = lean_float_to_string(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1685_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v_msg_1690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_msg_1690_, 0, v___x_1689_);
lean_ctor_set(v_msg_1690_, 1, v___x_1680_);
v_msg_1659_ = v_msg_1690_;
goto v___jp_1658_;
}
else
{
v_msg_1659_ = v_msg_1681_;
goto v___jp_1658_;
}
}
else
{
size_t v_sz_1691_; size_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_result_x3f_1655_);
lean_dec(v_cls_1654_);
lean_dec_ref(v_msg_1628_);
v_sz_1691_ = lean_array_size(v_children_1629_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1570_, v_x_1571_, v_sz_1691_, v___x_1692_, v_children_1629_);
v___x_1694_ = lean_array_to_list(v___x_1693_);
v___x_1695_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v___x_1696_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1694_, v___x_1695_);
return v___x_1696_;
}
v___jp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1633_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___y_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___y_1632_);
v___x_1637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1634_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
if (lean_obj_tag(v_x_1571_) == 0)
{
v___y_1575_ = v___x_1637_;
v___y_1576_ = v___x_1635_;
v_children_1577_ = v_children_1629_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1638_; lean_object* v_opts_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_val_1638_ = lean_ctor_get(v_x_1571_, 0);
v_opts_1639_ = lean_ctor_get(v_val_1638_, 3);
v___x_1640_ = l_Lean_MessageData_maxTraceChildren;
v___x_1641_ = l_Lean_Option_get___at___00Lean_MessageData_formatAux_spec__3(v_opts_1639_, v___x_1640_);
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_nat_dec_lt(v___x_1642_, v___x_1641_);
if (v___x_1643_ == 0)
{
lean_dec(v___x_1641_);
v___y_1575_ = v___x_1637_;
v___y_1576_ = v___x_1635_;
v_children_1577_ = v_children_1629_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_array_get_size(v_children_1629_);
v___x_1645_ = lean_nat_dec_lt(v___x_1641_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec(v___x_1641_);
v___y_1575_ = v___x_1637_;
v___y_1576_ = v___x_1635_;
v_children_1577_ = v_children_1629_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc(v___x_1641_);
v___x_1646_ = l_Array_extract___redArg(v_children_1629_, v___x_1642_, v___x_1641_);
lean_dec_ref(v_children_1629_);
v___x_1647_ = lean_nat_sub(v___x_1644_, v___x_1641_);
lean_dec(v___x_1641_);
v___x_1648_ = l_Nat_reprFast(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Lean_MessageData_ofFormat(v___x_1651_);
v___x_1653_ = lean_array_push(v___x_1646_, v___x_1652_);
v___y_1575_ = v___x_1637_;
v___y_1576_ = v___x_1635_;
v_children_1577_ = v___x_1653_;
goto v___jp_1574_;
}
}
}
}
v___jp_1658_:
{
lean_object* v___x_1660_; 
lean_inc(v_x_1571_);
lean_inc_ref(v_x_1570_);
v___x_1660_ = l_Lean_MessageData_formatAux(v_x_1570_, v_x_1571_, v_msg_1628_);
if (lean_obj_tag(v_result_x3f_1655_) == 0)
{
v___y_1631_ = v_msg_1659_;
v___y_1632_ = v___x_1660_;
goto v___jp_1630_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1673_; 
v_val_1661_ = lean_ctor_get(v_result_x3f_1655_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_result_x3f_1655_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1663_ = v_result_x3f_1655_;
v_isShared_1664_ = v_isSharedCheck_1673_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v_result_x3f_1655_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1673_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_unbox(v_val_1661_);
lean_dec(v_val_1661_);
v___x_1666_ = l_Lean_TraceResult_toEmoji(v___x_1665_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 3);
lean_ctor_set(v___x_1663_, 0, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1660_);
v___y_1631_ = v_msg_1659_;
v___y_1632_ = v___x_1671_;
goto v___jp_1630_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1697_; lean_object* v___x_1698_; lean_object* v___y_1700_; 
v_f_1697_ = lean_ctor_get(v_x_1572_, 0);
lean_inc_ref(v_f_1697_);
lean_dec_ref_known(v_x_1572_, 2);
v___x_1698_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_box(0);
v___y_1700_ = v___x_1716_;
goto v___jp_1699_;
}
else
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_val_1717_ = lean_ctor_get(v_x_1571_, 0);
v___x_1718_ = l_Lean_MessageData_mkPPContext(v_x_1570_, v_val_1717_);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___y_1700_ = v___x_1719_;
goto v___jp_1699_;
}
v___jp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_apply_2(v_f_1697_, v___y_1700_, lean_box(0));
v___x_1702_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1701_, v___x_1698_);
if (lean_obj_tag(v___x_1702_) == 1)
{
lean_object* v_val_1703_; 
lean_dec(v___x_1701_);
v_val_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v_x_1572_ = v_val_1703_;
goto _start;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v___x_1702_);
lean_dec(v_x_1571_);
lean_dec_ref(v_x_1570_);
v___x_1705_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1706_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__13));
v___x_1707_ = lean_unsigned_to_nat(409u);
v___x_1708_ = lean_unsigned_to_nat(8u);
v___x_1709_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__14));
v___x_1710_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1701_);
lean_dec(v___x_1701_);
v___x_1711_ = 1;
v___x_1712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1710_, v___x_1711_);
v___x_1713_ = lean_string_append(v___x_1709_, v___x_1712_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = l_mkPanicMessageWithDecl(v___x_1705_, v___x_1706_, v___x_1707_, v___x_1708_, v___x_1713_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_panic___at___00Lean_MessageData_formatAux_spec__4(v___x_1714_);
return v___x_1715_;
}
}
}
default: 
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v_x_1572_, 1);
lean_inc_ref(v_a_1720_);
lean_dec_ref(v_x_1572_);
v_x_1572_ = v_a_1720_;
goto _start;
}
}
v___jp_1574_:
{
size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_sz_1578_ = lean_array_size(v_children_1577_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1570_, v_x_1571_, v_sz_1578_, v___x_1579_, v_children_1577_);
v___x_1581_ = lean_array_to_list(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___y_1575_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v___x_1584_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1582_, v___x_1583_);
lean_inc(v___y_1576_);
v___x_1585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1576_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1722_, lean_object* v_x_1723_, size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_bs_1726_){
_start:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1728_ == 0)
{
lean_dec(v_x_1723_);
lean_dec_ref(v_x_1722_);
return v_bs_1726_;
}
else
{
lean_object* v_v_1729_; lean_object* v___x_1730_; lean_object* v_bs_x27_1731_; lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v_v_1729_ = lean_array_uget(v_bs_1726_, v_i_1725_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v_bs_x27_1731_ = lean_array_uset(v_bs_1726_, v_i_1725_, v___x_1730_);
lean_inc(v_x_1723_);
lean_inc_ref(v_x_1722_);
v___x_1732_ = l_Lean_MessageData_formatAux(v_x_1722_, v_x_1723_, v_v_1729_);
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1725_, v___x_1733_);
v___x_1735_ = lean_array_uset(v_bs_x27_1731_, v_i_1725_, v___x_1732_);
v_i_1725_ = v___x_1734_;
v_bs_1726_ = v___x_1735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_bs_1741_, lean_object* v___y_1742_){
_start:
{
size_t v_sz_boxed_1743_; size_t v_i_boxed_1744_; lean_object* v_res_1745_; 
v_sz_boxed_1743_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1737_, v_x_1738_, v_sz_boxed_1743_, v_i_boxed_1744_, v_bs_1741_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_MessageData_formatAux(v_x_1746_, v_x_1747_, v_x_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1754_, lean_object* v_ctx_x3f_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1758_ = l_Lean_MessageData_formatAux(v___x_1757_, v_ctx_x3f_1755_, v_msgData_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1759_, lean_object* v_ctx_x3f_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_MessageData_format(v_msgData_1759_, v_ctx_x3f_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Lean_MessageData_format(v_msgData_1763_, v___x_1765_);
v___x_1767_ = l_Std_Format_defWidth;
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = l_Std_Format_pretty(v___x_1766_, v___x_1767_, v___x_1768_, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_MessageData_toString(v_msgData_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_a_1773_);
lean_ctor_set(v___x_1775_, 1, v_a_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_s_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_a_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1803_ = l_Lean_MessageData_ofFormat(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1804_){
_start:
{
if (lean_obj_tag(v_o_1804_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1805_;
}
else
{
lean_object* v_val_1806_; lean_object* v___x_1807_; 
v_val_1806_ = lean_ctor_get(v_o_1804_, 0);
lean_inc(v_val_1806_);
lean_dec_ref_known(v_o_1804_, 1);
v___x_1807_ = l_Lean_MessageData_ofExpr(v_val_1806_);
return v___x_1807_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1816_ = l_Lean_MessageData_ofFormat(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1817_, lean_object* v_i_1818_, lean_object* v_acc_1819_){
_start:
{
lean_object* v___y_1821_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_es_1817_);
v___x_1826_ = lean_nat_dec_lt(v_i_1818_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_i_1818_);
v___x_1827_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_acc_1819_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v_e_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_e_1829_ = lean_array_fget_borrowed(v_es_1817_, v_i_1818_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_nat_dec_eq(v_i_1818_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v_acc_1819_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
lean_inc(v_e_1829_);
v___x_1834_ = l_Lean_MessageData_ofExpr(v_e_1829_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___y_1821_ = v___x_1835_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc(v_e_1829_);
v___x_1836_ = l_Lean_MessageData_ofExpr(v_e_1829_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_acc_1819_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___y_1821_ = v___x_1837_;
goto v___jp_1820_;
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_add(v_i_1818_, v___x_1822_);
lean_dec(v_i_1818_);
v_i_1818_ = v___x_1823_;
v_acc_1819_ = v___y_1821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1838_, lean_object* v_i_1839_, lean_object* v_acc_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1838_, v_i_1839_, v_acc_1840_);
lean_dec_ref(v_es_1838_);
return v_res_1841_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1846_ = l_Lean_MessageData_ofFormat(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1850_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1847_, v___x_1848_, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1851_);
lean_dec_ref(v_es_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1855_, lean_object* v_f_1856_, lean_object* v_r_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1858_ = lean_string_length(v_l_1855_);
v___x_1859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_l_1855_);
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_f_1856_);
v___x_1862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_r_1857_);
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1861_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1858_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1869_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1870_ = l_Lean_MessageData_bracket(v___x_1868_, v_f_1867_, v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1873_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__7));
v___x_1874_ = l_Lean_MessageData_bracket(v___x_1872_, v_f_1871_, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v___x_1877_; 
lean_dec_ref(v_x_1876_);
v___x_1877_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1877_;
}
else
{
lean_object* v_tail_1878_; 
v_tail_1878_ = lean_ctor_get(v_x_1875_, 1);
if (lean_obj_tag(v_tail_1878_) == 0)
{
lean_object* v_head_1879_; 
lean_dec_ref(v_x_1876_);
v_head_1879_ = lean_ctor_get(v_x_1875_, 0);
lean_inc(v_head_1879_);
lean_dec_ref_known(v_x_1875_, 2);
return v_head_1879_;
}
else
{
lean_object* v_head_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
lean_inc(v_tail_1878_);
v_head_1880_ = lean_ctor_get(v_x_1875_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_x_1875_, 1);
lean_dec(v_unused_1890_);
v___x_1882_ = v_x_1875_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_head_1880_);
lean_dec(v_x_1875_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
lean_inc_ref(v_x_1876_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 7);
lean_ctor_set(v___x_1882_, 1, v_x_1876_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_head_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_x_1876_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = l_Lean_MessageData_joinSep(v_tail_1878_, v_x_1876_);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
return v___x_1887_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1895_ = l_Lean_MessageData_ofFormat(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1900_ = l_Lean_MessageData_ofFormat(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_box(1);
v___x_1902_ = l_Lean_MessageData_ofFormat(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1904_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1909_ = l_Lean_MessageData_joinSep(v_x_1906_, v___x_1908_);
v___x_1910_ = l_Lean_MessageData_sbracket(v___x_1909_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_array_to_list(v_msgs_1911_);
v___x_1913_ = l_Lean_MessageData_ofList(v___x_1912_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1918_ = l_Lean_MessageData_ofFormat(v___x_1917_);
return v___x_1918_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1923_ = l_Lean_MessageData_ofFormat(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1928_ = l_Lean_MessageData_ofFormat(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1929_){
_start:
{
if (lean_obj_tag(v_xs_1929_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1930_;
}
else
{
lean_object* v_tail_1931_; 
v_tail_1931_ = lean_ctor_get(v_xs_1929_, 1);
lean_inc(v_tail_1931_);
if (lean_obj_tag(v_tail_1931_) == 0)
{
lean_object* v_head_1932_; 
v_head_1932_ = lean_ctor_get(v_xs_1929_, 0);
lean_inc(v_head_1932_);
lean_dec_ref_known(v_xs_1929_, 2);
return v_head_1932_;
}
else
{
lean_object* v_tail_1933_; 
v_tail_1933_ = lean_ctor_get(v_tail_1931_, 1);
if (lean_obj_tag(v_tail_1933_) == 0)
{
lean_object* v_head_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1951_; 
v_head_1934_ = lean_ctor_get(v_xs_1929_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_xs_1929_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_xs_1929_, 1);
lean_dec(v_unused_1952_);
v___x_1936_ = v_xs_1929_;
v_isShared_1937_ = v_isSharedCheck_1951_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_head_1934_);
lean_dec(v_xs_1929_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1951_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_head_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1949_; 
v_head_1938_ = lean_ctor_get(v_tail_1931_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_tail_1931_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_tail_1931_, 1);
lean_dec(v_unused_1950_);
v___x_1940_ = v_tail_1931_;
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_head_1938_);
lean_dec(v_tail_1931_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v___x_1942_);
lean_ctor_set(v___x_1940_, 0, v_head_1934_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_head_1934_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 7);
lean_ctor_set(v___x_1936_, 1, v_head_1938_);
lean_ctor_set(v___x_1936_, 0, v___x_1944_);
v___x_1946_ = v___x_1936_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_head_1938_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1976_; 
v_isSharedCheck_1976_ = !lean_is_exclusive(v_tail_1931_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; lean_object* v_unused_1978_; 
v_unused_1977_ = lean_ctor_get(v_tail_1931_, 1);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_tail_1931_, 0);
lean_dec(v_unused_1978_);
v___x_1954_ = v_tail_1931_;
v_isShared_1955_ = v_isSharedCheck_1976_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v_tail_1931_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1976_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1956_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1929_);
v___x_1957_ = lean_array_mk(v_xs_1929_);
v___x_1958_ = lean_array_pop(v___x_1957_);
v___x_1959_ = lean_array_to_list(v___x_1958_);
v___x_1960_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1961_ = l_Lean_MessageData_joinSep(v___x_1959_, v___x_1960_);
v___x_1962_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 7);
lean_ctor_set(v___x_1954_, 1, v___x_1962_);
lean_ctor_set(v___x_1954_, 0, v___x_1961_);
v___x_1964_ = v___x_1954_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v___x_1965_ = l_List_getLast_x21___redArg(v___x_1956_, v_xs_1929_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_xs_1929_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; lean_object* v_unused_1974_; 
v_unused_1973_ = lean_ctor_get(v_xs_1929_, 1);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_xs_1929_, 0);
lean_dec(v_unused_1974_);
v___x_1967_ = v_xs_1929_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_xs_1929_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 7);
lean_ctor_set(v___x_1967_, 1, v___x_1965_);
lean_ctor_set(v___x_1967_, 0, v___x_1964_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
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
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1983_ = l_Lean_MessageData_ofFormat(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1988_ = l_Lean_MessageData_ofFormat(v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1989_){
_start:
{
if (lean_obj_tag(v_xs_1989_) == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1990_;
}
else
{
lean_object* v_tail_1991_; 
v_tail_1991_ = lean_ctor_get(v_xs_1989_, 1);
lean_inc(v_tail_1991_);
if (lean_obj_tag(v_tail_1991_) == 0)
{
lean_object* v_head_1992_; 
v_head_1992_ = lean_ctor_get(v_xs_1989_, 0);
lean_inc(v_head_1992_);
lean_dec_ref_known(v_xs_1989_, 2);
return v_head_1992_;
}
else
{
lean_object* v_tail_1993_; 
v_tail_1993_ = lean_ctor_get(v_tail_1991_, 1);
if (lean_obj_tag(v_tail_1993_) == 0)
{
lean_object* v_head_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2011_; 
v_head_1994_ = lean_ctor_get(v_xs_1989_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_xs_1989_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_xs_1989_, 1);
lean_dec(v_unused_2012_);
v___x_1996_ = v_xs_1989_;
v_isShared_1997_ = v_isSharedCheck_2011_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_head_1994_);
lean_dec(v_xs_1989_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2011_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_head_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2009_; 
v_head_1998_ = lean_ctor_get(v_tail_1991_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_tail_1991_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_tail_1991_, 1);
lean_dec(v_unused_2010_);
v___x_2000_ = v_tail_1991_;
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_head_1998_);
lean_dec(v_tail_1991_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 7);
lean_ctor_set(v___x_2000_, 1, v___x_2002_);
lean_ctor_set(v___x_2000_, 0, v_head_1994_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_head_1994_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 7);
lean_ctor_set(v___x_1996_, 1, v_head_1998_);
lean_ctor_set(v___x_1996_, 0, v___x_2004_);
v___x_2006_ = v___x_1996_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_head_1998_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2036_; 
v_isSharedCheck_2036_ = !lean_is_exclusive(v_tail_1991_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2037_ = lean_ctor_get(v_tail_1991_, 1);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_tail_1991_, 0);
lean_dec(v_unused_2038_);
v___x_2014_ = v_tail_1991_;
v_isShared_2015_ = v_isSharedCheck_2036_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_tail_1991_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2036_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2016_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1989_);
v___x_2017_ = lean_array_mk(v_xs_1989_);
v___x_2018_ = lean_array_pop(v___x_2017_);
v___x_2019_ = lean_array_to_list(v___x_2018_);
v___x_2020_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_2021_ = l_Lean_MessageData_joinSep(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 7);
lean_ctor_set(v___x_2014_, 1, v___x_2022_);
lean_ctor_set(v___x_2014_, 0, v___x_2021_);
v___x_2024_ = v___x_2014_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v___x_2025_ = l_List_getLast_x21___redArg(v___x_2016_, v_xs_1989_);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_xs_1989_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2033_ = lean_ctor_get(v_xs_1989_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_xs_1989_, 0);
lean_dec(v_unused_2034_);
v___x_2027_ = v_xs_1989_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v_xs_1989_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 7);
lean_ctor_set(v___x_2027_, 1, v___x_2025_);
lean_ctor_set(v___x_2027_, 0, v___x_2024_);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
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
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2045_ = l_Lean_MessageData_ofFormat(v___x_2044_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2047_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v___x_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_note_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2058_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_hint_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2065_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2067_ = lean_box(0);
v___x_2068_ = l_List_mapTR_loop___redArg(v___x_2066_, v_es_2065_, v___x_2067_);
v___x_2069_ = l_Lean_MessageData_ofList(v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2073_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2074_ = l_Lean_instInhabitedPosition_default;
v___x_2075_ = lean_box(0);
v___x_2076_ = 0;
v___x_2077_ = 2;
v___x_2078_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2078_, 0, v___x_2073_);
lean_ctor_set(v___x_2078_, 1, v___x_2074_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
lean_ctor_set(v___x_2078_, 3, v___x_2073_);
lean_ctor_set(v___x_2078_, 4, v_inst_2072_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*5, v___x_2076_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*5 + 1, v___x_2077_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*5 + 2, v___x_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2079_, lean_object* v_inst_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2084_, lean_object* v_inst_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2099_, lean_object* v_x_2100_){
_start:
{
lean_object* v_fileName_2101_; lean_object* v_pos_2102_; lean_object* v_endPos_2103_; uint8_t v_keepFullRange_2104_; uint8_t v_severity_2105_; uint8_t v_isSilent_2106_; lean_object* v_caption_2107_; lean_object* v_data_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_fileName_2101_ = lean_ctor_get(v_x_2100_, 0);
lean_inc_ref(v_fileName_2101_);
v_pos_2102_ = lean_ctor_get(v_x_2100_, 1);
lean_inc_ref(v_pos_2102_);
v_endPos_2103_ = lean_ctor_get(v_x_2100_, 2);
lean_inc(v_endPos_2103_);
v_keepFullRange_2104_ = lean_ctor_get_uint8(v_x_2100_, sizeof(void*)*5);
v_severity_2105_ = lean_ctor_get_uint8(v_x_2100_, sizeof(void*)*5 + 1);
v_isSilent_2106_ = lean_ctor_get_uint8(v_x_2100_, sizeof(void*)*5 + 2);
v_caption_2107_ = lean_ctor_get(v_x_2100_, 3);
lean_inc_ref(v_caption_2107_);
v_data_2108_ = lean_ctor_get(v_x_2100_, 4);
lean_inc(v_data_2108_);
lean_dec_ref(v_x_2100_);
v___x_2109_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2110_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_fileName_2101_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2116_ = l_Lean_instToJsonPosition_toJson(v_pos_2102_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2113_);
v___x_2119_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2120_ = l_Lean_Option_toJson___redArg(v___x_2109_, v_endPos_2103_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2113_);
v___x_2123_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2124_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2124_, 0, v_keepFullRange_2104_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2113_);
v___x_2127_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2128_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2105_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2113_);
v___x_2131_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2132_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2132_, 0, v_isSilent_2106_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2113_);
v___x_2135_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_caption_2107_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_2113_);
v___x_2139_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2140_ = lean_apply_1(v_inst_2099_, v_data_2108_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2113_);
v___x_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2113_);
v___x_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2138_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2134_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2130_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2126_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2122_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2118_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2114_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2152_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2153_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2151_, v___x_2150_, v___x_2152_);
v___x_2154_ = l_Lean_Json_mkObj(v___x_2153_);
lean_dec(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2155_, lean_object* v_inst_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2160_, 0, lean_box(0));
lean_closure_set(v___x_2160_, 1, v_inst_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2161_, lean_object* v_inst_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2163_, 0, lean_box(0));
lean_closure_set(v___x_2163_, 1, v_inst_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = 1;
v___x_2170_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2170_, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2174_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2175_ = lean_string_append(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = 1;
v___x_2179_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2182_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2183_ = lean_string_append(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2186_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2187_ = lean_string_append(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = 1;
v___x_2194_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2197_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2198_ = lean_string_append(v___x_2197_, v___x_2196_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2200_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2201_ = lean_string_append(v___x_2200_, v___x_2199_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = 1;
v___x_2205_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2208_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2209_ = lean_string_append(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2211_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2212_ = lean_string_append(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = 1;
v___x_2217_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2220_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2221_ = lean_string_append(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2223_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2224_ = lean_string_append(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = 1;
v___x_2228_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2231_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2232_ = lean_string_append(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2234_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2235_ = lean_string_append(v___x_2234_, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = 1;
v___x_2239_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2239_, v___x_2238_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2242_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2243_ = lean_string_append(v___x_2242_, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2245_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2246_ = lean_string_append(v___x_2245_, v___x_2244_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = 1;
v___x_2250_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2250_, v___x_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2253_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2254_ = lean_string_append(v___x_2253_, v___x_2252_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2256_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2257_ = lean_string_append(v___x_2256_, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = 1;
v___x_2261_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2261_, v___x_2260_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2264_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2265_ = lean_string_append(v___x_2264_, v___x_2263_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2267_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2268_ = lean_string_append(v___x_2267_, v___x_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2269_, lean_object* v_json_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2272_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2270_);
v___x_2273_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2271_, v___x_2272_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2283_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2283_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2278_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2279_ = lean_string_append(v___x_2278_, v_a_2274_);
lean_dec(v_a_2274_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2279_);
v___x_2281_ = v___x_2276_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
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
lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2284_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2285_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2286_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2287_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2270_);
v___x_2288_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2285_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
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
v___x_2293_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
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
lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_a_2299_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2300_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2270_);
v___x_2301_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2286_, v___x_2300_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2307_ = lean_string_append(v___x_2306_, v_a_2302_);
lean_dec(v_a_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_a_2312_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2313_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2314_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2270_);
v___x_2315_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2313_, v___x_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2312_);
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2325_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2325_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2320_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2321_ = lean_string_append(v___x_2320_, v_a_2316_);
lean_dec(v_a_2316_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2321_);
v___x_2323_ = v___x_2318_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2326_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2327_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2328_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2270_);
v___x_2329_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2327_, v___x_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2326_);
lean_dec(v_a_2312_);
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
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
v___x_2334_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
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
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2341_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2270_);
v___x_2342_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2313_, v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2340_);
lean_dec(v_a_2326_);
lean_dec(v_a_2312_);
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
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
v___x_2347_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
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
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2354_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2270_);
v___x_2355_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v___x_2271_, v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2353_);
lean_dec(v_a_2340_);
lean_dec(v_a_2326_);
lean_dec(v_a_2312_);
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
lean_dec(v_json_2270_);
lean_dec_ref(v_inst_2269_);
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
v___x_2360_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
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
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2366_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2368_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2270_, v_inst_2269_, v___x_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_a_2366_);
lean_dec(v_a_2353_);
lean_dec(v_a_2340_);
lean_dec(v_a_2326_);
lean_dec(v_a_2312_);
lean_dec(v_a_2299_);
lean_dec(v_a_2284_);
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2373_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2374_ = lean_string_append(v___x_2373_, v_a_2369_);
lean_dec(v_a_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2374_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2390_; 
v_a_2379_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2381_ = v___x_2368_;
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2368_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; uint8_t v___x_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2388_; 
v___x_2383_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2383_, 0, v_a_2284_);
lean_ctor_set(v___x_2383_, 1, v_a_2299_);
lean_ctor_set(v___x_2383_, 2, v_a_2312_);
lean_ctor_set(v___x_2383_, 3, v_a_2366_);
lean_ctor_set(v___x_2383_, 4, v_a_2379_);
v___x_2384_ = lean_unbox(v_a_2326_);
lean_dec(v_a_2326_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*5, v___x_2384_);
v___x_2385_ = lean_unbox(v_a_2340_);
lean_dec(v_a_2340_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*5 + 1, v___x_2385_);
v___x_2386_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*5 + 2, v___x_2386_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2388_ = v___x_2381_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2391_, lean_object* v_inst_2392_, lean_object* v_json_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2392_, v_json_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2396_, 0, lean_box(0));
lean_closure_set(v___x_2396_, 1, v_inst_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2397_, lean_object* v_inst_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2399_, 0, lean_box(0));
lean_closure_set(v___x_2399_, 1, v_inst_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
else
{
lean_object* v_val_2402_; lean_object* v___x_2403_; 
v_val_2402_ = lean_ctor_get(v_x_2400_, 0);
lean_inc(v_val_2402_);
lean_dec_ref_known(v_x_2400_, 1);
v___x_2403_ = l_Lean_instToJsonPosition_toJson(v_val_2402_);
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
if (lean_obj_tag(v_a_2404_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_array_to_list(v_a_2405_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v___x_2409_; 
v_head_2407_ = lean_ctor_get(v_a_2404_, 0);
lean_inc(v_head_2407_);
v_tail_2408_ = lean_ctor_get(v_a_2404_, 1);
lean_inc(v_tail_2408_);
lean_dec_ref_known(v_a_2404_, 2);
v___x_2409_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2405_, v_head_2407_);
v_a_2404_ = v_tail_2408_;
v_a_2405_ = v___x_2409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2412_){
_start:
{
lean_object* v_toBaseMessage_2413_; lean_object* v_kind_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2479_; 
v_toBaseMessage_2413_ = lean_ctor_get(v_x_2412_, 0);
v_kind_2414_ = lean_ctor_get(v_x_2412_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2416_ = v_x_2412_;
v_isShared_2417_ = v_isSharedCheck_2479_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_kind_2414_);
lean_inc(v_toBaseMessage_2413_);
lean_dec(v_x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2479_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_fileName_2418_; lean_object* v_pos_2419_; lean_object* v_endPos_2420_; uint8_t v_keepFullRange_2421_; uint8_t v_severity_2422_; uint8_t v_isSilent_2423_; lean_object* v_caption_2424_; lean_object* v_data_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v_fileName_2418_ = lean_ctor_get(v_toBaseMessage_2413_, 0);
lean_inc_ref(v_fileName_2418_);
v_pos_2419_ = lean_ctor_get(v_toBaseMessage_2413_, 1);
lean_inc_ref(v_pos_2419_);
v_endPos_2420_ = lean_ctor_get(v_toBaseMessage_2413_, 2);
lean_inc(v_endPos_2420_);
v_keepFullRange_2421_ = lean_ctor_get_uint8(v_toBaseMessage_2413_, sizeof(void*)*5);
v_severity_2422_ = lean_ctor_get_uint8(v_toBaseMessage_2413_, sizeof(void*)*5 + 1);
v_isSilent_2423_ = lean_ctor_get_uint8(v_toBaseMessage_2413_, sizeof(void*)*5 + 2);
v_caption_2424_ = lean_ctor_get(v_toBaseMessage_2413_, 3);
lean_inc_ref(v_caption_2424_);
v_data_2425_ = lean_ctor_get(v_toBaseMessage_2413_, 4);
lean_inc(v_data_2425_);
lean_dec_ref(v_toBaseMessage_2413_);
v___x_2426_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_fileName_2418_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2427_);
lean_ctor_set(v___x_2416_, 0, v___x_2426_);
v___x_2429_ = v___x_2416_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2433_ = l_Lean_instToJsonPosition_toJson(v_pos_2419_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___x_2430_);
v___x_2436_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2437_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2420_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2430_);
v___x_2440_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2441_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2441_, 0, v_keepFullRange_2421_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2430_);
v___x_2444_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2445_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2422_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v___x_2430_);
v___x_2448_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2449_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2449_, 0, v_isSilent_2423_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v___x_2430_);
v___x_2452_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_caption_2424_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___x_2430_);
v___x_2456_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_data_2425_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2430_);
v___x_2460_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2461_ = 1;
v___x_2462_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2414_, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2460_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v___x_2430_);
v___x_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2430_);
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2459_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2455_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2451_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2447_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2443_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2439_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2435_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2431_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2476_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2474_, v___x_2475_);
v___x_2477_ = l_Lean_Json_mkObj(v___x_2476_);
lean_dec(v___x_2476_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2482_, lean_object* v_k_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = l_Lean_Json_getObjValD(v_j_2482_, v_k_2483_);
v___x_2485_ = l_Lean_Json_getStr_x3f(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2486_, lean_object* v_k_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2486_, v_k_2487_);
lean_dec_ref(v_k_2487_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2489_, lean_object* v_k_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = l_Lean_Json_getObjValD(v_j_2489_, v_k_2490_);
v___x_2492_ = l_Lean_instFromJsonPosition_fromJson(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2493_, lean_object* v_k_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2493_, v_k_2494_);
lean_dec_ref(v_k_2494_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2496_, lean_object* v_k_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = l_Lean_Json_getObjValD(v_j_2496_, v_k_2497_);
v___x_2499_ = l_Lean_Json_getBool_x3f(v___x_2498_);
lean_dec(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2500_, lean_object* v_k_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2500_, v_k_2501_);
lean_dec_ref(v_k_2501_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2503_, lean_object* v_k_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = l_Lean_Json_getObjValD(v_j_2503_, v_k_2504_);
v___x_2506_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2507_, lean_object* v_k_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2507_, v_k_2508_);
lean_dec_ref(v_k_2508_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2510_, lean_object* v_k_2511_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = l_Lean_Json_getObjValD(v_j_2510_, v_k_2511_);
v___x_2513_ = l_Lean_Name_fromJson_x3f(v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2514_, lean_object* v_k_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2514_, v_k_2515_);
lean_dec_ref(v_k_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_instFromJsonPosition_fromJson(v_x_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2538_; 
v_a_2530_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2532_ = v___x_2521_;
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2521_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_a_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2539_, lean_object* v_k_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = l_Lean_Json_getObjValD(v_j_2539_, v_k_2540_);
v___x_2542_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2543_, lean_object* v_k_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2543_, v_k_2544_);
lean_dec_ref(v_k_2544_);
return v_res_2545_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = 1;
v___x_2551_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2551_, v___x_2550_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2554_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2555_ = lean_string_append(v___x_2554_, v___x_2553_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2557_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2558_ = lean_string_append(v___x_2557_, v___x_2556_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2560_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2561_ = lean_string_append(v___x_2560_, v___x_2559_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2563_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2564_ = lean_string_append(v___x_2563_, v___x_2562_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2566_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2567_ = lean_string_append(v___x_2566_, v___x_2565_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2569_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2570_ = lean_string_append(v___x_2569_, v___x_2568_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2572_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2573_ = lean_string_append(v___x_2572_, v___x_2571_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2575_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2576_ = lean_string_append(v___x_2575_, v___x_2574_);
return v___x_2576_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2578_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2579_ = lean_string_append(v___x_2578_, v___x_2577_);
return v___x_2579_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2581_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2582_ = lean_string_append(v___x_2581_, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2584_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2585_ = lean_string_append(v___x_2584_, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2587_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2588_ = lean_string_append(v___x_2587_, v___x_2586_);
return v___x_2588_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2590_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2591_ = lean_string_append(v___x_2590_, v___x_2589_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2593_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2594_ = lean_string_append(v___x_2593_, v___x_2592_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2596_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2597_ = lean_string_append(v___x_2596_, v___x_2595_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2599_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2600_ = lean_string_append(v___x_2599_, v___x_2598_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2602_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2603_ = lean_string_append(v___x_2602_, v___x_2601_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = 1;
v___x_2607_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2608_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2610_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2611_ = lean_string_append(v___x_2610_, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2613_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2614_ = lean_string_append(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2615_);
v___x_2617_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2615_, v___x_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_json_2615_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2623_ = lean_string_append(v___x_2622_, v_a_2618_);
lean_dec(v_a_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2623_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_a_2628_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2629_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2615_);
v___x_2630_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2615_, v___x_2629_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2640_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2640_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2635_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2636_ = lean_string_append(v___x_2635_, v_a_2631_);
lean_dec(v_a_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2636_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2642_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2615_);
v___x_2643_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2615_, v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2649_ = lean_string_append(v___x_2648_, v_a_2644_);
lean_dec(v_a_2644_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2655_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2615_);
v___x_2656_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2615_, v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2666_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2666_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2661_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2662_ = lean_string_append(v___x_2661_, v_a_2657_);
lean_dec(v_a_2657_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2662_);
v___x_2664_ = v___x_2659_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2668_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2615_);
v___x_2669_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2615_, v___x_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_a_2667_);
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2675_ = lean_string_append(v___x_2674_, v_a_2670_);
lean_dec(v_a_2670_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2675_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_a_2680_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2681_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2615_);
v___x_2682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2615_, v___x_2681_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_a_2680_);
lean_dec(v_a_2667_);
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2688_ = lean_string_append(v___x_2687_, v_a_2683_);
lean_dec(v_a_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2688_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_a_2693_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2694_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2615_);
v___x_2695_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2615_, v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_a_2693_);
lean_dec(v_a_2680_);
lean_dec(v_a_2667_);
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
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
v___x_2700_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
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
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_a_2706_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2707_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2615_);
v___x_2708_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2615_, v___x_2707_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_a_2706_);
lean_dec(v_a_2693_);
lean_dec(v_a_2680_);
lean_dec(v_a_2667_);
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
lean_dec(v_json_2615_);
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2714_ = lean_string_append(v___x_2713_, v_a_2709_);
lean_dec(v_a_2709_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_a_2719_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2720_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2721_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2615_, v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_a_2719_);
lean_dec(v_a_2706_);
lean_dec(v_a_2693_);
lean_dec(v_a_2680_);
lean_dec(v_a_2667_);
lean_dec(v_a_2654_);
lean_dec(v_a_2641_);
lean_dec(v_a_2628_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2727_ = lean_string_append(v___x_2726_, v_a_2722_);
lean_dec(v_a_2722_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2727_);
v___x_2729_ = v___x_2724_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
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
v_a_2732_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2734_ = v___x_2721_;
v_isShared_2735_ = v_isSharedCheck_2744_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2721_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2744_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; uint8_t v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2736_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2736_, 0, v_a_2628_);
lean_ctor_set(v___x_2736_, 1, v_a_2641_);
lean_ctor_set(v___x_2736_, 2, v_a_2654_);
lean_ctor_set(v___x_2736_, 3, v_a_2706_);
lean_ctor_set(v___x_2736_, 4, v_a_2719_);
v___x_2737_ = lean_unbox(v_a_2667_);
lean_dec(v_a_2667_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*5, v___x_2737_);
v___x_2738_ = lean_unbox(v_a_2680_);
lean_dec(v_a_2680_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*5 + 1, v___x_2738_);
v___x_2739_ = lean_unbox(v_a_2693_);
lean_dec(v_a_2693_);
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
lean_object* v_pre_2758_; lean_object* v_str_2759_; lean_object* v_p_x27_2760_; uint8_t v___x_2761_; 
v_pre_2758_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_pre_2758_);
v_str_2759_ = lean_ctor_get(v_a_2757_, 1);
lean_inc_ref(v_str_2759_);
lean_dec_ref_known(v_a_2757_, 2);
v_p_x27_2760_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2758_);
v___x_2761_ = l_Lean_Name_isAnonymous(v_p_x27_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Name_str___override(v_p_x27_2760_, v_str_2759_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2764_ = lean_string_dec_eq(v_str_2759_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Name_str___override(v_p_x27_2760_, v_str_2759_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_p_x27_2760_);
lean_dec_ref(v_str_2759_);
v___x_2766_ = lean_box(0);
return v___x_2766_;
}
}
}
default: 
{
lean_object* v_pre_2767_; lean_object* v_i_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_pre_2767_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_pre_2767_);
v_i_2768_ = lean_ctor_get(v_a_2757_, 1);
lean_inc(v_i_2768_);
lean_dec_ref_known(v_a_2757_, 2);
v___x_2769_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2767_);
v___x_2770_ = l_Lean_Name_num___override(v___x_2769_, v_i_2768_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2771_){
_start:
{
switch(lean_obj_tag(v_x_2771_))
{
case 3:
{
lean_object* v_a_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2781_; 
v_a_2772_ = lean_ctor_get(v_x_2771_, 0);
v_a_2773_ = lean_ctor_get(v_x_2771_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2775_ = v_x_2771_;
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_inc(v_a_2772_);
lean_dec(v_x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = l_Lean_MessageData_stripNestedTags(v_a_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v___x_2777_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2772_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
case 4:
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2791_; 
v_a_2782_ = lean_ctor_get(v_x_2771_, 0);
v_a_2783_ = lean_ctor_get(v_x_2771_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2785_ = v_x_2771_;
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_inc(v_a_2782_);
lean_dec(v_x_2771_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = l_Lean_MessageData_stripNestedTags(v_a_2783_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2787_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
case 8:
{
lean_object* v_a_2792_; lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2801_; 
v_a_2792_ = lean_ctor_get(v_x_2771_, 0);
v_a_2793_ = lean_ctor_get(v_x_2771_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2795_ = v_x_2771_;
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_inc(v_a_2792_);
lean_dec(v_x_2771_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2792_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_a_2793_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
case 11:
{
lean_object* v_a_2802_; lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2811_; 
v_a_2802_ = lean_ctor_get(v_x_2771_, 0);
v_a_2803_ = lean_ctor_get(v_x_2771_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2805_ = v_x_2771_;
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_inc(v_a_2802_);
lean_dec(v_x_2771_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = l_Lean_MessageData_stripNestedTags(v_a_2803_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2802_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
default: 
{
return v_x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2812_){
_start:
{
if (lean_obj_tag(v_x_2812_) == 1)
{
lean_object* v_pre_2813_; lean_object* v_str_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_pre_2813_ = lean_ctor_get(v_x_2812_, 0);
v_str_2814_ = lean_ctor_get(v_x_2812_, 1);
v___x_2815_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2816_ = lean_string_dec_eq(v_str_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_box(0);
return v___x_2817_;
}
else
{
lean_object* v___x_2818_; 
lean_inc(v_pre_2813_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_pre_2813_);
return v___x_2818_;
}
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_box(0);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_errorNameOfKind_x3f(v_x_2820_);
lean_dec(v_x_2820_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = l_Lean_MessageData_kind(v_msg_2822_);
v___x_2824_ = l_Lean_errorNameOfKind_x3f(v___x_2823_);
lean_dec(v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_MessageData_errorName_x3f(v_msg_2825_);
lean_dec_ref(v_msg_2825_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2827_){
_start:
{
lean_object* v_data_2828_; lean_object* v___x_2829_; 
v_data_2828_ = lean_ctor_get(v_msg_2827_, 4);
v___x_2829_ = l_Lean_MessageData_errorName_x3f(v_data_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_Message_errorName_x3f(v_msg_2830_);
lean_dec_ref(v_msg_2830_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2832_){
_start:
{
lean_object* v_toBaseMessage_2833_; lean_object* v_fileName_2834_; lean_object* v_pos_2835_; lean_object* v_endPos_2836_; uint8_t v_keepFullRange_2837_; uint8_t v_severity_2838_; uint8_t v_isSilent_2839_; lean_object* v_caption_2840_; lean_object* v_data_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2850_; 
v_toBaseMessage_2833_ = lean_ctor_get(v_msg_2832_, 0);
lean_inc_ref(v_toBaseMessage_2833_);
lean_dec_ref(v_msg_2832_);
v_fileName_2834_ = lean_ctor_get(v_toBaseMessage_2833_, 0);
v_pos_2835_ = lean_ctor_get(v_toBaseMessage_2833_, 1);
v_endPos_2836_ = lean_ctor_get(v_toBaseMessage_2833_, 2);
v_keepFullRange_2837_ = lean_ctor_get_uint8(v_toBaseMessage_2833_, sizeof(void*)*5);
v_severity_2838_ = lean_ctor_get_uint8(v_toBaseMessage_2833_, sizeof(void*)*5 + 1);
v_isSilent_2839_ = lean_ctor_get_uint8(v_toBaseMessage_2833_, sizeof(void*)*5 + 2);
v_caption_2840_ = lean_ctor_get(v_toBaseMessage_2833_, 3);
v_data_2841_ = lean_ctor_get(v_toBaseMessage_2833_, 4);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_toBaseMessage_2833_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2843_ = v_toBaseMessage_2833_;
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_data_2841_);
lean_inc(v_caption_2840_);
lean_inc(v_endPos_2836_);
lean_inc(v_pos_2835_);
lean_inc(v_fileName_2834_);
lean_dec(v_toBaseMessage_2833_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2850_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_data_2841_);
v___x_2846_ = l_Lean_MessageData_ofFormat(v___x_2845_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 4, v___x_2846_);
v___x_2848_ = v___x_2843_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_fileName_2834_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_pos_2835_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_endPos_2836_);
lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_caption_2840_);
lean_ctor_set(v_reuseFailAlloc_2849_, 4, v___x_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*5, v_keepFullRange_2837_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*5 + 1, v_severity_2838_);
lean_ctor_set_uint8(v_reuseFailAlloc_2849_, sizeof(void*)*5 + 2, v_isSilent_2839_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2856_, uint8_t v_includeEndPos_2857_){
_start:
{
lean_object* v___y_2859_; lean_object* v___y_2863_; uint32_t v___y_2864_; lean_object* v___y_2868_; lean_object* v_str_2871_; lean_object* v_toBaseMessage_2881_; lean_object* v_kind_2882_; lean_object* v_fileName_2883_; lean_object* v_pos_2884_; lean_object* v_endPos_2885_; uint8_t v_severity_2886_; lean_object* v_caption_2887_; lean_object* v_data_2888_; lean_object* v___y_2890_; lean_object* v_str_2891_; lean_object* v___y_2899_; 
v_toBaseMessage_2881_ = lean_ctor_get(v_msg_2856_, 0);
lean_inc_ref(v_toBaseMessage_2881_);
v_kind_2882_ = lean_ctor_get(v_msg_2856_, 1);
lean_inc(v_kind_2882_);
lean_dec_ref(v_msg_2856_);
v_fileName_2883_ = lean_ctor_get(v_toBaseMessage_2881_, 0);
lean_inc_ref(v_fileName_2883_);
v_pos_2884_ = lean_ctor_get(v_toBaseMessage_2881_, 1);
lean_inc_ref(v_pos_2884_);
v_endPos_2885_ = lean_ctor_get(v_toBaseMessage_2881_, 2);
lean_inc(v_endPos_2885_);
v_severity_2886_ = lean_ctor_get_uint8(v_toBaseMessage_2881_, sizeof(void*)*5 + 1);
v_caption_2887_ = lean_ctor_get(v_toBaseMessage_2881_, 3);
lean_inc_ref(v_caption_2887_);
v_data_2888_ = lean_ctor_get(v_toBaseMessage_2881_, 4);
lean_inc(v_data_2888_);
lean_dec_ref(v_toBaseMessage_2881_);
if (v_includeEndPos_2857_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_endPos_2885_);
v___x_2905_ = lean_box(0);
v___y_2899_ = v___x_2905_;
goto v___jp_2898_;
}
else
{
v___y_2899_ = v_endPos_2885_;
goto v___jp_2898_;
}
v___jp_2858_:
{
lean_object* v___x_2860_; lean_object* v_str_2861_; 
v___x_2860_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v_str_2861_ = lean_string_append(v___y_2859_, v___x_2860_);
return v_str_2861_;
}
v___jp_2862_:
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 10;
v___x_2866_ = lean_uint32_dec_eq(v___y_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
v___y_2859_ = v___y_2863_;
goto v___jp_2858_;
}
else
{
return v___y_2863_;
}
}
v___jp_2867_:
{
uint32_t v___x_2869_; 
v___x_2869_ = 65;
v___y_2863_ = v___y_2868_;
v___y_2864_ = v___x_2869_;
goto v___jp_2862_;
}
v___jp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = lean_string_utf8_byte_size(v_str_2871_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_nat_dec_eq(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_inc_ref(v_str_2871_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v_str_2871_);
lean_ctor_set(v___x_2875_, 1, v___x_2873_);
lean_ctor_set(v___x_2875_, 2, v___x_2872_);
v___x_2876_ = l_String_Slice_Pos_prev_x3f(v___x_2875_, v___x_2872_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_dec_ref_known(v___x_2875_, 3);
v___y_2868_ = v_str_2871_;
goto v___jp_2867_;
}
else
{
lean_object* v_val_2877_; lean_object* v___x_2878_; 
v_val_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = l_String_Slice_Pos_get_x3f(v___x_2875_, v_val_2877_);
lean_dec(v_val_2877_);
lean_dec_ref_known(v___x_2875_, 3);
if (lean_obj_tag(v___x_2878_) == 0)
{
v___y_2868_ = v_str_2871_;
goto v___jp_2867_;
}
else
{
lean_object* v_val_2879_; uint32_t v___x_2880_; 
v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = lean_unbox_uint32(v_val_2879_);
lean_dec(v_val_2879_);
v___y_2863_ = v_str_2871_;
v___y_2864_ = v___x_2880_;
goto v___jp_2862_;
}
}
}
else
{
v___y_2859_ = v_str_2871_;
goto v___jp_2858_;
}
}
v___jp_2889_:
{
switch(v_severity_2886_)
{
case 0:
{
lean_dec(v___y_2890_);
lean_dec_ref(v_pos_2884_);
lean_dec_ref(v_fileName_2883_);
lean_dec(v_kind_2882_);
v_str_2871_ = v_str_2891_;
goto v___jp_2870_;
}
case 1:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_str_2894_; 
v___x_2892_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2893_ = l_Lean_errorNameOfKind_x3f(v_kind_2882_);
lean_dec(v_kind_2882_);
v_str_2894_ = l_Lean_mkErrorStringWithPos(v_fileName_2883_, v_pos_2884_, v_str_2891_, v___y_2890_, v___x_2892_, v___x_2893_);
lean_dec_ref(v_str_2891_);
v_str_2871_ = v_str_2894_;
goto v___jp_2870_;
}
default: 
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_str_2897_; 
v___x_2895_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2896_ = l_Lean_errorNameOfKind_x3f(v_kind_2882_);
lean_dec(v_kind_2882_);
v_str_2897_ = l_Lean_mkErrorStringWithPos(v_fileName_2883_, v_pos_2884_, v_str_2891_, v___y_2890_, v___x_2895_, v___x_2896_);
lean_dec_ref(v_str_2891_);
v_str_2871_ = v_str_2897_;
goto v___jp_2870_;
}
}
}
v___jp_2898_:
{
lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2900_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2901_ = lean_string_dec_eq(v_caption_2887_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v_str_2904_; 
v___x_2902_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2903_ = lean_string_append(v_caption_2887_, v___x_2902_);
v_str_2904_ = lean_string_append(v___x_2903_, v_data_2888_);
lean_dec(v_data_2888_);
v___y_2890_ = v___y_2899_;
v_str_2891_ = v_str_2904_;
goto v___jp_2889_;
}
else
{
lean_dec_ref(v_caption_2887_);
v___y_2890_ = v___y_2899_;
v_str_2891_ = v_data_2888_;
goto v___jp_2889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2906_, lean_object* v_includeEndPos_2907_){
_start:
{
uint8_t v_includeEndPos_boxed_2908_; lean_object* v_res_2909_; 
v_includeEndPos_boxed_2908_ = lean_unbox(v_includeEndPos_2907_);
v_res_2909_ = l_Lean_SerialMessage_toString(v_msg_2906_, v_includeEndPos_boxed_2908_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2910_){
_start:
{
uint8_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = 0;
v___x_2912_ = l_Lean_SerialMessage_toString(v_msg_2910_, v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2915_){
_start:
{
lean_object* v_data_2916_; lean_object* v___x_2917_; 
v_data_2916_ = lean_ctor_get(v_msg_2915_, 4);
v___x_2917_ = l_Lean_MessageData_kind(v_data_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Message_kind(v_msg_2918_);
lean_dec_ref(v_msg_2918_);
return v_res_2919_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2920_){
_start:
{
lean_object* v_data_2921_; uint8_t v___x_2922_; 
v_data_2921_ = lean_ctor_get(v_msg_2920_, 4);
v___x_2922_ = l_Lean_MessageData_isTrace(v_data_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2923_){
_start:
{
uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_res_2924_ = l_Lean_Message_isTrace(v_msg_2923_);
lean_dec_ref(v_msg_2923_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2926_){
_start:
{
lean_object* v_fileName_2928_; lean_object* v_pos_2929_; lean_object* v_endPos_2930_; uint8_t v_keepFullRange_2931_; uint8_t v_severity_2932_; uint8_t v_isSilent_2933_; lean_object* v_caption_2934_; lean_object* v_data_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2945_; 
v_fileName_2928_ = lean_ctor_get(v_msg_2926_, 0);
v_pos_2929_ = lean_ctor_get(v_msg_2926_, 1);
v_endPos_2930_ = lean_ctor_get(v_msg_2926_, 2);
v_keepFullRange_2931_ = lean_ctor_get_uint8(v_msg_2926_, sizeof(void*)*5);
v_severity_2932_ = lean_ctor_get_uint8(v_msg_2926_, sizeof(void*)*5 + 1);
v_isSilent_2933_ = lean_ctor_get_uint8(v_msg_2926_, sizeof(void*)*5 + 2);
v_caption_2934_ = lean_ctor_get(v_msg_2926_, 3);
v_data_2935_ = lean_ctor_get(v_msg_2926_, 4);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_msg_2926_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2937_ = v_msg_2926_;
v_isShared_2938_ = v_isSharedCheck_2945_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_data_2935_);
lean_inc(v_caption_2934_);
lean_inc(v_endPos_2930_);
lean_inc(v_pos_2929_);
lean_inc(v_fileName_2928_);
lean_dec(v_msg_2926_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2945_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_inc(v_data_2935_);
v___x_2939_ = l_Lean_MessageData_toString(v_data_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 4, v___x_2939_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_fileName_2928_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_pos_2929_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_endPos_2930_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v_caption_2934_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v___x_2939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2944_, sizeof(void*)*5, v_keepFullRange_2931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2944_, sizeof(void*)*5 + 1, v_severity_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2944_, sizeof(void*)*5 + 2, v_isSilent_2933_);
v___x_2941_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = l_Lean_MessageData_kind(v_data_2935_);
lean_dec(v_data_2935_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
return v___x_2943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Message_serialize(v_msg_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2949_, uint8_t v_includeEndPos_2950_){
_start:
{
lean_object* v_fileName_2952_; lean_object* v_pos_2953_; lean_object* v_endPos_2954_; uint8_t v_severity_2955_; lean_object* v_caption_2956_; lean_object* v_data_2957_; lean_object* v___x_2958_; lean_object* v___y_2960_; lean_object* v___y_2964_; uint32_t v___y_2965_; lean_object* v___y_2969_; lean_object* v_str_2972_; lean_object* v___x_2982_; lean_object* v___y_2984_; lean_object* v_str_2985_; lean_object* v___y_2993_; 
v_fileName_2952_ = lean_ctor_get(v_msg_2949_, 0);
lean_inc_ref(v_fileName_2952_);
v_pos_2953_ = lean_ctor_get(v_msg_2949_, 1);
lean_inc_ref(v_pos_2953_);
v_endPos_2954_ = lean_ctor_get(v_msg_2949_, 2);
lean_inc(v_endPos_2954_);
v_severity_2955_ = lean_ctor_get_uint8(v_msg_2949_, sizeof(void*)*5 + 1);
v_caption_2956_ = lean_ctor_get(v_msg_2949_, 3);
lean_inc_ref(v_caption_2956_);
v_data_2957_ = lean_ctor_get(v_msg_2949_, 4);
lean_inc_n(v_data_2957_, 2);
lean_dec_ref(v_msg_2949_);
v___x_2958_ = l_Lean_MessageData_toString(v_data_2957_);
v___x_2982_ = l_Lean_MessageData_kind(v_data_2957_);
lean_dec(v_data_2957_);
if (v_includeEndPos_2950_ == 0)
{
lean_object* v___x_2999_; 
lean_dec(v_endPos_2954_);
v___x_2999_ = lean_box(0);
v___y_2993_ = v___x_2999_;
goto v___jp_2992_;
}
else
{
v___y_2993_ = v_endPos_2954_;
goto v___jp_2992_;
}
v___jp_2959_:
{
lean_object* v___x_2961_; lean_object* v_str_2962_; 
v___x_2961_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v_str_2962_ = lean_string_append(v___y_2960_, v___x_2961_);
return v_str_2962_;
}
v___jp_2963_:
{
uint32_t v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = 10;
v___x_2967_ = lean_uint32_dec_eq(v___y_2965_, v___x_2966_);
if (v___x_2967_ == 0)
{
v___y_2960_ = v___y_2964_;
goto v___jp_2959_;
}
else
{
return v___y_2964_;
}
}
v___jp_2968_:
{
uint32_t v___x_2970_; 
v___x_2970_ = 65;
v___y_2964_ = v___y_2969_;
v___y_2965_ = v___x_2970_;
goto v___jp_2963_;
}
v___jp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2973_ = lean_string_utf8_byte_size(v_str_2972_);
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = lean_nat_dec_eq(v___x_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_inc_ref(v_str_2972_);
v___x_2976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2976_, 0, v_str_2972_);
lean_ctor_set(v___x_2976_, 1, v___x_2974_);
lean_ctor_set(v___x_2976_, 2, v___x_2973_);
v___x_2977_ = l_String_Slice_Pos_prev_x3f(v___x_2976_, v___x_2973_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_dec_ref_known(v___x_2976_, 3);
v___y_2969_ = v_str_2972_;
goto v___jp_2968_;
}
else
{
lean_object* v_val_2978_; lean_object* v___x_2979_; 
v_val_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_val_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = l_String_Slice_Pos_get_x3f(v___x_2976_, v_val_2978_);
lean_dec(v_val_2978_);
lean_dec_ref_known(v___x_2976_, 3);
if (lean_obj_tag(v___x_2979_) == 0)
{
v___y_2969_ = v_str_2972_;
goto v___jp_2968_;
}
else
{
lean_object* v_val_2980_; uint32_t v___x_2981_; 
v_val_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_val_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = lean_unbox_uint32(v_val_2980_);
lean_dec(v_val_2980_);
v___y_2964_ = v_str_2972_;
v___y_2965_ = v___x_2981_;
goto v___jp_2963_;
}
}
}
else
{
v___y_2960_ = v_str_2972_;
goto v___jp_2959_;
}
}
v___jp_2983_:
{
switch(v_severity_2955_)
{
case 0:
{
lean_dec(v___y_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_pos_2953_);
lean_dec_ref(v_fileName_2952_);
v_str_2972_ = v_str_2985_;
goto v___jp_2971_;
}
case 1:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v_str_2988_; 
v___x_2986_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2987_ = l_Lean_errorNameOfKind_x3f(v___x_2982_);
lean_dec(v___x_2982_);
v_str_2988_ = l_Lean_mkErrorStringWithPos(v_fileName_2952_, v_pos_2953_, v_str_2985_, v___y_2984_, v___x_2986_, v___x_2987_);
lean_dec_ref(v_str_2985_);
v_str_2972_ = v_str_2988_;
goto v___jp_2971_;
}
default: 
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_str_2991_; 
v___x_2989_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2990_ = l_Lean_errorNameOfKind_x3f(v___x_2982_);
lean_dec(v___x_2982_);
v_str_2991_ = l_Lean_mkErrorStringWithPos(v_fileName_2952_, v_pos_2953_, v_str_2985_, v___y_2984_, v___x_2989_, v___x_2990_);
lean_dec_ref(v_str_2985_);
v_str_2972_ = v_str_2991_;
goto v___jp_2971_;
}
}
}
v___jp_2992_:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2995_ = lean_string_dec_eq(v_caption_2956_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_str_2998_; 
v___x_2996_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2997_ = lean_string_append(v_caption_2956_, v___x_2996_);
v_str_2998_ = lean_string_append(v___x_2997_, v___x_2958_);
lean_dec_ref(v___x_2958_);
v___y_2984_ = v___y_2993_;
v_str_2985_ = v_str_2998_;
goto v___jp_2983_;
}
else
{
lean_dec_ref(v_caption_2956_);
v___y_2984_ = v___y_2993_;
v_str_2985_ = v___x_2958_;
goto v___jp_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3000_, lean_object* v_includeEndPos_3001_, lean_object* v_a_3002_){
_start:
{
uint8_t v_includeEndPos_boxed_3003_; lean_object* v_res_3004_; 
v_includeEndPos_boxed_3003_ = lean_unbox(v_includeEndPos_3001_);
v_res_3004_ = l_Lean_Message_toString(v_msg_3000_, v_includeEndPos_boxed_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_3005_){
_start:
{
lean_object* v_fileName_3007_; lean_object* v_pos_3008_; lean_object* v_endPos_3009_; uint8_t v_keepFullRange_3010_; uint8_t v_severity_3011_; uint8_t v_isSilent_3012_; lean_object* v_caption_3013_; lean_object* v_data_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_fileName_3007_ = lean_ctor_get(v_msg_3005_, 0);
lean_inc_ref(v_fileName_3007_);
v_pos_3008_ = lean_ctor_get(v_msg_3005_, 1);
lean_inc_ref(v_pos_3008_);
v_endPos_3009_ = lean_ctor_get(v_msg_3005_, 2);
lean_inc(v_endPos_3009_);
v_keepFullRange_3010_ = lean_ctor_get_uint8(v_msg_3005_, sizeof(void*)*5);
v_severity_3011_ = lean_ctor_get_uint8(v_msg_3005_, sizeof(void*)*5 + 1);
v_isSilent_3012_ = lean_ctor_get_uint8(v_msg_3005_, sizeof(void*)*5 + 2);
v_caption_3013_ = lean_ctor_get(v_msg_3005_, 3);
lean_inc_ref(v_caption_3013_);
v_data_3014_ = lean_ctor_get(v_msg_3005_, 4);
lean_inc_n(v_data_3014_, 2);
lean_dec_ref(v_msg_3005_);
v___x_3015_ = l_Lean_MessageData_toString(v_data_3014_);
v___x_3016_ = l_Lean_MessageData_kind(v_data_3014_);
lean_dec(v_data_3014_);
v___x_3017_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_fileName_3007_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3023_ = l_Lean_instToJsonPosition_toJson(v_pos_3008_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3020_);
v___x_3026_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3027_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3009_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3020_);
v___x_3030_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3031_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3031_, 0, v_keepFullRange_3010_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3020_);
v___x_3034_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3035_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3011_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3020_);
v___x_3038_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3039_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3039_, 0, v_isSilent_3012_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3020_);
v___x_3042_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_caption_3013_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3020_);
v___x_3046_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3015_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3020_);
v___x_3050_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3051_ = 1;
v___x_3052_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3016_, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3020_);
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3020_);
v___x_3057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3049_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3045_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3041_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3037_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3033_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3029_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3025_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3021_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3066_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3064_, v___x_3065_);
v___x_3067_ = l_Lean_Json_mkObj(v___x_3066_);
lean_dec(v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Message_toJson(v_msg_3068_);
return v_res_3070_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_unsigned_to_nat(32u);
v___x_3072_ = lean_mk_empty_array_with_capacity(v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3074_ = ((size_t)5ULL);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_unsigned_to_nat(32u);
v___x_3077_ = lean_mk_empty_array_with_capacity(v___x_3076_);
v___x_3078_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
lean_ctor_set(v___x_3079_, 2, v___x_3075_);
lean_ctor_set(v___x_3079_, 3, v___x_3075_);
lean_ctor_set_usize(v___x_3079_, 4, v___x_3074_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = l_Lean_NameSet_empty;
v___x_3081_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
lean_ctor_set(v___x_3082_, 2, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3084_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_unsigned_to_nat(32u);
v___x_3086_ = lean_mk_empty_array_with_capacity(v___x_3085_);
lean_dec_ref(v___x_3086_);
v___x_3087_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3088_){
_start:
{
lean_object* v_unreported_3089_; 
v_unreported_3089_ = lean_ctor_get(v_self_3088_, 1);
lean_inc_ref(v_unreported_3089_);
return v_unreported_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_MessageLog_msgs(v_self_3090_);
lean_dec_ref(v_self_3090_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3092_){
_start:
{
lean_object* v_reported_3093_; lean_object* v_unreported_3094_; lean_object* v___x_3095_; 
v_reported_3093_ = lean_ctor_get(v_x_3092_, 0);
lean_inc_ref(v_reported_3093_);
v_unreported_3094_ = lean_ctor_get(v_x_3092_, 1);
lean_inc_ref(v_unreported_3094_);
lean_dec_ref(v_x_3092_);
v___x_3095_ = l_Lean_PersistentArray_append___redArg(v_reported_3093_, v_unreported_3094_);
lean_dec_ref(v_unreported_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3096_){
_start:
{
lean_object* v_unreported_3097_; uint8_t v___x_3098_; 
v_unreported_3097_ = lean_ctor_get(v_log_3096_, 1);
v___x_3098_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3097_);
if (v___x_3098_ == 0)
{
uint8_t v___x_3099_; 
v___x_3099_ = 1;
return v___x_3099_;
}
else
{
uint8_t v___x_3100_; 
v___x_3100_ = 0;
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3101_){
_start:
{
uint8_t v_res_3102_; lean_object* v_r_3103_; 
v_res_3102_ = l_Lean_MessageLog_hasUnreported(v_log_3101_);
lean_dec_ref(v_log_3101_);
v_r_3103_ = lean_box(v_res_3102_);
return v_r_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3104_, lean_object* v_log_3105_){
_start:
{
lean_object* v_reported_3106_; lean_object* v_unreported_3107_; lean_object* v_loggedKinds_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3116_; 
v_reported_3106_ = lean_ctor_get(v_log_3105_, 0);
v_unreported_3107_ = lean_ctor_get(v_log_3105_, 1);
v_loggedKinds_3108_ = lean_ctor_get(v_log_3105_, 2);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_log_3105_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3110_ = v_log_3105_;
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_loggedKinds_3108_);
lean_inc(v_unreported_3107_);
lean_inc(v_reported_3106_);
lean_dec(v_log_3105_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = l_Lean_PersistentArray_push___redArg(v_unreported_3107_, v_msg_3104_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v___x_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_reported_3106_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_loggedKinds_3108_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3119_, lean_object* v_x_3120_){
_start:
{
if (lean_obj_tag(v_x_3120_) == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_u2082_3119_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; 
v___x_3122_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3123_, v_x_3124_);
lean_dec(v_x_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3126_, lean_object* v_k_3127_, lean_object* v_t_3128_){
_start:
{
if (lean_obj_tag(v_t_3128_) == 0)
{
lean_object* v_size_3129_; lean_object* v_k_3130_; lean_object* v_v_3131_; lean_object* v_l_3132_; lean_object* v_r_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3148_; 
v_size_3129_ = lean_ctor_get(v_t_3128_, 0);
v_k_3130_ = lean_ctor_get(v_t_3128_, 1);
v_v_3131_ = lean_ctor_get(v_t_3128_, 2);
v_l_3132_ = lean_ctor_get(v_t_3128_, 3);
v_r_3133_ = lean_ctor_get(v_t_3128_, 4);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_t_3128_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3135_ = v_t_3128_;
v_isShared_3136_ = v_isSharedCheck_3148_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_r_3133_);
lean_inc(v_l_3132_);
lean_inc(v_v_3131_);
lean_inc(v_k_3130_);
lean_inc(v_size_3129_);
lean_dec(v_t_3128_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3148_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
uint8_t v___x_3137_; 
v___x_3137_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3127_, v_k_3130_);
switch(v___x_3137_)
{
case 0:
{
lean_object* v_impl_3138_; lean_object* v___x_3139_; 
lean_del_object(v___x_3135_);
lean_dec(v_size_3129_);
v_impl_3138_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3126_, v_k_3127_, v_l_3132_);
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3130_, v_v_3131_, v_impl_3138_, v_r_3133_);
return v___x_3139_;
}
case 1:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_val_3142_; lean_object* v___x_3144_; 
lean_dec(v_k_3130_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_v_3131_);
v___x_3141_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3126_, v___x_3140_);
lean_dec_ref_known(v___x_3140_, 1);
v_val_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_val_3142_);
lean_dec(v___x_3141_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 2, v_val_3142_);
lean_ctor_set(v___x_3135_, 1, v_k_3127_);
v___x_3144_ = v___x_3135_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_size_3129_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_k_3127_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_val_3142_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_l_3132_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_r_3133_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
default: 
{
lean_object* v_impl_3146_; lean_object* v___x_3147_; 
lean_del_object(v___x_3135_);
lean_dec(v_size_3129_);
v_impl_3146_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3126_, v_k_3127_, v_r_3133_);
v___x_3147_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3130_, v_v_3131_, v_l_3132_, v_impl_3146_);
return v___x_3147_;
}
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v_val_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_box(0);
v___x_3150_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3126_, v___x_3149_);
v_val_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_val_3151_);
lean_dec(v___x_3150_);
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v_k_3127_);
lean_ctor_set(v___x_3153_, 2, v_val_3151_);
lean_ctor_set(v___x_3153_, 3, v_t_3128_);
lean_ctor_set(v___x_3153_, 4, v_t_3128_);
return v___x_3153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3154_, lean_object* v_x_3155_){
_start:
{
if (lean_obj_tag(v_x_3155_) == 0)
{
lean_object* v_k_3156_; lean_object* v_v_3157_; lean_object* v_l_3158_; lean_object* v_r_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_k_3156_ = lean_ctor_get(v_x_3155_, 1);
lean_inc(v_k_3156_);
v_v_3157_ = lean_ctor_get(v_x_3155_, 2);
lean_inc(v_v_3157_);
v_l_3158_ = lean_ctor_get(v_x_3155_, 3);
lean_inc(v_l_3158_);
v_r_3159_ = lean_ctor_get(v_x_3155_, 4);
lean_inc(v_r_3159_);
lean_dec_ref_known(v_x_3155_, 5);
v___x_3160_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3154_, v_l_3158_);
v___x_3161_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3157_, v_k_3156_, v___x_3160_);
v_init_3154_ = v___x_3161_;
v_x_3155_ = v_r_3159_;
goto _start;
}
else
{
return v_init_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3163_, lean_object* v_l_u2082_3164_){
_start:
{
lean_object* v_reported_3165_; lean_object* v_unreported_3166_; lean_object* v_loggedKinds_3167_; lean_object* v_reported_3168_; lean_object* v_unreported_3169_; lean_object* v_loggedKinds_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3180_; 
v_reported_3165_ = lean_ctor_get(v_l_u2081_3163_, 0);
lean_inc_ref(v_reported_3165_);
v_unreported_3166_ = lean_ctor_get(v_l_u2081_3163_, 1);
lean_inc_ref(v_unreported_3166_);
v_loggedKinds_3167_ = lean_ctor_get(v_l_u2081_3163_, 2);
lean_inc(v_loggedKinds_3167_);
lean_dec_ref(v_l_u2081_3163_);
v_reported_3168_ = lean_ctor_get(v_l_u2082_3164_, 0);
v_unreported_3169_ = lean_ctor_get(v_l_u2082_3164_, 1);
v_loggedKinds_3170_ = lean_ctor_get(v_l_u2082_3164_, 2);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_l_u2082_3164_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3172_ = v_l_u2082_3164_;
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_loggedKinds_3170_);
lean_inc(v_unreported_3169_);
lean_inc(v_reported_3168_);
lean_dec(v_l_u2082_3164_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3174_ = l_Lean_PersistentArray_append___redArg(v_reported_3165_, v_reported_3168_);
lean_dec_ref(v_reported_3168_);
v___x_3175_ = l_Lean_PersistentArray_append___redArg(v_unreported_3166_, v_unreported_3169_);
lean_dec_ref(v_unreported_3169_);
v___x_3176_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3167_, v_loggedKinds_3170_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 2, v___x_3176_);
lean_ctor_set(v___x_3172_, 1, v___x_3175_);
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3178_ = v___x_3172_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3181_, lean_object* v_k_3182_, lean_object* v_t_3183_, lean_object* v_hl_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3181_, v_k_3182_, v_t_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3186_, lean_object* v_t_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3186_, v_t_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3191_, size_t v_i_3192_, size_t v_stop_3193_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_usize_dec_eq(v_i_3192_, v_stop_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; uint8_t v_severity_3196_; 
v___x_3195_ = lean_array_uget_borrowed(v_as_3191_, v_i_3192_);
v_severity_3196_ = lean_ctor_get_uint8(v___x_3195_, sizeof(void*)*5 + 1);
if (v_severity_3196_ == 2)
{
uint8_t v___x_3197_; 
v___x_3197_ = 1;
return v___x_3197_;
}
else
{
size_t v___x_3198_; size_t v___x_3199_; 
v___x_3198_ = ((size_t)1ULL);
v___x_3199_ = lean_usize_add(v_i_3192_, v___x_3198_);
v_i_3192_ = v___x_3199_;
goto _start;
}
}
else
{
uint8_t v___x_3201_; 
v___x_3201_ = 0;
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3202_, lean_object* v_i_3203_, lean_object* v_stop_3204_){
_start:
{
size_t v_i_boxed_3205_; size_t v_stop_boxed_3206_; uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_i_boxed_3205_ = lean_unbox_usize(v_i_3203_);
lean_dec(v_i_3203_);
v_stop_boxed_3206_ = lean_unbox_usize(v_stop_3204_);
lean_dec(v_stop_3204_);
v_res_3207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3202_, v_i_boxed_3205_, v_stop_boxed_3206_);
lean_dec_ref(v_as_3202_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3209_){
_start:
{
if (lean_obj_tag(v_x_3209_) == 0)
{
lean_object* v_cs_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_cs_3210_ = lean_ctor_get(v_x_3209_, 0);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_array_get_size(v_cs_3210_);
v___x_3213_ = lean_nat_dec_lt(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
return v___x_3213_;
}
else
{
size_t v___x_3214_; size_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3214_ = ((size_t)0ULL);
v___x_3215_ = lean_usize_of_nat(v___x_3212_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3210_, v___x_3214_, v___x_3215_);
return v___x_3216_;
}
}
else
{
lean_object* v_vs_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_vs_3217_ = lean_ctor_get(v_x_3209_, 0);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_array_get_size(v_vs_3217_);
v___x_3220_ = lean_nat_dec_lt(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
return v___x_3220_;
}
else
{
size_t v___x_3221_; size_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = lean_usize_of_nat(v___x_3219_);
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3217_, v___x_3221_, v___x_3222_);
return v___x_3223_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3224_, size_t v_i_3225_, size_t v_stop_3226_){
_start:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_eq(v_i_3225_, v_stop_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_array_uget_borrowed(v_as_3224_, v_i_3225_);
v___x_3229_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3228_);
if (v___x_3229_ == 0)
{
size_t v___x_3230_; size_t v___x_3231_; 
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3225_, v___x_3230_);
v_i_3225_ = v___x_3231_;
goto _start;
}
else
{
return v___x_3229_;
}
}
else
{
uint8_t v___x_3233_; 
v___x_3233_ = 0;
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3234_, lean_object* v_i_3235_, lean_object* v_stop_3236_){
_start:
{
size_t v_i_boxed_3237_; size_t v_stop_boxed_3238_; uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_i_boxed_3237_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_stop_boxed_3238_ = lean_unbox_usize(v_stop_3236_);
lean_dec(v_stop_3236_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3234_, v_i_boxed_3237_, v_stop_boxed_3238_);
lean_dec_ref(v_as_3234_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3241_);
lean_dec_ref(v_x_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3244_){
_start:
{
lean_object* v_root_3245_; lean_object* v_tail_3246_; uint8_t v___x_3247_; 
v_root_3245_ = lean_ctor_get(v_t_3244_, 0);
v_tail_3246_ = lean_ctor_get(v_t_3244_, 1);
v___x_3247_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3245_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = lean_array_get_size(v_tail_3246_);
v___x_3250_ = lean_nat_dec_lt(v___x_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
return v___x_3250_;
}
else
{
size_t v___x_3251_; size_t v___x_3252_; uint8_t v___x_3253_; 
v___x_3251_ = ((size_t)0ULL);
v___x_3252_ = lean_usize_of_nat(v___x_3249_);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3246_, v___x_3251_, v___x_3252_);
return v___x_3253_;
}
}
else
{
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3254_){
_start:
{
uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_res_3255_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3254_);
lean_dec_ref(v_t_3254_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3257_, lean_object* v_as_3258_, size_t v_i_3259_, size_t v_stop_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_usize_dec_eq(v_i_3259_, v_stop_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; uint8_t v_severity_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_array_uget_borrowed(v_as_3258_, v_i_3259_);
v_severity_3263_ = lean_ctor_get_uint8(v___x_3262_, sizeof(void*)*5 + 1);
v___x_3264_ = 1;
if (v_severity_3263_ == 2)
{
return v___x_3264_;
}
else
{
if (v___x_3257_ == 0)
{
size_t v___x_3265_; size_t v___x_3266_; 
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3259_, v___x_3265_);
v_i_3259_ = v___x_3266_;
goto _start;
}
else
{
return v___x_3264_;
}
}
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = 0;
return v___x_3268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3269_, lean_object* v_as_3270_, lean_object* v_i_3271_, lean_object* v_stop_3272_){
_start:
{
uint8_t v___x_1809__boxed_3273_; size_t v_i_boxed_3274_; size_t v_stop_boxed_3275_; uint8_t v_res_3276_; lean_object* v_r_3277_; 
v___x_1809__boxed_3273_ = lean_unbox(v___x_3269_);
v_i_boxed_3274_ = lean_unbox_usize(v_i_3271_);
lean_dec(v_i_3271_);
v_stop_boxed_3275_ = lean_unbox_usize(v_stop_3272_);
lean_dec(v_stop_3272_);
v_res_3276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3273_, v_as_3270_, v_i_boxed_3274_, v_stop_boxed_3275_);
lean_dec_ref(v_as_3270_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v_cs_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v_cs_3280_ = lean_ctor_get(v_x_3279_, 0);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = lean_array_get_size(v_cs_3280_);
v___x_3283_ = lean_nat_dec_lt(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
return v___x_3283_;
}
else
{
size_t v___x_3284_; size_t v___x_3285_; uint8_t v___x_3286_; 
v___x_3284_ = ((size_t)0ULL);
v___x_3285_ = lean_usize_of_nat(v___x_3282_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3278_, v_cs_3280_, v___x_3284_, v___x_3285_);
return v___x_3286_;
}
}
else
{
lean_object* v_vs_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v_vs_3287_ = lean_ctor_get(v_x_3279_, 0);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v_vs_3287_);
v___x_3290_ = lean_nat_dec_lt(v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
return v___x_3290_;
}
else
{
size_t v___x_3291_; size_t v___x_3292_; uint8_t v___x_3293_; 
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = lean_usize_of_nat(v___x_3289_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3278_, v_vs_3287_, v___x_3291_, v___x_3292_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3294_, lean_object* v_as_3295_, size_t v_i_3296_, size_t v_stop_3297_){
_start:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_usize_dec_eq(v_i_3296_, v_stop_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = lean_array_uget_borrowed(v_as_3295_, v_i_3296_);
v___x_3300_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3294_, v___x_3299_);
if (v___x_3300_ == 0)
{
size_t v___x_3301_; size_t v___x_3302_; 
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3296_, v___x_3301_);
v_i_3296_ = v___x_3302_;
goto _start;
}
else
{
return v___x_3300_;
}
}
else
{
uint8_t v___x_3304_; 
v___x_3304_ = 0;
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3305_, lean_object* v_as_3306_, lean_object* v_i_3307_, lean_object* v_stop_3308_){
_start:
{
uint8_t v___x_1826__boxed_3309_; size_t v_i_boxed_3310_; size_t v_stop_boxed_3311_; uint8_t v_res_3312_; lean_object* v_r_3313_; 
v___x_1826__boxed_3309_ = lean_unbox(v___x_3305_);
v_i_boxed_3310_ = lean_unbox_usize(v_i_3307_);
lean_dec(v_i_3307_);
v_stop_boxed_3311_ = lean_unbox_usize(v_stop_3308_);
lean_dec(v_stop_3308_);
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3309_, v_as_3306_, v_i_boxed_3310_, v_stop_boxed_3311_);
lean_dec_ref(v_as_3306_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3314_, lean_object* v_x_3315_){
_start:
{
uint8_t v___x_1834__boxed_3316_; uint8_t v_res_3317_; lean_object* v_r_3318_; 
v___x_1834__boxed_3316_ = lean_unbox(v___x_3314_);
v_res_3317_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3316_, v_x_3315_);
lean_dec_ref(v_x_3315_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3319_, lean_object* v_t_3320_){
_start:
{
lean_object* v_root_3321_; lean_object* v_tail_3322_; uint8_t v___x_3323_; 
v_root_3321_ = lean_ctor_get(v_t_3320_, 0);
v_tail_3322_ = lean_ctor_get(v_t_3320_, 1);
v___x_3323_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3319_, v_root_3321_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_array_get_size(v_tail_3322_);
v___x_3326_ = lean_nat_dec_lt(v___x_3324_, v___x_3325_);
if (v___x_3326_ == 0)
{
return v___x_3326_;
}
else
{
size_t v___x_3327_; size_t v___x_3328_; uint8_t v___x_3329_; 
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3325_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3319_, v_tail_3322_, v___x_3327_, v___x_3328_);
return v___x_3329_;
}
}
else
{
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3330_, lean_object* v_t_3331_){
_start:
{
uint8_t v___x_1877__boxed_3332_; uint8_t v_res_3333_; lean_object* v_r_3334_; 
v___x_1877__boxed_3332_ = lean_unbox(v___x_3330_);
v_res_3333_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3332_, v_t_3331_);
lean_dec_ref(v_t_3331_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3335_){
_start:
{
lean_object* v_reported_3336_; lean_object* v_unreported_3337_; uint8_t v___x_3338_; 
v_reported_3336_ = lean_ctor_get(v_log_3335_, 0);
v_unreported_3337_ = lean_ctor_get(v_log_3335_, 1);
v___x_3338_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3336_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
v___x_3339_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3338_, v_unreported_3337_);
return v___x_3339_;
}
else
{
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3340_){
_start:
{
uint8_t v_res_3341_; lean_object* v_r_3342_; 
v_res_3341_ = l_Lean_MessageLog_hasErrors(v_log_3340_);
lean_dec_ref(v_log_3340_);
v_r_3342_ = lean_box(v_res_3341_);
return v_r_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3343_){
_start:
{
lean_object* v_reported_3344_; lean_object* v_unreported_3345_; lean_object* v_loggedKinds_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3357_; 
v_reported_3344_ = lean_ctor_get(v_log_3343_, 0);
v_unreported_3345_ = lean_ctor_get(v_log_3343_, 1);
v_loggedKinds_3346_ = lean_ctor_get(v_log_3343_, 2);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_log_3343_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3348_ = v_log_3343_;
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_loggedKinds_3346_);
lean_inc(v_unreported_3345_);
lean_inc(v_reported_3344_);
lean_dec(v_log_3343_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3350_ = l_Lean_PersistentArray_append___redArg(v_reported_3344_, v_unreported_3345_);
lean_dec_ref(v_unreported_3345_);
v___x_3351_ = lean_unsigned_to_nat(32u);
v___x_3352_ = lean_mk_empty_array_with_capacity(v___x_3351_);
lean_dec_ref(v___x_3352_);
v___x_3353_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v___x_3353_);
lean_ctor_set(v___x_3348_, 0, v___x_3350_);
v___x_3355_ = v___x_3348_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_loggedKinds_3346_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3358_, size_t v_i_3359_, lean_object* v_bs_3360_){
_start:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_usize_dec_lt(v_i_3359_, v_sz_3358_);
if (v___x_3361_ == 0)
{
return v_bs_3360_;
}
else
{
lean_object* v_v_3362_; lean_object* v_fileName_3363_; lean_object* v_pos_3364_; lean_object* v_endPos_3365_; uint8_t v_keepFullRange_3366_; uint8_t v_severity_3367_; uint8_t v_isSilent_3368_; lean_object* v_caption_3369_; lean_object* v_data_3370_; lean_object* v___x_3371_; lean_object* v_bs_x27_3372_; lean_object* v___y_3374_; 
v_v_3362_ = lean_array_uget(v_bs_3360_, v_i_3359_);
v_fileName_3363_ = lean_ctor_get(v_v_3362_, 0);
v_pos_3364_ = lean_ctor_get(v_v_3362_, 1);
v_endPos_3365_ = lean_ctor_get(v_v_3362_, 2);
v_keepFullRange_3366_ = lean_ctor_get_uint8(v_v_3362_, sizeof(void*)*5);
v_severity_3367_ = lean_ctor_get_uint8(v_v_3362_, sizeof(void*)*5 + 1);
v_isSilent_3368_ = lean_ctor_get_uint8(v_v_3362_, sizeof(void*)*5 + 2);
v_caption_3369_ = lean_ctor_get(v_v_3362_, 3);
v_data_3370_ = lean_ctor_get(v_v_3362_, 4);
v___x_3371_ = lean_unsigned_to_nat(0u);
v_bs_x27_3372_ = lean_array_uset(v_bs_3360_, v_i_3359_, v___x_3371_);
if (v_severity_3367_ == 2)
{
lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3386_; 
lean_inc(v_data_3370_);
lean_inc_ref(v_caption_3369_);
lean_inc(v_endPos_3365_);
lean_inc_ref(v_pos_3364_);
lean_inc_ref(v_fileName_3363_);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_v_3362_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; lean_object* v_unused_3390_; lean_object* v_unused_3391_; 
v_unused_3387_ = lean_ctor_get(v_v_3362_, 4);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_v_3362_, 3);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_v_3362_, 2);
lean_dec(v_unused_3389_);
v_unused_3390_ = lean_ctor_get(v_v_3362_, 1);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v_v_3362_, 0);
lean_dec(v_unused_3391_);
v___x_3380_ = v_v_3362_;
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
else
{
lean_dec(v_v_3362_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
uint8_t v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = 1;
if (v_isShared_3381_ == 0)
{
v___x_3384_ = v___x_3380_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_fileName_3363_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_pos_3364_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_endPos_3365_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_caption_3369_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_data_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*5, v_keepFullRange_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*5 + 2, v_isSilent_3368_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*5 + 1, v___x_3382_);
v___y_3374_ = v___x_3384_;
goto v___jp_3373_;
}
}
}
else
{
v___y_3374_ = v_v_3362_;
goto v___jp_3373_;
}
v___jp_3373_:
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = ((size_t)1ULL);
v___x_3376_ = lean_usize_add(v_i_3359_, v___x_3375_);
v___x_3377_ = lean_array_uset(v_bs_x27_3372_, v_i_3359_, v___y_3374_);
v_i_3359_ = v___x_3376_;
v_bs_3360_ = v___x_3377_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_bs_3394_){
_start:
{
size_t v_sz_boxed_3395_; size_t v_i_boxed_3396_; lean_object* v_res_3397_; 
v_sz_boxed_3395_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3396_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3395_, v_i_boxed_3396_, v_bs_3394_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3398_, size_t v_i_3399_, lean_object* v_bs_3400_){
_start:
{
uint8_t v___x_3401_; 
v___x_3401_ = lean_usize_dec_lt(v_i_3399_, v_sz_3398_);
if (v___x_3401_ == 0)
{
return v_bs_3400_;
}
else
{
lean_object* v_v_3402_; lean_object* v___x_3403_; lean_object* v_bs_x27_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; 
v_v_3402_ = lean_array_uget(v_bs_3400_, v_i_3399_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v_bs_x27_3404_ = lean_array_uset(v_bs_3400_, v_i_3399_, v___x_3403_);
v___x_3405_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3402_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3399_, v___x_3406_);
v___x_3408_ = lean_array_uset(v_bs_x27_3404_, v_i_3399_, v___x_3405_);
v_i_3399_ = v___x_3407_;
v_bs_3400_ = v___x_3408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3410_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 0)
{
lean_object* v_cs_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3421_; 
v_cs_3411_ = lean_ctor_get(v_x_3410_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_x_3410_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3413_ = v_x_3410_;
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_cs_3411_);
lean_dec(v_x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3421_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
size_t v_sz_3415_; size_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v_sz_3415_ = lean_array_size(v_cs_3411_);
v___x_3416_ = ((size_t)0ULL);
v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3415_, v___x_3416_, v_cs_3411_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3417_);
v___x_3419_ = v___x_3413_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
else
{
lean_object* v_vs_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3432_; 
v_vs_3422_ = lean_ctor_get(v_x_3410_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_x_3410_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3424_ = v_x_3410_;
v_isShared_3425_ = v_isSharedCheck_3432_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_vs_3422_);
lean_dec(v_x_3410_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3432_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
size_t v_sz_3426_; size_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v_sz_3426_ = lean_array_size(v_vs_3422_);
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3426_, v___x_3427_, v_vs_3422_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3428_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3433_, lean_object* v_i_3434_, lean_object* v_bs_3435_){
_start:
{
size_t v_sz_boxed_3436_; size_t v_i_boxed_3437_; lean_object* v_res_3438_; 
v_sz_boxed_3436_ = lean_unbox_usize(v_sz_3433_);
lean_dec(v_sz_3433_);
v_i_boxed_3437_ = lean_unbox_usize(v_i_3434_);
lean_dec(v_i_3434_);
v_res_3438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3436_, v_i_boxed_3437_, v_bs_3435_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3439_){
_start:
{
lean_object* v_root_3440_; lean_object* v_tail_3441_; lean_object* v_size_3442_; size_t v_shift_3443_; lean_object* v_tailOff_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3455_; 
v_root_3440_ = lean_ctor_get(v_t_3439_, 0);
v_tail_3441_ = lean_ctor_get(v_t_3439_, 1);
v_size_3442_ = lean_ctor_get(v_t_3439_, 2);
v_shift_3443_ = lean_ctor_get_usize(v_t_3439_, 4);
v_tailOff_3444_ = lean_ctor_get(v_t_3439_, 3);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_t_3439_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3446_ = v_t_3439_;
v_isShared_3447_ = v_isSharedCheck_3455_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_tailOff_3444_);
lean_inc(v_size_3442_);
lean_inc(v_tail_3441_);
lean_inc(v_root_3440_);
lean_dec(v_t_3439_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3455_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; size_t v_sz_3449_; size_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3448_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3440_);
v_sz_3449_ = lean_array_size(v_tail_3441_);
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3449_, v___x_3450_, v_tail_3441_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3451_);
lean_ctor_set(v___x_3446_, 0, v___x_3448_);
v___x_3453_ = v___x_3446_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_size_3442_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_tailOff_3444_);
lean_ctor_set_usize(v_reuseFailAlloc_3454_, 4, v_shift_3443_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3456_){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_unreported_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3469_; 
v___x_3457_ = lean_unsigned_to_nat(32u);
v___x_3458_ = lean_mk_empty_array_with_capacity(v___x_3457_);
lean_dec_ref(v___x_3458_);
v___x_3459_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3460_ = lean_ctor_get(v_log_3456_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_log_3456_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; lean_object* v_unused_3471_; 
v_unused_3470_ = lean_ctor_get(v_log_3456_, 2);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_log_3456_, 0);
lean_dec(v_unused_3471_);
v___x_3462_ = v_log_3456_;
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_unreported_3460_);
lean_dec(v_log_3456_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3460_);
v___x_3465_ = l_Lean_NameSet_empty;
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 2, v___x_3465_);
lean_ctor_set(v___x_3462_, 1, v___x_3464_);
lean_ctor_set(v___x_3462_, 0, v___x_3459_);
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3472_, size_t v_i_3473_, lean_object* v_bs_3474_){
_start:
{
uint8_t v___x_3475_; 
v___x_3475_ = lean_usize_dec_lt(v_i_3473_, v_sz_3472_);
if (v___x_3475_ == 0)
{
return v_bs_3474_;
}
else
{
lean_object* v_v_3476_; lean_object* v_fileName_3477_; lean_object* v_pos_3478_; lean_object* v_endPos_3479_; uint8_t v_keepFullRange_3480_; uint8_t v_severity_3481_; uint8_t v_isSilent_3482_; lean_object* v_caption_3483_; lean_object* v_data_3484_; lean_object* v___x_3485_; lean_object* v_bs_x27_3486_; lean_object* v___y_3488_; 
v_v_3476_ = lean_array_uget(v_bs_3474_, v_i_3473_);
v_fileName_3477_ = lean_ctor_get(v_v_3476_, 0);
v_pos_3478_ = lean_ctor_get(v_v_3476_, 1);
v_endPos_3479_ = lean_ctor_get(v_v_3476_, 2);
v_keepFullRange_3480_ = lean_ctor_get_uint8(v_v_3476_, sizeof(void*)*5);
v_severity_3481_ = lean_ctor_get_uint8(v_v_3476_, sizeof(void*)*5 + 1);
v_isSilent_3482_ = lean_ctor_get_uint8(v_v_3476_, sizeof(void*)*5 + 2);
v_caption_3483_ = lean_ctor_get(v_v_3476_, 3);
v_data_3484_ = lean_ctor_get(v_v_3476_, 4);
v___x_3485_ = lean_unsigned_to_nat(0u);
v_bs_x27_3486_ = lean_array_uset(v_bs_3474_, v_i_3473_, v___x_3485_);
if (v_severity_3481_ == 2)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
lean_inc(v_data_3484_);
lean_inc_ref(v_caption_3483_);
lean_inc(v_endPos_3479_);
lean_inc_ref(v_pos_3478_);
lean_inc_ref(v_fileName_3477_);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_v_3476_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; lean_object* v_unused_3502_; lean_object* v_unused_3503_; lean_object* v_unused_3504_; lean_object* v_unused_3505_; 
v_unused_3501_ = lean_ctor_get(v_v_3476_, 4);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_v_3476_, 3);
lean_dec(v_unused_3502_);
v_unused_3503_ = lean_ctor_get(v_v_3476_, 2);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_v_3476_, 1);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_v_3476_, 0);
lean_dec(v_unused_3505_);
v___x_3494_ = v_v_3476_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v_v_3476_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
uint8_t v___x_3496_; lean_object* v___x_3498_; 
v___x_3496_ = 0;
if (v_isShared_3495_ == 0)
{
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_fileName_3477_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_pos_3478_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_endPos_3479_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_caption_3483_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_data_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3499_, sizeof(void*)*5, v_keepFullRange_3480_);
lean_ctor_set_uint8(v_reuseFailAlloc_3499_, sizeof(void*)*5 + 2, v_isSilent_3482_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*5 + 1, v___x_3496_);
v___y_3488_ = v___x_3498_;
goto v___jp_3487_;
}
}
}
else
{
v___y_3488_ = v_v_3476_;
goto v___jp_3487_;
}
v___jp_3487_:
{
size_t v___x_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((size_t)1ULL);
v___x_3490_ = lean_usize_add(v_i_3473_, v___x_3489_);
v___x_3491_ = lean_array_uset(v_bs_x27_3486_, v_i_3473_, v___y_3488_);
v_i_3473_ = v___x_3490_;
v_bs_3474_ = v___x_3491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3506_, lean_object* v_i_3507_, lean_object* v_bs_3508_){
_start:
{
size_t v_sz_boxed_3509_; size_t v_i_boxed_3510_; lean_object* v_res_3511_; 
v_sz_boxed_3509_ = lean_unbox_usize(v_sz_3506_);
lean_dec(v_sz_3506_);
v_i_boxed_3510_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3509_, v_i_boxed_3510_, v_bs_3508_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3512_, size_t v_i_3513_, lean_object* v_bs_3514_){
_start:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_usize_dec_lt(v_i_3513_, v_sz_3512_);
if (v___x_3515_ == 0)
{
return v_bs_3514_;
}
else
{
lean_object* v_v_3516_; lean_object* v___x_3517_; lean_object* v_bs_x27_3518_; lean_object* v___x_3519_; size_t v___x_3520_; size_t v___x_3521_; lean_object* v___x_3522_; 
v_v_3516_ = lean_array_uget(v_bs_3514_, v_i_3513_);
v___x_3517_ = lean_unsigned_to_nat(0u);
v_bs_x27_3518_ = lean_array_uset(v_bs_3514_, v_i_3513_, v___x_3517_);
v___x_3519_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3516_);
v___x_3520_ = ((size_t)1ULL);
v___x_3521_ = lean_usize_add(v_i_3513_, v___x_3520_);
v___x_3522_ = lean_array_uset(v_bs_x27_3518_, v_i_3513_, v___x_3519_);
v_i_3513_ = v___x_3521_;
v_bs_3514_ = v___x_3522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_object* v_cs_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3535_; 
v_cs_3525_ = lean_ctor_get(v_x_3524_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3527_ = v_x_3524_;
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_cs_3525_);
lean_dec(v_x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v_sz_3529_ = lean_array_size(v_cs_3525_);
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3529_, v___x_3530_, v_cs_3525_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3531_);
v___x_3533_ = v___x_3527_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
else
{
lean_object* v_vs_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3546_; 
v_vs_3536_ = lean_ctor_get(v_x_3524_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3538_ = v_x_3524_;
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_vs_3536_);
lean_dec(v_x_3524_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
size_t v_sz_3540_; size_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v_sz_3540_ = lean_array_size(v_vs_3536_);
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3540_, v___x_3541_, v_vs_3536_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3542_);
v___x_3544_ = v___x_3538_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3547_, lean_object* v_i_3548_, lean_object* v_bs_3549_){
_start:
{
size_t v_sz_boxed_3550_; size_t v_i_boxed_3551_; lean_object* v_res_3552_; 
v_sz_boxed_3550_ = lean_unbox_usize(v_sz_3547_);
lean_dec(v_sz_3547_);
v_i_boxed_3551_ = lean_unbox_usize(v_i_3548_);
lean_dec(v_i_3548_);
v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3550_, v_i_boxed_3551_, v_bs_3549_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3553_){
_start:
{
lean_object* v_root_3554_; lean_object* v_tail_3555_; lean_object* v_size_3556_; size_t v_shift_3557_; lean_object* v_tailOff_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3569_; 
v_root_3554_ = lean_ctor_get(v_t_3553_, 0);
v_tail_3555_ = lean_ctor_get(v_t_3553_, 1);
v_size_3556_ = lean_ctor_get(v_t_3553_, 2);
v_shift_3557_ = lean_ctor_get_usize(v_t_3553_, 4);
v_tailOff_3558_ = lean_ctor_get(v_t_3553_, 3);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_t_3553_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3560_ = v_t_3553_;
v_isShared_3561_ = v_isSharedCheck_3569_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_tailOff_3558_);
lean_inc(v_size_3556_);
lean_inc(v_tail_3555_);
lean_inc(v_root_3554_);
lean_dec(v_t_3553_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3569_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; size_t v_sz_3563_; size_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3562_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3554_);
v_sz_3563_ = lean_array_size(v_tail_3555_);
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3563_, v___x_3564_, v_tail_3555_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v___x_3565_);
lean_ctor_set(v___x_3560_, 0, v___x_3562_);
v___x_3567_ = v___x_3560_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_size_3556_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_tailOff_3558_);
lean_ctor_set_usize(v_reuseFailAlloc_3568_, 4, v_shift_3557_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3570_){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_unreported_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3583_; 
v___x_3571_ = lean_unsigned_to_nat(32u);
v___x_3572_ = lean_mk_empty_array_with_capacity(v___x_3571_);
lean_dec_ref(v___x_3572_);
v___x_3573_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3574_ = lean_ctor_get(v_log_3570_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_log_3570_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; lean_object* v_unused_3585_; 
v_unused_3584_ = lean_ctor_get(v_log_3570_, 2);
lean_dec(v_unused_3584_);
v_unused_3585_ = lean_ctor_get(v_log_3570_, 0);
lean_dec(v_unused_3585_);
v___x_3576_ = v_log_3570_;
v_isShared_3577_ = v_isSharedCheck_3583_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_unreported_3574_);
lean_dec(v_log_3570_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3583_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3578_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3574_);
v___x_3579_ = l_Lean_NameSet_empty;
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 2, v___x_3579_);
lean_ctor_set(v___x_3576_, 1, v___x_3578_);
lean_ctor_set(v___x_3576_, 0, v___x_3573_);
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3586_, size_t v_i_3587_, size_t v_stop_3588_, lean_object* v_b_3589_){
_start:
{
lean_object* v___y_3591_; uint8_t v___x_3595_; 
v___x_3595_ = lean_usize_dec_eq(v_i_3587_, v_stop_3588_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; uint8_t v_severity_3597_; 
v___x_3596_ = lean_array_uget_borrowed(v_as_3586_, v_i_3587_);
v_severity_3597_ = lean_ctor_get_uint8(v___x_3596_, sizeof(void*)*5 + 1);
if (v_severity_3597_ == 0)
{
lean_object* v___x_3598_; 
lean_inc(v___x_3596_);
v___x_3598_ = l_Lean_PersistentArray_push___redArg(v_b_3589_, v___x_3596_);
v___y_3591_ = v___x_3598_;
goto v___jp_3590_;
}
else
{
v___y_3591_ = v_b_3589_;
goto v___jp_3590_;
}
}
else
{
return v_b_3589_;
}
v___jp_3590_:
{
size_t v___x_3592_; size_t v___x_3593_; 
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3587_, v___x_3592_);
v_i_3587_ = v___x_3593_;
v_b_3589_ = v___y_3591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3599_, lean_object* v_i_3600_, lean_object* v_stop_3601_, lean_object* v_b_3602_){
_start:
{
size_t v_i_boxed_3603_; size_t v_stop_boxed_3604_; lean_object* v_res_3605_; 
v_i_boxed_3603_ = lean_unbox_usize(v_i_3600_);
lean_dec(v_i_3600_);
v_stop_boxed_3604_ = lean_unbox_usize(v_stop_3601_);
lean_dec(v_stop_3601_);
v_res_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3599_, v_i_boxed_3603_, v_stop_boxed_3604_, v_b_3602_);
lean_dec_ref(v_as_3599_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
lean_object* v_cs_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_cs_3608_ = lean_ctor_get(v_x_3606_, 0);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = lean_array_get_size(v_cs_3608_);
v___x_3611_ = lean_nat_dec_lt(v___x_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
return v_x_3607_;
}
else
{
size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_usize_of_nat(v___x_3610_);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3608_, v___x_3612_, v___x_3613_, v_x_3607_);
return v___x_3614_;
}
}
else
{
lean_object* v_vs_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_vs_3615_ = lean_ctor_get(v_x_3606_, 0);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = lean_array_get_size(v_vs_3615_);
v___x_3618_ = lean_nat_dec_lt(v___x_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
return v_x_3607_;
}
else
{
size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = ((size_t)0ULL);
v___x_3620_ = lean_usize_of_nat(v___x_3617_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3615_, v___x_3619_, v___x_3620_, v_x_3607_);
return v___x_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3622_, size_t v_i_3623_, size_t v_stop_3624_, lean_object* v_b_3625_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_eq(v_i_3623_, v_stop_3624_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; 
v___x_3627_ = lean_array_uget_borrowed(v_as_3622_, v_i_3623_);
v___x_3628_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3627_, v_b_3625_);
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3623_, v___x_3629_);
v_i_3623_ = v___x_3630_;
v_b_3625_ = v___x_3628_;
goto _start;
}
else
{
return v_b_3625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3632_, lean_object* v_i_3633_, lean_object* v_stop_3634_, lean_object* v_b_3635_){
_start:
{
size_t v_i_boxed_3636_; size_t v_stop_boxed_3637_; lean_object* v_res_3638_; 
v_i_boxed_3636_ = lean_unbox_usize(v_i_3633_);
lean_dec(v_i_3633_);
v_stop_boxed_3637_ = lean_unbox_usize(v_stop_3634_);
lean_dec(v_stop_3634_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3632_, v_i_boxed_3636_, v_stop_boxed_3637_, v_b_3635_);
lean_dec_ref(v_as_3632_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3639_, v_x_3640_);
lean_dec_ref(v_x_3639_);
return v_res_3641_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3643_, size_t v_x_3644_, size_t v_x_3645_, lean_object* v_x_3646_){
_start:
{
if (lean_obj_tag(v_x_3643_) == 0)
{
lean_object* v_cs_3647_; lean_object* v___x_3648_; size_t v___x_3649_; lean_object* v_j_3650_; lean_object* v___x_3651_; size_t v___x_3652_; size_t v___x_3653_; size_t v___x_3654_; size_t v___x_3655_; size_t v___x_3656_; size_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_cs_3647_ = lean_ctor_get(v_x_3643_, 0);
v___x_3648_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3649_ = lean_usize_shift_right(v_x_3644_, v_x_3645_);
v_j_3650_ = lean_usize_to_nat(v___x_3649_);
v___x_3651_ = lean_array_get_borrowed(v___x_3648_, v_cs_3647_, v_j_3650_);
v___x_3652_ = ((size_t)1ULL);
v___x_3653_ = lean_usize_shift_left(v___x_3652_, v_x_3645_);
v___x_3654_ = lean_usize_sub(v___x_3653_, v___x_3652_);
v___x_3655_ = lean_usize_land(v_x_3644_, v___x_3654_);
v___x_3656_ = ((size_t)5ULL);
v___x_3657_ = lean_usize_sub(v_x_3645_, v___x_3656_);
v___x_3658_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3651_, v___x_3655_, v___x_3657_, v_x_3646_);
v___x_3659_ = lean_unsigned_to_nat(1u);
v___x_3660_ = lean_nat_add(v_j_3650_, v___x_3659_);
lean_dec(v_j_3650_);
v___x_3661_ = lean_array_get_size(v_cs_3647_);
v___x_3662_ = lean_nat_dec_lt(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec(v___x_3660_);
return v___x_3658_;
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_usize_of_nat(v___x_3660_);
lean_dec(v___x_3660_);
v___x_3664_ = lean_usize_of_nat(v___x_3661_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3647_, v___x_3663_, v___x_3664_, v___x_3658_);
return v___x_3665_;
}
}
else
{
lean_object* v_vs_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_vs_3666_ = lean_ctor_get(v_x_3643_, 0);
v___x_3667_ = lean_usize_to_nat(v_x_3644_);
v___x_3668_ = lean_array_get_size(v_vs_3666_);
v___x_3669_ = lean_nat_dec_lt(v___x_3667_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_dec(v___x_3667_);
return v_x_3646_;
}
else
{
size_t v___x_3670_; size_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = lean_usize_of_nat(v___x_3667_);
lean_dec(v___x_3667_);
v___x_3671_ = lean_usize_of_nat(v___x_3668_);
v___x_3672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3666_, v___x_3670_, v___x_3671_, v_x_3646_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_, lean_object* v_x_3676_){
_start:
{
size_t v_x_1153__boxed_3677_; size_t v_x_1154__boxed_3678_; lean_object* v_res_3679_; 
v_x_1153__boxed_3677_ = lean_unbox_usize(v_x_3674_);
lean_dec(v_x_3674_);
v_x_1154__boxed_3678_ = lean_unbox_usize(v_x_3675_);
lean_dec(v_x_3675_);
v_res_3679_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3673_, v_x_1153__boxed_3677_, v_x_1154__boxed_3678_, v_x_3676_);
lean_dec_ref(v_x_3673_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3680_, lean_object* v_init_3681_, lean_object* v_start_3682_){
_start:
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = lean_unsigned_to_nat(0u);
v___x_3684_ = lean_nat_dec_eq(v_start_3682_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v_root_3685_; lean_object* v_tail_3686_; size_t v_shift_3687_; lean_object* v_tailOff_3688_; uint8_t v___x_3689_; 
v_root_3685_ = lean_ctor_get(v_t_3680_, 0);
v_tail_3686_ = lean_ctor_get(v_t_3680_, 1);
v_shift_3687_ = lean_ctor_get_usize(v_t_3680_, 4);
v_tailOff_3688_ = lean_ctor_get(v_t_3680_, 3);
v___x_3689_ = lean_nat_dec_le(v_tailOff_3688_, v_start_3682_);
if (v___x_3689_ == 0)
{
size_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3690_ = lean_usize_of_nat(v_start_3682_);
v___x_3691_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3685_, v___x_3690_, v_shift_3687_, v_init_3681_);
v___x_3692_ = lean_array_get_size(v_tail_3686_);
v___x_3693_ = lean_nat_dec_lt(v___x_3683_, v___x_3692_);
if (v___x_3693_ == 0)
{
return v___x_3691_;
}
else
{
size_t v___x_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = lean_usize_of_nat(v___x_3692_);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3686_, v___x_3694_, v___x_3695_, v___x_3691_);
return v___x_3696_;
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3697_ = lean_nat_sub(v_start_3682_, v_tailOff_3688_);
v___x_3698_ = lean_array_get_size(v_tail_3686_);
v___x_3699_ = lean_nat_dec_lt(v___x_3697_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_dec(v___x_3697_);
return v_init_3681_;
}
else
{
size_t v___x_3700_; size_t v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_usize_of_nat(v___x_3697_);
lean_dec(v___x_3697_);
v___x_3701_ = lean_usize_of_nat(v___x_3698_);
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3686_, v___x_3700_, v___x_3701_, v_init_3681_);
return v___x_3702_;
}
}
}
else
{
lean_object* v_root_3703_; lean_object* v_tail_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v_root_3703_ = lean_ctor_get(v_t_3680_, 0);
v_tail_3704_ = lean_ctor_get(v_t_3680_, 1);
v___x_3705_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3703_, v_init_3681_);
v___x_3706_ = lean_array_get_size(v_tail_3704_);
v___x_3707_ = lean_nat_dec_lt(v___x_3683_, v___x_3706_);
if (v___x_3707_ == 0)
{
return v___x_3705_;
}
else
{
size_t v___x_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = ((size_t)0ULL);
v___x_3709_ = lean_usize_of_nat(v___x_3706_);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3704_, v___x_3708_, v___x_3709_, v___x_3705_);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3711_, lean_object* v_init_3712_, lean_object* v_start_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3711_, v_init_3712_, v_start_3713_);
lean_dec(v_start_3713_);
lean_dec_ref(v_t_3711_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3715_){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_unreported_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3729_; 
v___x_3716_ = lean_unsigned_to_nat(32u);
v___x_3717_ = lean_mk_empty_array_with_capacity(v___x_3716_);
lean_dec_ref(v___x_3717_);
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3720_ = lean_ctor_get(v_log_3715_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_log_3715_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; lean_object* v_unused_3731_; 
v_unused_3730_ = lean_ctor_get(v_log_3715_, 2);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_log_3715_, 0);
lean_dec(v_unused_3731_);
v___x_3722_ = v_log_3715_;
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_unreported_3720_);
lean_dec(v_log_3715_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3724_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3720_, v___x_3719_, v___x_3718_);
lean_dec_ref(v_unreported_3720_);
v___x_3725_ = l_Lean_NameSet_empty;
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 2, v___x_3725_);
lean_ctor_set(v___x_3722_, 1, v___x_3724_);
lean_ctor_set(v___x_3722_, 0, v___x_3719_);
v___x_3727_ = v___x_3722_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3732_, size_t v_i_3733_, size_t v_stop_3734_, lean_object* v_b_3735_){
_start:
{
lean_object* v___y_3737_; uint8_t v___x_3741_; 
v___x_3741_ = lean_usize_dec_eq(v_i_3733_, v_stop_3734_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; uint8_t v_severity_3743_; 
v___x_3742_ = lean_array_uget_borrowed(v_as_3732_, v_i_3733_);
v_severity_3743_ = lean_ctor_get_uint8(v___x_3742_, sizeof(void*)*5 + 1);
if (v_severity_3743_ == 1)
{
lean_object* v___x_3744_; 
lean_inc(v___x_3742_);
v___x_3744_ = l_Lean_PersistentArray_push___redArg(v_b_3735_, v___x_3742_);
v___y_3737_ = v___x_3744_;
goto v___jp_3736_;
}
else
{
v___y_3737_ = v_b_3735_;
goto v___jp_3736_;
}
}
else
{
return v_b_3735_;
}
v___jp_3736_:
{
size_t v___x_3738_; size_t v___x_3739_; 
v___x_3738_ = ((size_t)1ULL);
v___x_3739_ = lean_usize_add(v_i_3733_, v___x_3738_);
v_i_3733_ = v___x_3739_;
v_b_3735_ = v___y_3737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3745_, lean_object* v_i_3746_, lean_object* v_stop_3747_, lean_object* v_b_3748_){
_start:
{
size_t v_i_boxed_3749_; size_t v_stop_boxed_3750_; lean_object* v_res_3751_; 
v_i_boxed_3749_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_stop_boxed_3750_ = lean_unbox_usize(v_stop_3747_);
lean_dec(v_stop_3747_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3745_, v_i_boxed_3749_, v_stop_boxed_3750_, v_b_3748_);
lean_dec_ref(v_as_3745_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3752_, lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 0)
{
lean_object* v_cs_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v_cs_3754_ = lean_ctor_get(v_x_3752_, 0);
v___x_3755_ = lean_unsigned_to_nat(0u);
v___x_3756_ = lean_array_get_size(v_cs_3754_);
v___x_3757_ = lean_nat_dec_lt(v___x_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
return v_x_3753_;
}
else
{
size_t v___x_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = lean_usize_of_nat(v___x_3756_);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3754_, v___x_3758_, v___x_3759_, v_x_3753_);
return v___x_3760_;
}
}
else
{
lean_object* v_vs_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_vs_3761_ = lean_ctor_get(v_x_3752_, 0);
v___x_3762_ = lean_unsigned_to_nat(0u);
v___x_3763_ = lean_array_get_size(v_vs_3761_);
v___x_3764_ = lean_nat_dec_lt(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
return v_x_3753_;
}
else
{
size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = ((size_t)0ULL);
v___x_3766_ = lean_usize_of_nat(v___x_3763_);
v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3761_, v___x_3765_, v___x_3766_, v_x_3753_);
return v___x_3767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3768_, size_t v_i_3769_, size_t v_stop_3770_, lean_object* v_b_3771_){
_start:
{
uint8_t v___x_3772_; 
v___x_3772_ = lean_usize_dec_eq(v_i_3769_, v_stop_3770_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; size_t v___x_3775_; size_t v___x_3776_; 
v___x_3773_ = lean_array_uget_borrowed(v_as_3768_, v_i_3769_);
v___x_3774_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3773_, v_b_3771_);
v___x_3775_ = ((size_t)1ULL);
v___x_3776_ = lean_usize_add(v_i_3769_, v___x_3775_);
v_i_3769_ = v___x_3776_;
v_b_3771_ = v___x_3774_;
goto _start;
}
else
{
return v_b_3771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3778_, lean_object* v_i_3779_, lean_object* v_stop_3780_, lean_object* v_b_3781_){
_start:
{
size_t v_i_boxed_3782_; size_t v_stop_boxed_3783_; lean_object* v_res_3784_; 
v_i_boxed_3782_ = lean_unbox_usize(v_i_3779_);
lean_dec(v_i_3779_);
v_stop_boxed_3783_ = lean_unbox_usize(v_stop_3780_);
lean_dec(v_stop_3780_);
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3778_, v_i_boxed_3782_, v_stop_boxed_3783_, v_b_3781_);
lean_dec_ref(v_as_3778_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3785_, v_x_3786_);
lean_dec_ref(v_x_3785_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3788_, size_t v_x_3789_, size_t v_x_3790_, lean_object* v_x_3791_){
_start:
{
if (lean_obj_tag(v_x_3788_) == 0)
{
lean_object* v_cs_3792_; lean_object* v___x_3793_; size_t v___x_3794_; lean_object* v_j_3795_; lean_object* v___x_3796_; size_t v___x_3797_; size_t v___x_3798_; size_t v___x_3799_; size_t v___x_3800_; size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_cs_3792_ = lean_ctor_get(v_x_3788_, 0);
v___x_3793_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3794_ = lean_usize_shift_right(v_x_3789_, v_x_3790_);
v_j_3795_ = lean_usize_to_nat(v___x_3794_);
v___x_3796_ = lean_array_get_borrowed(v___x_3793_, v_cs_3792_, v_j_3795_);
v___x_3797_ = ((size_t)1ULL);
v___x_3798_ = lean_usize_shift_left(v___x_3797_, v_x_3790_);
v___x_3799_ = lean_usize_sub(v___x_3798_, v___x_3797_);
v___x_3800_ = lean_usize_land(v_x_3789_, v___x_3799_);
v___x_3801_ = ((size_t)5ULL);
v___x_3802_ = lean_usize_sub(v_x_3790_, v___x_3801_);
v___x_3803_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3796_, v___x_3800_, v___x_3802_, v_x_3791_);
v___x_3804_ = lean_unsigned_to_nat(1u);
v___x_3805_ = lean_nat_add(v_j_3795_, v___x_3804_);
lean_dec(v_j_3795_);
v___x_3806_ = lean_array_get_size(v_cs_3792_);
v___x_3807_ = lean_nat_dec_lt(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_dec(v___x_3805_);
return v___x_3803_;
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_usize_of_nat(v___x_3805_);
lean_dec(v___x_3805_);
v___x_3809_ = lean_usize_of_nat(v___x_3806_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3792_, v___x_3808_, v___x_3809_, v___x_3803_);
return v___x_3810_;
}
}
else
{
lean_object* v_vs_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_vs_3811_ = lean_ctor_get(v_x_3788_, 0);
v___x_3812_ = lean_usize_to_nat(v_x_3789_);
v___x_3813_ = lean_array_get_size(v_vs_3811_);
v___x_3814_ = lean_nat_dec_lt(v___x_3812_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_dec(v___x_3812_);
return v_x_3791_;
}
else
{
size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = lean_usize_of_nat(v___x_3812_);
lean_dec(v___x_3812_);
v___x_3816_ = lean_usize_of_nat(v___x_3813_);
v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3811_, v___x_3815_, v___x_3816_, v_x_3791_);
return v___x_3817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3818_, lean_object* v_x_3819_, lean_object* v_x_3820_, lean_object* v_x_3821_){
_start:
{
size_t v_x_1152__boxed_3822_; size_t v_x_1153__boxed_3823_; lean_object* v_res_3824_; 
v_x_1152__boxed_3822_ = lean_unbox_usize(v_x_3819_);
lean_dec(v_x_3819_);
v_x_1153__boxed_3823_ = lean_unbox_usize(v_x_3820_);
lean_dec(v_x_3820_);
v_res_3824_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3818_, v_x_1152__boxed_3822_, v_x_1153__boxed_3823_, v_x_3821_);
lean_dec_ref(v_x_3818_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3825_, lean_object* v_init_3826_, lean_object* v_start_3827_){
_start:
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = lean_unsigned_to_nat(0u);
v___x_3829_ = lean_nat_dec_eq(v_start_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v_root_3830_; lean_object* v_tail_3831_; size_t v_shift_3832_; lean_object* v_tailOff_3833_; uint8_t v___x_3834_; 
v_root_3830_ = lean_ctor_get(v_t_3825_, 0);
v_tail_3831_ = lean_ctor_get(v_t_3825_, 1);
v_shift_3832_ = lean_ctor_get_usize(v_t_3825_, 4);
v_tailOff_3833_ = lean_ctor_get(v_t_3825_, 3);
v___x_3834_ = lean_nat_dec_le(v_tailOff_3833_, v_start_3827_);
if (v___x_3834_ == 0)
{
size_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = lean_usize_of_nat(v_start_3827_);
v___x_3836_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3830_, v___x_3835_, v_shift_3832_, v_init_3826_);
v___x_3837_ = lean_array_get_size(v_tail_3831_);
v___x_3838_ = lean_nat_dec_lt(v___x_3828_, v___x_3837_);
if (v___x_3838_ == 0)
{
return v___x_3836_;
}
else
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = ((size_t)0ULL);
v___x_3840_ = lean_usize_of_nat(v___x_3837_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3831_, v___x_3839_, v___x_3840_, v___x_3836_);
return v___x_3841_;
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = lean_nat_sub(v_start_3827_, v_tailOff_3833_);
v___x_3843_ = lean_array_get_size(v_tail_3831_);
v___x_3844_ = lean_nat_dec_lt(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_dec(v___x_3842_);
return v_init_3826_;
}
else
{
size_t v___x_3845_; size_t v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = lean_usize_of_nat(v___x_3842_);
lean_dec(v___x_3842_);
v___x_3846_ = lean_usize_of_nat(v___x_3843_);
v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3831_, v___x_3845_, v___x_3846_, v_init_3826_);
return v___x_3847_;
}
}
}
else
{
lean_object* v_root_3848_; lean_object* v_tail_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v_root_3848_ = lean_ctor_get(v_t_3825_, 0);
v_tail_3849_ = lean_ctor_get(v_t_3825_, 1);
v___x_3850_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3848_, v_init_3826_);
v___x_3851_ = lean_array_get_size(v_tail_3849_);
v___x_3852_ = lean_nat_dec_lt(v___x_3828_, v___x_3851_);
if (v___x_3852_ == 0)
{
return v___x_3850_;
}
else
{
size_t v___x_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = ((size_t)0ULL);
v___x_3854_ = lean_usize_of_nat(v___x_3851_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3849_, v___x_3853_, v___x_3854_, v___x_3850_);
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3856_, lean_object* v_init_3857_, lean_object* v_start_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3856_, v_init_3857_, v_start_3858_);
lean_dec(v_start_3858_);
lean_dec_ref(v_t_3856_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3860_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_unreported_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3874_; 
v___x_3861_ = lean_unsigned_to_nat(32u);
v___x_3862_ = lean_mk_empty_array_with_capacity(v___x_3861_);
lean_dec_ref(v___x_3862_);
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3865_ = lean_ctor_get(v_log_3860_, 1);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_log_3860_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; lean_object* v_unused_3876_; 
v_unused_3875_ = lean_ctor_get(v_log_3860_, 2);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_log_3860_, 0);
lean_dec(v_unused_3876_);
v___x_3867_ = v_log_3860_;
v_isShared_3868_ = v_isSharedCheck_3874_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_unreported_3865_);
lean_dec(v_log_3860_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3874_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3869_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3865_, v___x_3864_, v___x_3863_);
lean_dec_ref(v_unreported_3865_);
v___x_3870_ = l_Lean_NameSet_empty;
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 2, v___x_3870_);
lean_ctor_set(v___x_3867_, 1, v___x_3869_);
lean_ctor_set(v___x_3867_, 0, v___x_3864_);
v___x_3872_ = v___x_3867_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3877_, lean_object* v_log_3878_, lean_object* v_f_3879_){
_start:
{
lean_object* v_unreported_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_unreported_3880_ = lean_ctor_get(v_log_3878_, 1);
lean_inc_ref(v_unreported_3880_);
lean_dec_ref(v_log_3878_);
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = l_Lean_PersistentArray_forM___redArg(v_inst_3877_, v_unreported_3880_, v_f_3879_, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3883_, lean_object* v_inst_3884_, lean_object* v_log_3885_, lean_object* v_f_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_MessageLog_forM___redArg(v_inst_3884_, v_log_3885_, v_f_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3888_){
_start:
{
lean_object* v_unreported_3889_; lean_object* v___x_3890_; 
v_unreported_3889_ = lean_ctor_get(v_log_3888_, 1);
v___x_3890_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_MessageLog_toList(v_log_3891_);
lean_dec_ref(v_log_3891_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3893_){
_start:
{
lean_object* v_unreported_3894_; lean_object* v___x_3895_; 
v_unreported_3894_ = lean_ctor_get(v_log_3893_, 1);
v___x_3895_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_MessageLog_toArray(v_log_3896_);
lean_dec_ref(v_log_3896_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3898_){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_unsigned_to_nat(2u);
v___x_3900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v_msg_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3901_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3902_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v_msg_3901_);
v___x_3904_ = l_Lean_MessageData_nestD(v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3905_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = l_Lean_MessageData_ofExpr(v_e_3905_);
v___x_3907_ = l_Lean_indentD(v___x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3908_, lean_object* v_msg_3909_){
_start:
{
lean_object* v_env_3911_; lean_object* v_mctx_3912_; lean_object* v_lctx_3913_; lean_object* v_opts_3914_; lean_object* v_currNamespace_3915_; lean_object* v_openDecls_3916_; lean_object* v___x_3917_; lean_object* v_msg_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_env_3911_ = lean_ctor_get(v_ctx_3908_, 0);
v_mctx_3912_ = lean_ctor_get(v_ctx_3908_, 1);
v_lctx_3913_ = lean_ctor_get(v_ctx_3908_, 2);
v_opts_3914_ = lean_ctor_get(v_ctx_3908_, 3);
v_currNamespace_3915_ = lean_ctor_get(v_ctx_3908_, 4);
v_openDecls_3916_ = lean_ctor_get(v_ctx_3908_, 5);
lean_inc(v_openDecls_3916_);
lean_inc(v_currNamespace_3915_);
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v_currNamespace_3915_);
lean_ctor_set(v___x_3917_, 1, v_openDecls_3916_);
v_msg_3918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3918_, 0, v___x_3917_);
lean_ctor_set(v_msg_3918_, 1, v_msg_3909_);
lean_inc_ref(v_opts_3914_);
lean_inc_ref(v_lctx_3913_);
lean_inc_ref(v_mctx_3912_);
lean_inc_ref(v_env_3911_);
v___x_3919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3919_, 0, v_env_3911_);
lean_ctor_set(v___x_3919_, 1, v_mctx_3912_);
lean_ctor_set(v___x_3919_, 2, v_lctx_3913_);
lean_ctor_set(v___x_3919_, 3, v_opts_3914_);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___x_3921_ = l_Lean_MessageData_format(v_msg_3918_, v___x_3920_);
v___x_3922_ = l_Std_Format_defWidth;
v___x_3923_ = lean_unsigned_to_nat(0u);
v___x_3924_ = l_Std_Format_pretty(v___x_3921_, v___x_3922_, v___x_3923_, v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3925_, lean_object* v_msg_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3925_, v_msg_3926_);
lean_dec_ref(v_ctx_3925_);
return v_res_3928_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_3929_, lean_object* v_a_3930_, uint8_t v_b_3931_){
_start:
{
lean_object* v_str_3932_; lean_object* v_startInclusive_3933_; lean_object* v_endExclusive_3934_; lean_object* v___x_3935_; uint8_t v_decide_3936_; 
v_str_3932_ = lean_ctor_get(v_s_3929_, 0);
v_startInclusive_3933_ = lean_ctor_get(v_s_3929_, 1);
v_endExclusive_3934_ = lean_ctor_get(v_s_3929_, 2);
v___x_3935_ = lean_nat_sub(v_endExclusive_3934_, v_startInclusive_3933_);
v_decide_3936_ = lean_nat_dec_eq(v_a_3930_, v___x_3935_);
lean_dec(v___x_3935_);
if (v_decide_3936_ == 0)
{
lean_object* v___x_3937_; uint32_t v___x_3938_; uint32_t v___x_3939_; uint8_t v___x_3940_; 
v___x_3937_ = lean_nat_add(v_startInclusive_3933_, v_a_3930_);
lean_dec(v_a_3930_);
v___x_3938_ = lean_string_utf8_get_fast(v_str_3932_, v___x_3937_);
v___x_3939_ = 10;
v___x_3940_ = lean_uint32_dec_eq(v___x_3938_, v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_string_utf8_next_fast(v_str_3932_, v___x_3937_);
lean_dec(v___x_3937_);
v___x_3942_ = lean_nat_sub(v___x_3941_, v_startInclusive_3933_);
v_a_3930_ = v___x_3942_;
v_b_3931_ = v___x_3940_;
goto _start;
}
else
{
lean_dec(v___x_3937_);
return v___x_3940_;
}
}
else
{
lean_dec(v_a_3930_);
return v_b_3931_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_3944_, lean_object* v_a_3945_, lean_object* v_b_3946_){
_start:
{
uint8_t v_b_boxed_3947_; uint8_t v_res_3948_; lean_object* v_r_3949_; 
v_b_boxed_3947_ = lean_unbox(v_b_3946_);
v_res_3948_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3944_, v_a_3945_, v_b_boxed_3947_);
lean_dec_ref(v_s_3944_);
v_r_3949_ = lean_box(v_res_3948_);
return v_r_3949_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_3950_){
_start:
{
lean_object* v_searcher_3951_; uint8_t v___x_3952_; uint8_t v___x_3953_; 
v_searcher_3951_ = lean_unsigned_to_nat(0u);
v___x_3952_ = 0;
v___x_3953_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3950_, v_searcher_3951_, v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_3954_){
_start:
{
uint8_t v_res_3955_; lean_object* v_r_3956_; 
v_res_3955_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_3954_);
lean_dec_ref(v_s_3954_);
v_r_3956_ = lean_box(v_res_3955_);
return v_r_3956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_3957_, lean_object* v_val_3958_, lean_object* v_a_3959_, lean_object* v_b_3960_){
_start:
{
uint8_t v_decide_3961_; 
v_decide_3961_ = lean_nat_dec_eq(v_a_3959_, v___x_3957_);
if (v_decide_3961_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_string_utf8_next_fast(v_val_3958_, v_a_3959_);
lean_dec(v_a_3959_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_3964_ = lean_nat_add(v_b_3960_, v___x_3963_);
lean_dec(v_b_3960_);
v_a_3959_ = v___x_3962_;
v_b_3960_ = v___x_3964_;
goto _start;
}
else
{
lean_dec(v_a_3959_);
return v_b_3960_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_3966_, lean_object* v_val_3967_, lean_object* v_a_3968_, lean_object* v_b_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3966_, v_val_3967_, v_a_3968_, v_b_3969_);
lean_dec_ref(v_val_3967_);
lean_dec(v___x_3966_);
return v_res_3970_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v___x_3972_ = l_Lean_MessageData_ofFormat(v___x_3971_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_3977_ = l_Lean_MessageData_ofFormat(v___x_3976_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_3982_ = l_Lean_MessageData_ofFormat(v___x_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3983_, lean_object* v_maxInlineLength_3984_, lean_object* v_ctx_3985_){
_start:
{
lean_object* v_msg_3987_; lean_object* v___x_3988_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; 
v_msg_3987_ = l_Lean_MessageData_ofExpr(v_e_3983_);
lean_inc_ref(v_msg_3987_);
v___x_3988_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3985_, v_msg_3987_);
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = lean_string_utf8_byte_size(v___x_3988_);
lean_inc_ref(v___x_3988_);
v___x_3995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3988_);
lean_ctor_set(v___x_3995_, 1, v___x_3993_);
lean_ctor_set(v___x_3995_, 2, v___x_3994_);
v___x_3996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3994_, v___x_3988_, v___x_3993_, v___x_3993_);
lean_dec_ref(v___x_3988_);
v___x_3997_ = lean_nat_dec_lt(v_maxInlineLength_3984_, v___x_3996_);
lean_dec(v___x_3996_);
if (v___x_3997_ == 0)
{
uint8_t v___x_3998_; 
v___x_3998_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_3995_);
lean_dec_ref_known(v___x_3995_, 3);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3999_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v_msg_3987_);
v___x_4001_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4000_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
return v___x_4002_;
}
else
{
goto v___jp_3989_;
}
}
else
{
lean_dec_ref_known(v___x_3995_, 3);
goto v___jp_3989_;
}
v___jp_3989_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = l_Lean_indentD(v_msg_3987_);
v___x_3991_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4003_, lean_object* v_maxInlineLength_4004_, lean_object* v_ctx_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_inlineExpr___lam__0(v_e_4003_, v_maxInlineLength_4004_, v_ctx_4005_);
lean_dec_ref(v_ctx_4005_);
lean_dec(v_maxInlineLength_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4008_, lean_object* v_x_4009_){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4011_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4012_ = l_Lean_MessageData_ofExpr(v_e_4008_);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_inlineExpr___lam__2(v_e_4016_, v_x_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4020_, lean_object* v_maxInlineLength_4021_){
_start:
{
lean_object* v___f_4022_; lean_object* v___f_4023_; lean_object* v___f_4024_; lean_object* v___x_4025_; 
lean_inc_ref_n(v_e_4020_, 2);
v___f_4022_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4022_, 0, v_e_4020_);
lean_closure_set(v___f_4022_, 1, v_maxInlineLength_4021_);
v___f_4023_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4023_, 0, v_e_4020_);
v___f_4024_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4024_, 0, v_e_4020_);
v___x_4025_ = l_Lean_MessageData_lazy(v___f_4022_, v___f_4023_, v___f_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4026_, lean_object* v___x_4027_, lean_object* v_val_4028_, lean_object* v_inst_4029_, lean_object* v_R_4030_, lean_object* v_a_4031_, lean_object* v_b_4032_, lean_object* v_c_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4026_, v_val_4028_, v_a_4031_, v_b_4032_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4035_, lean_object* v___x_4036_, lean_object* v_val_4037_, lean_object* v_inst_4038_, lean_object* v_R_4039_, lean_object* v_a_4040_, lean_object* v_b_4041_, lean_object* v_c_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4035_, v___x_4036_, v_val_4037_, v_inst_4038_, v_R_4039_, v_a_4040_, v_b_4041_, v_c_4042_);
lean_dec_ref(v_val_4037_);
lean_dec_ref(v___x_4036_);
lean_dec(v___x_4035_);
return v_res_4043_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4044_, lean_object* v_inst_4045_, lean_object* v_R_4046_, lean_object* v_a_4047_, uint8_t v_b_4048_, lean_object* v_c_4049_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4044_, v_a_4047_, v_b_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4051_, lean_object* v_inst_4052_, lean_object* v_R_4053_, lean_object* v_a_4054_, lean_object* v_b_4055_, lean_object* v_c_4056_){
_start:
{
uint8_t v_b_boxed_4057_; uint8_t v_res_4058_; lean_object* v_r_4059_; 
v_b_boxed_4057_ = lean_unbox(v_b_4055_);
v_res_4058_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4051_, v_inst_4052_, v_R_4053_, v_a_4054_, v_b_boxed_4057_, v_c_4056_);
lean_dec_ref(v_s_4051_);
v_r_4059_ = lean_box(v_res_4058_);
return v_r_4059_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4064_ = l_Lean_MessageData_ofFormat(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4065_, lean_object* v_maxInlineLength_4066_, lean_object* v_ctx_4067_){
_start:
{
lean_object* v_msg_4069_; lean_object* v___x_4070_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_msg_4069_ = l_Lean_MessageData_ofExpr(v_e_4065_);
lean_inc_ref(v_msg_4069_);
v___x_4070_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4067_, v_msg_4069_);
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_string_utf8_byte_size(v___x_4070_);
lean_inc_ref(v___x_4070_);
v___x_4075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4070_);
lean_ctor_set(v___x_4075_, 1, v___x_4073_);
lean_ctor_set(v___x_4075_, 2, v___x_4074_);
v___x_4076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4074_, v___x_4070_, v___x_4073_, v___x_4073_);
lean_dec_ref(v___x_4070_);
v___x_4077_ = lean_nat_dec_lt(v_maxInlineLength_4066_, v___x_4076_);
lean_dec(v___x_4076_);
if (v___x_4077_ == 0)
{
uint8_t v___x_4078_; 
v___x_4078_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4075_);
lean_dec_ref_known(v___x_4075_, 3);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4079_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v_msg_4069_);
v___x_4081_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
return v___x_4082_;
}
else
{
goto v___jp_4071_;
}
}
else
{
lean_dec_ref_known(v___x_4075_, 3);
goto v___jp_4071_;
}
v___jp_4071_:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_indentD(v_msg_4069_);
return v___x_4072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4083_, lean_object* v_maxInlineLength_4084_, lean_object* v_ctx_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_inlineExprTrailing___lam__0(v_e_4083_, v_maxInlineLength_4084_, v_ctx_4085_);
lean_dec_ref(v_ctx_4085_);
lean_dec(v_maxInlineLength_4084_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4088_, lean_object* v_x_4089_){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4091_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4092_ = l_Lean_MessageData_ofExpr(v_e_4088_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_inlineExprTrailing___lam__2(v_e_4096_, v_x_4097_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4100_, lean_object* v_maxInlineLength_4101_){
_start:
{
lean_object* v___f_4102_; lean_object* v___f_4103_; lean_object* v___f_4104_; lean_object* v___x_4105_; 
lean_inc_ref_n(v_e_4100_, 2);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4102_, 0, v_e_4100_);
lean_closure_set(v___f_4102_, 1, v_maxInlineLength_4101_);
v___f_4103_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4103_, 0, v_e_4100_);
v___f_4104_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4104_, 0, v_e_4100_);
v___x_4105_ = l_Lean_MessageData_lazy(v___f_4102_, v___f_4103_, v___f_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4110_ = l_Lean_MessageData_ofFormat(v___x_4109_);
return v___x_4110_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4115_ = l_Lean_MessageData_ofFormat(v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4116_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4117_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v_msg_4116_);
v___x_4119_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4121_, lean_object* v_inst_4122_, lean_object* v_msg_4123_){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_apply_1(v_inst_4121_, v_msg_4123_);
v___x_4125_ = lean_apply_2(v_inst_4122_, lean_box(0), v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4126_, lean_object* v_inst_4127_){
_start:
{
lean_object* v___f_4128_; 
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4128_, 0, v_inst_4127_);
lean_closure_set(v___f_4128_, 1, v_inst_4126_);
return v___f_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4129_, lean_object* v_n_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_){
_start:
{
lean_object* v___f_4133_; 
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4133_, 0, v_inst_4132_);
lean_closure_set(v___f_4133_, 1, v_inst_4131_);
return v___f_4133_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4134_ = lean_unsigned_to_nat(32u);
v___x_4135_ = lean_mk_empty_array_with_capacity(v___x_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4137_ = ((size_t)5ULL);
v___x_4138_ = lean_unsigned_to_nat(0u);
v___x_4139_ = lean_unsigned_to_nat(32u);
v___x_4140_ = lean_mk_empty_array_with_capacity(v___x_4139_);
v___x_4141_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4142_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
lean_ctor_set(v___x_4142_, 1, v___x_4140_);
lean_ctor_set(v___x_4142_, 2, v___x_4138_);
lean_ctor_set(v___x_4142_, 3, v___x_4138_);
lean_ctor_set_usize(v___x_4142_, 4, v___x_4137_);
return v___x_4142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4143_ = lean_box(1);
v___x_4144_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4145_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v___x_4144_);
lean_ctor_set(v___x_4146_, 2, v___x_4143_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4147_, lean_object* v_msgData_4148_, lean_object* v_toPure_4149_, lean_object* v_opts_4150_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4151_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4152_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4153_, 0, v_env_4147_);
lean_ctor_set(v___x_4153_, 1, v___x_4151_);
lean_ctor_set(v___x_4153_, 2, v___x_4152_);
lean_ctor_set(v___x_4153_, 3, v_opts_4150_);
v___x_4154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
lean_ctor_set(v___x_4154_, 1, v_msgData_4148_);
v___x_4155_ = lean_apply_2(v_toPure_4149_, lean_box(0), v___x_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_inst_4156_, lean_object* v_msgData_4157_, lean_object* v_toPure_4158_, lean_object* v_toBind_4159_, lean_object* v_____do__lift_4160_){
_start:
{
lean_object* v_getOptionsUnrestricted_4161_; uint8_t v___x_4162_; lean_object* v_env_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; 
v_getOptionsUnrestricted_4161_ = lean_ctor_get(v_inst_4156_, 1);
lean_inc(v_getOptionsUnrestricted_4161_);
lean_dec_ref(v_inst_4156_);
v___x_4162_ = 0;
v_env_4163_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4160_, v___x_4162_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4164_, 0, v_env_4163_);
lean_closure_set(v___f_4164_, 1, v_msgData_4157_);
lean_closure_set(v___f_4164_, 2, v_toPure_4158_);
v___x_4165_ = lean_apply_4(v_toBind_4159_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4161_, v___f_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4166_, lean_object* v_inst_4167_, lean_object* v_inst_4168_, lean_object* v_msgData_4169_){
_start:
{
lean_object* v_toApplicative_4170_; lean_object* v_toBind_4171_; lean_object* v_getEnv_4172_; lean_object* v_toPure_4173_; lean_object* v___f_4174_; lean_object* v___x_4175_; 
v_toApplicative_4170_ = lean_ctor_get(v_inst_4166_, 0);
lean_inc_ref(v_toApplicative_4170_);
v_toBind_4171_ = lean_ctor_get(v_inst_4166_, 1);
lean_inc_n(v_toBind_4171_, 2);
lean_dec_ref(v_inst_4166_);
v_getEnv_4172_ = lean_ctor_get(v_inst_4167_, 0);
lean_inc(v_getEnv_4172_);
lean_dec_ref(v_inst_4167_);
v_toPure_4173_ = lean_ctor_get(v_toApplicative_4170_, 1);
lean_inc(v_toPure_4173_);
lean_dec_ref(v_toApplicative_4170_);
v___f_4174_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4174_, 0, v_inst_4168_);
lean_closure_set(v___f_4174_, 1, v_msgData_4169_);
lean_closure_set(v___f_4174_, 2, v_toPure_4173_);
lean_closure_set(v___f_4174_, 3, v_toBind_4171_);
v___x_4175_ = lean_apply_4(v_toBind_4171_, lean_box(0), lean_box(0), v_getEnv_4172_, v___f_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4176_, lean_object* v_inst_4177_, lean_object* v_inst_4178_, lean_object* v_inst_4179_, lean_object* v_msgData_4180_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_addMessageContextPartial___redArg(v_inst_4177_, v_inst_4178_, v_inst_4179_, v_msgData_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4182_, lean_object* v_mctx_4183_, lean_object* v_lctx_4184_, lean_object* v_msgData_4185_, lean_object* v_toPure_4186_, lean_object* v_opts_4187_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4188_, 0, v_env_4182_);
lean_ctor_set(v___x_4188_, 1, v_mctx_4183_);
lean_ctor_set(v___x_4188_, 2, v_lctx_4184_);
lean_ctor_set(v___x_4188_, 3, v_opts_4187_);
v___x_4189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
lean_ctor_set(v___x_4189_, 1, v_msgData_4185_);
v___x_4190_ = lean_apply_2(v_toPure_4186_, lean_box(0), v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_inst_4191_, lean_object* v_env_4192_, lean_object* v_mctx_4193_, lean_object* v_msgData_4194_, lean_object* v_toPure_4195_, lean_object* v_toBind_4196_, lean_object* v_lctx_4197_){
_start:
{
lean_object* v_getOptionsUnrestricted_4198_; lean_object* v___f_4199_; lean_object* v___x_4200_; 
v_getOptionsUnrestricted_4198_ = lean_ctor_get(v_inst_4191_, 1);
lean_inc(v_getOptionsUnrestricted_4198_);
lean_dec_ref(v_inst_4191_);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4199_, 0, v_env_4192_);
lean_closure_set(v___f_4199_, 1, v_mctx_4193_);
lean_closure_set(v___f_4199_, 2, v_lctx_4197_);
lean_closure_set(v___f_4199_, 3, v_msgData_4194_);
lean_closure_set(v___f_4199_, 4, v_toPure_4195_);
v___x_4200_ = lean_apply_4(v_toBind_4196_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4198_, v___f_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_inst_4201_, lean_object* v_env_4202_, lean_object* v_msgData_4203_, lean_object* v_toPure_4204_, lean_object* v_toBind_4205_, lean_object* v_inst_4206_, lean_object* v_mctx_4207_){
_start:
{
lean_object* v___f_4208_; lean_object* v___x_4209_; 
lean_inc(v_toBind_4205_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4208_, 0, v_inst_4201_);
lean_closure_set(v___f_4208_, 1, v_env_4202_);
lean_closure_set(v___f_4208_, 2, v_mctx_4207_);
lean_closure_set(v___f_4208_, 3, v_msgData_4203_);
lean_closure_set(v___f_4208_, 4, v_toPure_4204_);
lean_closure_set(v___f_4208_, 5, v_toBind_4205_);
v___x_4209_ = lean_apply_4(v_toBind_4205_, lean_box(0), lean_box(0), v_inst_4206_, v___f_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4210_, lean_object* v_inst_4211_, lean_object* v_msgData_4212_, lean_object* v_toPure_4213_, lean_object* v_toBind_4214_, lean_object* v_inst_4215_, lean_object* v_____do__lift_4216_){
_start:
{
lean_object* v_getMCtx_4217_; uint8_t v___x_4218_; lean_object* v_env_4219_; lean_object* v___f_4220_; lean_object* v___x_4221_; 
v_getMCtx_4217_ = lean_ctor_get(v_inst_4210_, 0);
lean_inc(v_getMCtx_4217_);
lean_dec_ref(v_inst_4210_);
v___x_4218_ = 0;
v_env_4219_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4216_, v___x_4218_);
lean_inc(v_toBind_4214_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4220_, 0, v_inst_4211_);
lean_closure_set(v___f_4220_, 1, v_env_4219_);
lean_closure_set(v___f_4220_, 2, v_msgData_4212_);
lean_closure_set(v___f_4220_, 3, v_toPure_4213_);
lean_closure_set(v___f_4220_, 4, v_toBind_4214_);
lean_closure_set(v___f_4220_, 5, v_inst_4215_);
v___x_4221_ = lean_apply_4(v_toBind_4214_, lean_box(0), lean_box(0), v_getMCtx_4217_, v___f_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4222_, lean_object* v_inst_4223_, lean_object* v_inst_4224_, lean_object* v_inst_4225_, lean_object* v_inst_4226_, lean_object* v_msgData_4227_){
_start:
{
lean_object* v_toApplicative_4228_; lean_object* v_toBind_4229_; lean_object* v_getEnv_4230_; lean_object* v_toPure_4231_; lean_object* v___f_4232_; lean_object* v___x_4233_; 
v_toApplicative_4228_ = lean_ctor_get(v_inst_4222_, 0);
lean_inc_ref(v_toApplicative_4228_);
v_toBind_4229_ = lean_ctor_get(v_inst_4222_, 1);
lean_inc_n(v_toBind_4229_, 2);
lean_dec_ref(v_inst_4222_);
v_getEnv_4230_ = lean_ctor_get(v_inst_4223_, 0);
lean_inc(v_getEnv_4230_);
lean_dec_ref(v_inst_4223_);
v_toPure_4231_ = lean_ctor_get(v_toApplicative_4228_, 1);
lean_inc(v_toPure_4231_);
lean_dec_ref(v_toApplicative_4228_);
v___f_4232_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4232_, 0, v_inst_4224_);
lean_closure_set(v___f_4232_, 1, v_inst_4226_);
lean_closure_set(v___f_4232_, 2, v_msgData_4227_);
lean_closure_set(v___f_4232_, 3, v_toPure_4231_);
lean_closure_set(v___f_4232_, 4, v_toBind_4229_);
lean_closure_set(v___f_4232_, 5, v_inst_4225_);
v___x_4233_ = lean_apply_4(v_toBind_4229_, lean_box(0), lean_box(0), v_getEnv_4230_, v___f_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4234_, lean_object* v_inst_4235_, lean_object* v_inst_4236_, lean_object* v_inst_4237_, lean_object* v_inst_4238_, lean_object* v_inst_4239_, lean_object* v_msgData_4240_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_addMessageContextFull___redArg(v_inst_4235_, v_inst_4236_, v_inst_4237_, v_inst_4238_, v_inst_4239_, v_msgData_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg(){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0));
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object* v___dummy_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v_res_4247_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4251_);
lean_dec_ref(v_s_4251_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4253_, lean_object* v___x_4254_, lean_object* v___x_4255_, lean_object* v_a_4256_, lean_object* v_b_4257_){
_start:
{
lean_object* v_it_4259_; lean_object* v_startInclusive_4260_; lean_object* v_endExclusive_4261_; 
if (lean_obj_tag(v_a_4256_) == 0)
{
lean_object* v_currPos_4267_; lean_object* v_searcher_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4291_; 
v_currPos_4267_ = lean_ctor_get(v_a_4256_, 0);
v_searcher_4268_ = lean_ctor_get(v_a_4256_, 1);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_a_4256_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4270_ = v_a_4256_;
v_isShared_4271_ = v_isSharedCheck_4291_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_searcher_4268_);
lean_inc(v_currPos_4267_);
lean_dec(v_a_4256_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4291_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
uint8_t v_decide_4272_; 
v_decide_4272_ = lean_nat_dec_eq(v_searcher_4268_, v___x_4255_);
if (v_decide_4272_ == 0)
{
uint32_t v___x_4273_; uint32_t v___x_4274_; uint8_t v___x_4275_; 
v___x_4273_ = 10;
v___x_4274_ = lean_string_utf8_get_fast(v_str_4253_, v_searcher_4268_);
v___x_4275_ = lean_uint32_dec_eq(v___x_4274_, v___x_4273_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = lean_string_utf8_next_fast(v_str_4253_, v_searcher_4268_);
lean_dec(v_searcher_4268_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 1, v___x_4276_);
v___x_4278_ = v___x_4270_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_currPos_4267_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
v_a_4256_ = v___x_4278_;
goto _start;
}
}
else
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v_slice_4284_; lean_object* v_nextIt_4286_; 
v___x_4281_ = lean_string_utf8_next_fast(v_str_4253_, v_searcher_4268_);
v___x_4282_ = lean_nat_sub(v___x_4281_, v_searcher_4268_);
v___x_4283_ = lean_nat_add(v_searcher_4268_, v___x_4282_);
lean_dec(v___x_4282_);
v_slice_4284_ = l_String_Slice_subslice_x21(v___x_4254_, v_currPos_4267_, v_searcher_4268_);
lean_inc(v___x_4283_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 1, v___x_4283_);
lean_ctor_set(v___x_4270_, 0, v___x_4283_);
v_nextIt_4286_ = v___x_4270_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4283_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v___x_4283_);
v_nextIt_4286_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v_startInclusive_4287_; lean_object* v_endExclusive_4288_; 
v_startInclusive_4287_ = lean_ctor_get(v_slice_4284_, 0);
lean_inc(v_startInclusive_4287_);
v_endExclusive_4288_ = lean_ctor_get(v_slice_4284_, 1);
lean_inc(v_endExclusive_4288_);
lean_dec_ref(v_slice_4284_);
v_it_4259_ = v_nextIt_4286_;
v_startInclusive_4260_ = v_startInclusive_4287_;
v_endExclusive_4261_ = v_endExclusive_4288_;
goto v___jp_4258_;
}
}
}
else
{
lean_object* v___x_4290_; 
lean_del_object(v___x_4270_);
lean_dec(v_searcher_4268_);
v___x_4290_ = lean_box(1);
lean_inc(v___x_4255_);
v_it_4259_ = v___x_4290_;
v_startInclusive_4260_ = v_currPos_4267_;
v_endExclusive_4261_ = v___x_4255_;
goto v___jp_4258_;
}
}
}
else
{
lean_dec(v___x_4255_);
return v_b_4257_;
}
v___jp_4258_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4262_ = lean_string_utf8_extract_fast(v_str_4253_, v_startInclusive_4260_, v_endExclusive_4261_);
lean_dec(v_endExclusive_4261_);
lean_dec(v_startInclusive_4260_);
v___x_4263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
v___x_4264_ = l_Lean_MessageData_ofFormat(v___x_4263_);
v___x_4265_ = lean_array_push(v_b_4257_, v___x_4264_);
v_a_4256_ = v_it_4259_;
v_b_4257_ = v___x_4265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v_a_4295_, lean_object* v_b_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4292_, v___x_4293_, v___x_4294_, v_a_4295_, v_b_4296_);
lean_dec_ref(v___x_4293_);
lean_dec_ref(v_str_4292_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4300_){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_lines_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4301_ = lean_unsigned_to_nat(0u);
v___x_4302_ = lean_string_utf8_byte_size(v_str_4300_);
lean_inc_ref(v_str_4300_);
v___x_4303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4303_, 0, v_str_4300_);
lean_ctor_set(v___x_4303_, 1, v___x_4301_);
lean_ctor_set(v___x_4303_, 2, v___x_4302_);
v_lines_4304_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
v___x_4305_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4306_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4300_, v___x_4303_, v___x_4302_, v_lines_4304_, v___x_4305_);
lean_dec_ref_known(v___x_4303_, 3);
lean_dec_ref(v_str_4300_);
v___x_4307_ = lean_array_to_list(v___x_4306_);
v___x_4308_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4309_ = l_Lean_MessageData_joinSep(v___x_4307_, v___x_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4310_, lean_object* v___x_4311_, lean_object* v___x_4312_, lean_object* v_inst_4313_, lean_object* v_R_4314_, lean_object* v_a_4315_, lean_object* v_b_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4310_, v___x_4311_, v___x_4312_, v_a_4315_, v_b_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4318_, lean_object* v___x_4319_, lean_object* v___x_4320_, lean_object* v_inst_4321_, lean_object* v_R_4322_, lean_object* v_a_4323_, lean_object* v_b_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4318_, v___x_4319_, v___x_4320_, v_inst_4321_, v_R_4322_, v_a_4323_, v_b_4324_);
lean_dec_ref(v___x_4319_);
lean_dec_ref(v_str_4318_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4326_){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4328_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4328_, 0, lean_box(0));
lean_closure_set(v___x_4328_, 1, lean_box(0));
lean_closure_set(v___x_4328_, 2, lean_box(0));
lean_closure_set(v___x_4328_, 3, v___x_4327_);
lean_closure_set(v___x_4328_, 4, v_inst_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4329_, lean_object* v_inst_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg(){
_start:
{
lean_object* v___f_4339_; 
v___f_4339_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object* v___dummy_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_instToMessageDataTSyntax___redArg();
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4342_){
_start:
{
lean_object* v___f_4343_; 
v___f_4343_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_instToMessageDataTSyntax(v_k_4344_);
lean_dec(v_k_4344_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4350_, lean_object* v_as_4351_){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_box(0);
v___x_4353_ = l_List_mapTR_loop___redArg(v_inst_4350_, v_as_4351_, v___x_4352_);
v___x_4354_ = l_Lean_MessageData_ofList(v___x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4355_){
_start:
{
lean_object* v___f_4356_; 
v___f_4356_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4356_, 0, v_inst_4355_);
return v___f_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4357_, lean_object* v_inst_4358_){
_start:
{
lean_object* v___f_4359_; 
v___f_4359_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4359_, 0, v_inst_4358_);
return v___f_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4360_, lean_object* v_as_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = lean_array_to_list(v_as_4361_);
v___x_4363_ = lean_box(0);
v___x_4364_ = l_List_mapTR_loop___redArg(v_inst_4360_, v___x_4362_, v___x_4363_);
v___x_4365_ = l_Lean_MessageData_ofList(v___x_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4366_){
_start:
{
lean_object* v___f_4367_; 
v___f_4367_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4367_, 0, v_inst_4366_);
return v___f_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4368_, lean_object* v_inst_4369_){
_start:
{
lean_object* v___f_4370_; 
v___f_4370_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4370_, 0, v_inst_4369_);
return v___f_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4371_, lean_object* v_acc_4372_, lean_object* v_recur_4373_){
_start:
{
lean_object* v_array_4374_; lean_object* v_start_4375_; lean_object* v_stop_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4389_; 
v_array_4374_ = lean_ctor_get(v_it_4371_, 0);
v_start_4375_ = lean_ctor_get(v_it_4371_, 1);
v_stop_4376_ = lean_ctor_get(v_it_4371_, 2);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_it_4371_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4378_ = v_it_4371_;
v_isShared_4379_ = v_isSharedCheck_4389_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_stop_4376_);
lean_inc(v_start_4375_);
lean_inc(v_array_4374_);
lean_dec(v_it_4371_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4389_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
uint8_t v___x_4380_; 
v___x_4380_ = lean_nat_dec_lt(v_start_4375_, v_stop_4376_);
if (v___x_4380_ == 0)
{
lean_del_object(v___x_4378_);
lean_dec(v_stop_4376_);
lean_dec(v_start_4375_);
lean_dec_ref(v_array_4374_);
lean_dec_ref(v_recur_4373_);
return v_acc_4372_;
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4381_ = lean_unsigned_to_nat(1u);
v___x_4382_ = lean_nat_add(v_start_4375_, v___x_4381_);
lean_inc_ref(v_array_4374_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 1, v___x_4382_);
v___x_4384_ = v___x_4378_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_array_4374_);
lean_ctor_set(v_reuseFailAlloc_4388_, 1, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4388_, 2, v_stop_4376_);
v___x_4384_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = lean_array_fget(v_array_4374_, v_start_4375_);
lean_dec(v_start_4375_);
lean_dec_ref(v_array_4374_);
v___x_4386_ = lean_array_push(v_acc_4372_, v___x_4385_);
v___x_4387_ = lean_apply_3(v_recur_4373_, v___x_4384_, v___x_4386_, lean_box(0));
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4392_, lean_object* v_inst_4393_, lean_object* v_as_4394_){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4395_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4396_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4392_, v_as_4394_, v___x_4395_);
v___x_4397_ = lean_array_to_list(v___x_4396_);
v___x_4398_ = lean_box(0);
v___x_4399_ = l_List_mapTR_loop___redArg(v_inst_4393_, v___x_4397_, v___x_4398_);
v___x_4400_ = l_Lean_MessageData_ofList(v___x_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4402_){
_start:
{
lean_object* v___f_4403_; lean_object* v___f_4404_; 
v___f_4403_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4404_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4404_, 0, v___f_4403_);
lean_closure_set(v___f_4404_, 1, v_inst_4402_);
return v___f_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4405_, lean_object* v_inst_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4406_);
return v___x_4407_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4412_ = l_Lean_MessageData_ofFormat(v___x_4411_);
return v___x_4412_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4416_ = l_Lean_MessageData_ofFormat(v___x_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4417_, lean_object* v_x_4418_){
_start:
{
if (lean_obj_tag(v_x_4418_) == 0)
{
lean_object* v___x_4419_; 
lean_dec_ref(v_inst_4417_);
v___x_4419_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4419_;
}
else
{
lean_object* v_val_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_val_4420_ = lean_ctor_get(v_x_4418_, 0);
lean_inc(v_val_4420_);
lean_dec_ref_known(v_x_4418_, 1);
v___x_4421_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4422_ = lean_apply_1(v_inst_4417_, v_val_4420_);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
return v___x_4425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4426_){
_start:
{
lean_object* v___f_4427_; 
v___f_4427_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4427_, 0, v_inst_4426_);
return v___f_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4428_, lean_object* v_inst_4429_){
_start:
{
lean_object* v___f_4430_; 
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4430_, 0, v_inst_4429_);
return v___f_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4431_, lean_object* v_inst_4432_, lean_object* v_x_4433_){
_start:
{
lean_object* v_fst_4434_; lean_object* v_snd_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4449_; 
v_fst_4434_ = lean_ctor_get(v_x_4433_, 0);
v_snd_4435_ = lean_ctor_get(v_x_4433_, 1);
v_isSharedCheck_4449_ = !lean_is_exclusive(v_x_4433_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4437_ = v_x_4433_;
v_isShared_4438_ = v_isSharedCheck_4449_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_snd_4435_);
lean_inc(v_fst_4434_);
lean_dec(v_x_4433_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4449_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4439_ = lean_apply_1(v_inst_4431_, v_fst_4434_);
v___x_4440_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4438_ == 0)
{
lean_ctor_set_tag(v___x_4437_, 7);
lean_ctor_set(v___x_4437_, 1, v___x_4440_);
lean_ctor_set(v___x_4437_, 0, v___x_4439_);
v___x_4442_ = v___x_4437_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4443_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4442_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
v___x_4445_ = lean_apply_1(v_inst_4432_, v_snd_4435_);
v___x_4446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4444_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = l_Lean_MessageData_paren(v___x_4446_);
return v___x_4447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4450_, lean_object* v_inst_4451_){
_start:
{
lean_object* v___f_4452_; 
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4452_, 0, v_inst_4450_);
lean_closure_set(v___f_4452_, 1, v_inst_4451_);
return v___f_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4453_, lean_object* v_00_u03b2_4454_, lean_object* v_inst_4455_, lean_object* v_inst_4456_){
_start:
{
lean_object* v___f_4457_; 
v___f_4457_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4457_, 0, v_inst_4455_);
lean_closure_set(v___f_4457_, 1, v_inst_4456_);
return v___f_4457_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4462_ = l_Lean_MessageData_ofFormat(v___x_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4463_){
_start:
{
if (lean_obj_tag(v_x_4463_) == 0)
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4464_;
}
else
{
lean_object* v_val_4465_; lean_object* v___x_4466_; 
v_val_4465_ = lean_ctor_get(v_x_4463_, 0);
lean_inc(v_val_4465_);
lean_dec_ref_known(v_x_4463_, 1);
v___x_4466_ = l_Lean_MessageData_ofExpr(v_val_4465_);
return v___x_4466_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4501_ = l_String_toRawSubstring_x27(v___x_4500_);
return v___x_4501_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4517_ = l_String_toRawSubstring_x27(v___x_4516_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4531_);
v___x_4535_ = l_Lean_Syntax_isOfKind(v_x_4531_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec(v_x_4531_);
v___x_4536_ = lean_box(1);
v___x_4537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
lean_ctor_set(v___x_4537_, 1, v_a_4533_);
return v___x_4537_;
}
else
{
lean_object* v_quotContext_4538_; lean_object* v_currMacroScope_4539_; lean_object* v_ref_4540_; lean_object* v___x_4541_; lean_object* v_interpStr_4542_; uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_quotContext_4538_ = lean_ctor_get(v_a_4532_, 1);
v_currMacroScope_4539_ = lean_ctor_get(v_a_4532_, 2);
v_ref_4540_ = lean_ctor_get(v_a_4532_, 5);
v___x_4541_ = lean_unsigned_to_nat(1u);
v_interpStr_4542_ = l_Lean_Syntax_getArg(v_x_4531_, v___x_4541_);
lean_dec(v_x_4531_);
v___x_4543_ = 0;
v___x_4544_ = l_Lean_SourceInfo_fromRef(v_ref_4540_, v___x_4543_);
v___x_4545_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4546_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4539_, 2);
lean_inc_n(v_quotContext_4538_, 2);
v___x_4547_ = l_Lean_addMacroScope(v_quotContext_4538_, v___x_4546_, v_currMacroScope_4539_);
v___x_4548_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4544_);
v___x_4549_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4544_);
lean_ctor_set(v___x_4549_, 1, v___x_4545_);
lean_ctor_set(v___x_4549_, 2, v___x_4547_);
lean_ctor_set(v___x_4549_, 3, v___x_4548_);
v___x_4550_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4551_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4552_ = l_Lean_addMacroScope(v_quotContext_4538_, v___x_4551_, v_currMacroScope_4539_);
v___x_4553_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4544_);
lean_ctor_set(v___x_4554_, 1, v___x_4550_);
lean_ctor_set(v___x_4554_, 2, v___x_4552_);
lean_ctor_set(v___x_4554_, 3, v___x_4553_);
lean_inc_ref(v___x_4554_);
v___x_4555_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4542_, v___x_4549_, v___x_4554_, v___x_4554_, v_a_4532_, v_a_4533_);
lean_dec(v_interpStr_4542_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_a_4557_ = lean_ctor_get(v___x_4555_, 1);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4555_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4556_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
v_a_4565_ = lean_ctor_get(v___x_4555_, 0);
v_a_4566_ = lean_ctor_get(v___x_4555_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4555_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_inc(v_a_4565_);
lean_dec(v___x_4555_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4565_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4574_, v_a_4575_, v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4577_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4580_ = l_Lean_stringToMessageData(v___x_4579_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4581_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = lean_array_to_list(v_msgs_4581_);
v___x_4583_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4584_ = l_Lean_MessageData_joinSep(v___x_4582_, v___x_4583_);
v___x_4585_ = l_Lean_indentD(v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4586_, lean_object* v_lctx_4587_, lean_object* v_opts_4588_, lean_object* v_msg_4589_){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4590_ = l_Lean_Environment_ofKernelEnv(v_env_4586_);
v___x_4591_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
lean_ctor_set(v___x_4592_, 2, v_lctx_4587_);
lean_ctor_set(v___x_4592_, 3, v_opts_4588_);
v___x_4593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
lean_ctor_set(v___x_4593_, 1, v_msg_4589_);
return v___x_4593_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4596_ = l_Lean_stringToMessageData(v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4599_ = l_Lean_stringToMessageData(v___x_4598_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4602_ = l_Lean_stringToMessageData(v___x_4601_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4603_, lean_object* v_n_4604_, lean_object* v_expectedType_4605_){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4606_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4607_ = l_Lean_MessageData_ofName(v_n_4604_);
v___x_4608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4608_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___x_4611_ = l_Lean_indentExpr(v_givenType_4603_);
v___x_4612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4610_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = l_Lean_indentExpr(v_expectedType_4605_);
v___x_4616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4614_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
return v___x_4616_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4619_ = lean_box(1);
v___x_4620_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4621_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
lean_ctor_set(v___x_4622_, 1, v___x_4620_);
lean_ctor_set(v___x_4622_, 2, v___x_4619_);
return v___x_4622_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__2));
v___x_4625_ = l_Lean_stringToMessageData(v___x_4624_);
return v___x_4625_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__4));
v___x_4628_ = l_Lean_stringToMessageData(v___x_4627_);
return v___x_4628_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__6));
v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
return v___x_4631_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__9));
v___x_4636_ = l_Lean_MessageData_ofFormat(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__12(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__11));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__14(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__13));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__16(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__15));
v___x_4645_ = l_Lean_stringToMessageData(v___x_4644_);
return v___x_4645_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__18(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__17));
v___x_4648_ = l_Lean_stringToMessageData(v___x_4647_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__20(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__19));
v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__22(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__21));
v___x_4654_ = l_Lean_stringToMessageData(v___x_4653_);
return v___x_4654_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__24(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__23));
v___x_4657_ = l_Lean_stringToMessageData(v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__26(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__25));
v___x_4660_ = l_Lean_stringToMessageData(v___x_4659_);
return v___x_4660_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__28(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__27));
v___x_4663_ = l_Lean_stringToMessageData(v___x_4662_);
return v___x_4663_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__30(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__29));
v___x_4666_ = l_Lean_stringToMessageData(v___x_4665_);
return v___x_4666_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__32(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__31));
v___x_4669_ = l_Lean_stringToMessageData(v___x_4668_);
return v___x_4669_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__34(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__33));
v___x_4672_ = l_Lean_stringToMessageData(v___x_4671_);
return v___x_4672_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__36(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__35));
v___x_4675_ = l_Lean_stringToMessageData(v___x_4674_);
return v___x_4675_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__38(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__37));
v___x_4678_ = l_Lean_stringToMessageData(v___x_4677_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__41(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__40));
v___x_4683_ = l_Lean_MessageData_ofFormat(v___x_4682_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__44(void){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__43));
v___x_4688_ = l_Lean_MessageData_ofFormat(v___x_4687_);
return v___x_4688_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__47(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__46));
v___x_4693_ = l_Lean_MessageData_ofFormat(v___x_4692_);
return v___x_4693_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__50(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__49));
v___x_4698_ = l_Lean_MessageData_ofFormat(v___x_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4699_, lean_object* v_opts_4700_){
_start:
{
switch(lean_obj_tag(v_e_4699_))
{
case 0:
{
lean_object* v_env_4701_; lean_object* v_name_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4715_; 
v_env_4701_ = lean_ctor_get(v_e_4699_, 0);
v_name_4702_ = lean_ctor_get(v_e_4699_, 1);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_e_4699_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4704_ = v_e_4699_;
v_isShared_4705_ = v_isSharedCheck_4715_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_name_4702_);
lean_inc(v_env_4701_);
lean_dec(v_e_4699_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4715_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
v___x_4706_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4707_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__3, &l_Lean_Kernel_Exception_toMessageData___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__3);
v___x_4708_ = l_Lean_MessageData_ofName(v_name_4702_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 7);
lean_ctor_set(v___x_4704_, 1, v___x_4708_);
lean_ctor_set(v___x_4704_, 0, v___x_4707_);
v___x_4710_ = v___x_4704_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4711_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4701_, v___x_4706_, v_opts_4700_, v___x_4712_);
return v___x_4713_;
}
}
}
case 1:
{
lean_object* v_env_4716_; lean_object* v_name_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4731_; 
v_env_4716_ = lean_ctor_get(v_e_4699_, 0);
v_name_4717_ = lean_ctor_get(v_e_4699_, 1);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_e_4699_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4719_ = v_e_4699_;
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_name_4717_);
lean_inc(v_env_4716_);
lean_dec(v_e_4699_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4726_; 
v___x_4721_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4722_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__7, &l_Lean_Kernel_Exception_toMessageData___closed__7_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__7);
v___x_4723_ = 1;
v___x_4724_ = l_Lean_MessageData_ofConstName(v_name_4717_, v___x_4723_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set_tag(v___x_4719_, 7);
lean_ctor_set(v___x_4719_, 1, v___x_4724_);
lean_ctor_set(v___x_4719_, 0, v___x_4722_);
v___x_4726_ = v___x_4719_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v___x_4724_);
v___x_4726_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4727_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4726_);
lean_ctor_set(v___x_4728_, 1, v___x_4727_);
v___x_4729_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4716_, v___x_4721_, v_opts_4700_, v___x_4728_);
return v___x_4729_;
}
}
}
case 2:
{
lean_object* v_env_4732_; lean_object* v_decl_4733_; lean_object* v_givenType_4734_; lean_object* v___x_4735_; 
v_env_4732_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4732_);
v_decl_4733_ = lean_ctor_get(v_e_4699_, 1);
lean_inc(v_decl_4733_);
v_givenType_4734_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_givenType_4734_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4735_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
switch(lean_obj_tag(v_decl_4733_))
{
case 1:
{
lean_object* v_val_4736_; lean_object* v_toConstantVal_4737_; lean_object* v_name_4738_; lean_object* v_type_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_val_4736_ = lean_ctor_get(v_decl_4733_, 0);
lean_inc_ref(v_val_4736_);
lean_dec_ref_known(v_decl_4733_, 1);
v_toConstantVal_4737_ = lean_ctor_get(v_val_4736_, 0);
lean_inc_ref(v_toConstantVal_4737_);
lean_dec_ref(v_val_4736_);
v_name_4738_ = lean_ctor_get(v_toConstantVal_4737_, 0);
lean_inc(v_name_4738_);
v_type_4739_ = lean_ctor_get(v_toConstantVal_4737_, 2);
lean_inc_ref(v_type_4739_);
lean_dec_ref(v_toConstantVal_4737_);
v___x_4740_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4734_, v_name_4738_, v_type_4739_);
v___x_4741_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4732_, v___x_4735_, v_opts_4700_, v___x_4740_);
return v___x_4741_;
}
case 2:
{
lean_object* v_val_4742_; lean_object* v_toConstantVal_4743_; lean_object* v_name_4744_; lean_object* v_type_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_val_4742_ = lean_ctor_get(v_decl_4733_, 0);
lean_inc_ref(v_val_4742_);
lean_dec_ref_known(v_decl_4733_, 1);
v_toConstantVal_4743_ = lean_ctor_get(v_val_4742_, 0);
lean_inc_ref(v_toConstantVal_4743_);
lean_dec_ref(v_val_4742_);
v_name_4744_ = lean_ctor_get(v_toConstantVal_4743_, 0);
lean_inc(v_name_4744_);
v_type_4745_ = lean_ctor_get(v_toConstantVal_4743_, 2);
lean_inc_ref(v_type_4745_);
lean_dec_ref(v_toConstantVal_4743_);
v___x_4746_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4734_, v_name_4744_, v_type_4745_);
v___x_4747_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4732_, v___x_4735_, v_opts_4700_, v___x_4746_);
return v___x_4747_;
}
default: 
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_dec_ref(v_givenType_4734_);
lean_dec(v_decl_4733_);
v___x_4748_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__10, &l_Lean_Kernel_Exception_toMessageData___closed__10_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__10);
v___x_4749_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4732_, v___x_4735_, v_opts_4700_, v___x_4748_);
return v___x_4749_;
}
}
}
case 3:
{
lean_object* v_env_4750_; lean_object* v_name_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_env_4750_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4750_);
v_name_4751_ = lean_ctor_get(v_e_4699_, 1);
lean_inc(v_name_4751_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4752_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4753_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__12, &l_Lean_Kernel_Exception_toMessageData___closed__12_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__12);
v___x_4754_ = 1;
v___x_4755_ = l_Lean_MessageData_ofConstName(v_name_4751_, v___x_4754_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4753_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4750_, v___x_4752_, v_opts_4700_, v___x_4758_);
return v___x_4759_;
}
case 4:
{
lean_object* v_env_4760_; lean_object* v_name_4761_; lean_object* v_expr_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; uint8_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_env_4760_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4760_);
v_name_4761_ = lean_ctor_get(v_e_4699_, 1);
lean_inc(v_name_4761_);
v_expr_4762_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_expr_4762_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4763_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4764_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__14, &l_Lean_Kernel_Exception_toMessageData___closed__14_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__14);
v___x_4765_ = 1;
v___x_4766_ = l_Lean_MessageData_ofConstName(v_name_4761_, v___x_4765_);
v___x_4767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4764_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__16, &l_Lean_Kernel_Exception_toMessageData___closed__16_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__16);
v___x_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4767_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = l_Lean_indentExpr(v_expr_4762_);
v___x_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4769_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4760_, v___x_4763_, v_opts_4700_, v___x_4771_);
return v___x_4772_;
}
case 5:
{
lean_object* v_env_4773_; lean_object* v_lctx_4774_; lean_object* v_expr_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v_env_4773_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4773_);
v_lctx_4774_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4774_);
v_expr_4775_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_expr_4775_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4776_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__18, &l_Lean_Kernel_Exception_toMessageData___closed__18_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__18);
v___x_4777_ = l_Lean_indentExpr(v_expr_4775_);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4773_, v_lctx_4774_, v_opts_4700_, v___x_4778_);
return v___x_4779_;
}
case 6:
{
lean_object* v_env_4780_; lean_object* v_lctx_4781_; lean_object* v_expr_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v_env_4780_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4780_);
v_lctx_4781_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4781_);
v_expr_4782_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_expr_4782_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4783_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__20, &l_Lean_Kernel_Exception_toMessageData___closed__20_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__20);
v___x_4784_ = l_Lean_indentExpr(v_expr_4782_);
v___x_4785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4783_);
lean_ctor_set(v___x_4785_, 1, v___x_4784_);
v___x_4786_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4780_, v_lctx_4781_, v_opts_4700_, v___x_4785_);
return v___x_4786_;
}
case 7:
{
lean_object* v_env_4787_; lean_object* v_lctx_4788_; lean_object* v_name_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v_env_4787_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4787_);
v_lctx_4788_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4788_);
v_name_4789_ = lean_ctor_get(v_e_4699_, 2);
lean_inc(v_name_4789_);
lean_dec_ref_known(v_e_4699_, 5);
v___x_4790_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__22, &l_Lean_Kernel_Exception_toMessageData___closed__22_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__22);
v___x_4791_ = l_Lean_MessageData_ofName(v_name_4789_);
v___x_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4790_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v___x_4793_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4792_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4787_, v_lctx_4788_, v_opts_4700_, v___x_4794_);
return v___x_4795_;
}
case 8:
{
lean_object* v_env_4796_; lean_object* v_lctx_4797_; lean_object* v_expr_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v_env_4796_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4796_);
v_lctx_4797_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4797_);
v_expr_4798_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_expr_4798_);
lean_dec_ref_known(v_e_4699_, 4);
v___x_4799_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__24, &l_Lean_Kernel_Exception_toMessageData___closed__24_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__24);
v___x_4800_ = l_Lean_indentExpr(v_expr_4798_);
v___x_4801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4799_);
lean_ctor_set(v___x_4801_, 1, v___x_4800_);
v___x_4802_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4796_, v_lctx_4797_, v_opts_4700_, v___x_4801_);
return v___x_4802_;
}
case 9:
{
lean_object* v_env_4803_; lean_object* v_lctx_4804_; lean_object* v_app_4805_; lean_object* v_funType_4806_; lean_object* v_argType_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v_env_4803_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4803_);
v_lctx_4804_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4804_);
v_app_4805_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_app_4805_);
v_funType_4806_ = lean_ctor_get(v_e_4699_, 3);
lean_inc_ref(v_funType_4806_);
v_argType_4807_ = lean_ctor_get(v_e_4699_, 4);
lean_inc_ref(v_argType_4807_);
lean_dec_ref_known(v_e_4699_, 5);
v___x_4808_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__26, &l_Lean_Kernel_Exception_toMessageData___closed__26_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__26);
v___x_4809_ = l_Lean_indentExpr(v_app_4805_);
v___x_4810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4808_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
v___x_4811_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__28, &l_Lean_Kernel_Exception_toMessageData___closed__28_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__28);
v___x_4812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4810_);
lean_ctor_set(v___x_4812_, 1, v___x_4811_);
v___x_4813_ = l_Lean_indentExpr(v_argType_4807_);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__30, &l_Lean_Kernel_Exception_toMessageData___closed__30_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__30);
v___x_4816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4814_);
lean_ctor_set(v___x_4816_, 1, v___x_4815_);
v___x_4817_ = l_Lean_indentExpr(v_funType_4806_);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4803_, v_lctx_4804_, v_opts_4700_, v___x_4818_);
return v___x_4819_;
}
case 10:
{
lean_object* v_env_4820_; lean_object* v_lctx_4821_; lean_object* v_proj_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v_env_4820_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4820_);
v_lctx_4821_ = lean_ctor_get(v_e_4699_, 1);
lean_inc_ref(v_lctx_4821_);
v_proj_4822_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_proj_4822_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4823_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__32, &l_Lean_Kernel_Exception_toMessageData___closed__32_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__32);
v___x_4824_ = l_Lean_indentExpr(v_proj_4822_);
v___x_4825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4823_);
lean_ctor_set(v___x_4825_, 1, v___x_4824_);
v___x_4826_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4820_, v_lctx_4821_, v_opts_4700_, v___x_4825_);
return v___x_4826_;
}
case 11:
{
lean_object* v_env_4827_; lean_object* v_name_4828_; lean_object* v_type_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v_env_4827_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_env_4827_);
v_name_4828_ = lean_ctor_get(v_e_4699_, 1);
lean_inc(v_name_4828_);
v_type_4829_ = lean_ctor_get(v_e_4699_, 2);
lean_inc_ref(v_type_4829_);
lean_dec_ref_known(v_e_4699_, 3);
v___x_4830_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4831_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__34, &l_Lean_Kernel_Exception_toMessageData___closed__34_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__34);
v___x_4832_ = 1;
v___x_4833_ = l_Lean_MessageData_ofConstName(v_name_4828_, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4831_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__36, &l_Lean_Kernel_Exception_toMessageData___closed__36_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__36);
v___x_4836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
v___x_4837_ = l_Lean_indentExpr(v_type_4829_);
v___x_4838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4836_);
lean_ctor_set(v___x_4838_, 1, v___x_4837_);
v___x_4839_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4827_, v___x_4830_, v_opts_4700_, v___x_4838_);
return v___x_4839_;
}
case 12:
{
lean_object* v_msg_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref(v_opts_4700_);
v_msg_4840_ = lean_ctor_get(v_e_4699_, 0);
lean_inc_ref(v_msg_4840_);
lean_dec_ref_known(v_e_4699_, 1);
v___x_4841_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__38, &l_Lean_Kernel_Exception_toMessageData___closed__38_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__38);
v___x_4842_ = l_Lean_stringToMessageData(v_msg_4840_);
v___x_4843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4841_);
lean_ctor_set(v___x_4843_, 1, v___x_4842_);
return v___x_4843_;
}
case 13:
{
lean_object* v___x_4844_; 
lean_dec_ref(v_opts_4700_);
v___x_4844_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__41, &l_Lean_Kernel_Exception_toMessageData___closed__41_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__41);
return v___x_4844_;
}
case 14:
{
lean_object* v___x_4845_; 
lean_dec_ref(v_opts_4700_);
v___x_4845_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__44, &l_Lean_Kernel_Exception_toMessageData___closed__44_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__44);
return v___x_4845_;
}
case 15:
{
lean_object* v___x_4846_; 
lean_dec_ref(v_opts_4700_);
v___x_4846_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__47, &l_Lean_Kernel_Exception_toMessageData___closed__47_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__47);
return v___x_4846_;
}
default: 
{
lean_object* v___x_4847_; 
lean_dec_ref(v_opts_4700_);
v___x_4847_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__50, &l_Lean_Kernel_Exception_toMessageData___closed__50_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__50);
return v___x_4847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4848_, lean_object* v_e_4849_, lean_object* v_cls_4850_){
_start:
{
lean_object* v___x_4851_; double v___x_4852_; uint8_t v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4851_ = lean_box(0);
v___x_4852_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4853_ = 1;
v___x_4854_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4855_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4855_, 0, v_cls_4850_);
lean_ctor_set(v___x_4855_, 1, v___x_4851_);
lean_ctor_set(v___x_4855_, 2, v___x_4854_);
lean_ctor_set_float(v___x_4855_, sizeof(void*)*3, v___x_4852_);
lean_ctor_set_float(v___x_4855_, sizeof(void*)*3 + 8, v___x_4852_);
lean_ctor_set_uint8(v___x_4855_, sizeof(void*)*3 + 16, v___x_4853_);
v___x_4856_ = lean_apply_1(v_inst_4848_, v_e_4849_);
v___x_4857_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4858_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4855_);
lean_ctor_set(v___x_4858_, 1, v___x_4856_);
lean_ctor_set(v___x_4858_, 2, v___x_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4859_, lean_object* v_inst_4860_, lean_object* v_e_4861_, lean_object* v_cls_4862_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l_Lean_toTraceElem___redArg(v_inst_4860_, v_e_4861_, v_cls_4862_);
return v___x_4863_;
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
